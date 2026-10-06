#!/usr/bin/env python3
"""Save actual imported Lean IR and selected generated C / optimized assembly.

Run separately from timing. Assembly extraction targets the local Apple ARM64
toolchain; the IR and C output are also useful on other platforms.
"""

import argparse
import hashlib
import json
import platform
import re
import shlex
import subprocess
from pathlib import Path


def c_functions(source):
    # Generated Lean C function bodies have balanced braces and no brace-bearing
    # strings in the selected lookup / measurement functions.
    for match in re.finditer(r"^LEAN_EXPORT [^;\n]+\{\n", source, re.M):
        name = re.search(r"(lp_\w+)\(", match.group())
        if name is None:
            continue
        depth = 1
        for end in range(match.end(), len(source)):
            depth += (source[end] == "{") - (source[end] == "}")
            if depth == 0:
                yield name[1], source[match.start():end + 1]
                break


def ir_body(ir, name):
    match = re.search(r"^def " + re.escape(name) + r" .*?(?=^def |\Z)", ir, re.M | re.S)
    if match is None:
        raise RuntimeError(f"Missing IR: {name}")
    return match[0].strip()


def redact_paths(text, root):
    """Remove local repository and home paths from saved compiler evidence."""
    return text.replace(str(root), "<repo>").replace(str(Path.home()), "<home>")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("Benchmarks/results"))
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    output = root / args.output
    output.mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "build", "containsBench"], cwd=root, check=True)
    lean_version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    ir = subprocess.check_output(["lake", "env", "lean", "Benchmarks/InspectIR.lean"], cwd=root, text=True)
    (output / "contains.ir.txt").write_text(ir)

    native_scan = "Lean.PersistentHashMap.containsAtAux._redArg"
    total_scan = "VerifiedHAMT.containsAt._redArg"
    scan_equal = ir_body(ir, native_scan).replace(native_scan, "SCAN") == ir_body(ir, total_scan).replace(total_scan, "SCAN")
    if not scan_equal:
        raise RuntimeError("Collision scan IR changed; review before claiming identical IR")

    c_path = root / ".lake/build/ir/Benchmarks/Contains.c"
    c_source = c_path.read_text()
    selected = []
    timers = []
    for name, body in c_functions(c_source):
        lookup = ("containsNode___at" in name or "containsAux___at" in name) and "___boxed" not in name
        # Skip forwarding wrappers; retain actual traversal and collision loops.
        lookup = lookup and ("lean_obj_tag" in body or "lean_nat_dec_lt" in body)
        timed = body.count("lean_io_mono_nanos_now()") == 2
        if timed:
            batch = "nativeBatch" if "measureNative" in name else "totalBatch"
            start = body.index("lean_io_mono_nanos_now()")
            stop = body.rindex("lean_io_mono_nanos_now()")
            if not start < body.index(batch + "_", start) < body.index("lean_runtime_hold", start) < stop:
                raise RuntimeError(f"Unexpected C timer ordering: {name}")
            timers.append(name)
        if lookup or timed:
            selected.append((name, body))
    if len(timers) != 8:
        raise RuntimeError(f"Expected generic, empty-Nat, Nat, and Name timer pairs; found {len(timers)} functions")
    (output / "contains.c.txt").write_text("// Extracted from .lake/build/ir/Benchmarks/Contains.c\n\n" + "\n\n".join(body for _, body in selected) + "\n")

    trace = json.loads((root / ".lake/build/ir/Benchmarks/Contains.c.o.export.trace").read_text())
    command = next(item["message"][3:] for item in trace["log"] if item["message"].startswith(".> "))
    compile_args = shlex.split(command)
    assembly_dir = root / ".lake/inspection"
    assembly_dir.mkdir(parents=True, exist_ok=True)
    assembly_path = assembly_dir / "Contains.s"
    compile_args[compile_args.index("-c")] = "-S"
    compile_args[compile_args.index("-o") + 1] = str(assembly_path)
    subprocess.run(compile_args, cwd=root, check=True)
    assembly = assembly_path.read_text()
    asm_selected = []
    asm_timers = []
    nat_scans = []
    nat_scan_equal = None
    # Python may be running under Rosetta while Lean generates native ARM64.
    if platform.system() == "Darwin" and "arm64-apple" in lean_version:
        for name, _ in selected:
            match = re.search(r"^_" + re.escape(name) + ":", assembly, re.M)
            if match is None:
                raise RuntimeError(f"Missing assembly symbol: {name}")
            end = assembly.index(".cfi_endproc", match.end()) + len(".cfi_endproc")
            body = assembly[match.start():end]
            if name in timers:
                calls = re.findall(r"^\s+bl\s+(\S+)", body, re.M)
                clock_indices = [i for i, call in enumerate(calls) if call == "_lean_io_mono_nanos_now"]
                batch_indices = [i for i, call in enumerate(calls) if "nativeBatch" in call or "totalBatch" in call]
                if len(clock_indices) != 2 or len(batch_indices) != 1 or not clock_indices[0] < batch_indices[0] < clock_indices[1]:
                    raise RuntimeError(f"Unexpected assembly timer ordering: {name}")
                asm_timers.append(name)
            asm_selected.append(body)
            if "runNat_spec" in name and ("containsAtAux___at" in name or "containsAt___at" in name):
                normalized = "\n".join(line.split(";", 1)[0].strip() for line in body.splitlines()[1:])
                nat_scans.append(re.sub(r"LBB\d+_", "LBB_", normalized))
        nat_scan_equal = len(nat_scans) == 2 and nat_scans[0] == nat_scans[1]
        if not nat_scan_equal:
            raise RuntimeError("Nat collision scan assembly changed; review before claiming identical instructions")
        (output / "contains.arm64.txt").write_text(redact_paths(
            "; Same Lake clang flags, replacing -c with -S. Selected functions.\n\n" +
            "\n\n".join(asm_selected) + "\n", root))

    metadata = {
        "lean": lean_version,
        "source_sha256": {path: hashlib.sha256((root / path).read_bytes()).hexdigest() for path in
                          ("VerifiedHAMT/Basic.lean", "VerifiedHAMT/Contains.lean", "Benchmarks/Contains.lean")},
        "generated_c_sha256": hashlib.sha256(c_path.read_bytes()).hexdigest(),
        "assembly_command": [redact_paths(arg, root) for arg in compile_args],
        "collision_scan_ir_identical_modulo_name": scan_equal,
        "nat_collision_scan_arm64_identical_modulo_labels": nat_scan_equal,
        "c_timer_order_checked": timers,
        "arm64_timer_order_checked": asm_timers,
    }
    (output / "compiler.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"Saved IR, C, compiler metadata, and local assembly to {output}")
    print(f"Collision scan IR matches modulo name; checked {len(timers)} C / {len(asm_timers)} ARM64 timer functions.")


if __name__ == "__main__":
    main()
