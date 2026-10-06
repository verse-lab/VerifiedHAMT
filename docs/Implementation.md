# Implementation notes

This document explains how the verified operations compile to efficient code,
and what evidence supports that. [Verification.md](Verification.md) states the
theorems, and [Benchmarks/README.md](../Benchmarks/README.md) explains how to
measure performance.

## Runtime representation

`Map` extends `SizedRaw`, a structure holding the native map and its size, and
its proof fields are erased. `Set` delegates every operation to its underlying
`Map α Unit`. The native nodes keep their representation. Upstream's opaque set
insertion and query serve only as test oracles.

`VerifiedHAMTTests/MapIR.lean` and `VerifiedHAMTTests/SetIR.lean` check this as part
of `lake test`. On Lean v4.32.0, the bundled `Nat` insertion and lookup compile to
the same IR signatures and bodies, including ownership annotations, as direct
calls of the verified operations on `SizedRaw`, ignoring only declaration names.
These entry points therefore do no proof computation and no work beyond
maintaining the size. The check is a compiler regression test for these entry
points, not a timing guarantee or an equivalence with upstream. To run one check
alone:

```sh
lake env lean VerifiedHAMTTests/MapIR.lean
```

## Insertion traversal

`insert` computes the key's hash once, at the root, and `insertNode` passes the
remaining hash and the consumed-bit offset down as machine words. Hashes are
recomputed only while rebuilding promoted buckets, and `@[specialize]` removes
the indirect calls from the rebuild loop. The theorems are proved about this
code directly; see [Verification.md](Verification.md#executable-code).

`insertEntries` reads the selected entry, writes `.null` into its slot, and only
then writes the new entry. Clearing the slot first releases the array's reference
to the child, so an unshared child stays unshared during the recursive call and
can be updated in place; core's `Array.modify` achieves the same by storing
`box(0)`, since it has no value of an arbitrary element type to store. Logically
the clearing write cancels out (`insertEntries_eq`). The compiler may move a pure
write after the call, though. In the current shape, where every arm writes into
the cleared array, it keeps the write first, and `VerifiedHAMTTests/ReleaseIR.lean`
checks this in the compiled traversals. The child callback also receives a proof
that the child came from the array, which `insertNoExpand` needs for termination.
`insertCollisionAux` scans and updates a collision node directly, so its
constructor can be reused.

An earlier refactoring instead used `Array.modifyWithCallBackProof`, an
`Array.modify` whose callback also received the membership proof. Through
`implemented_by`, it ran an unsafe function that stores `box(0)` like core's.
It was removed for three reasons:

- Its callback could return only the new entry. The sized traversal must also
  return the count, so it made its recursive call before calling the modifier,
  while the slot still held the child, and every node below the root was copied.
- Letting the callback return the count as well did not help. In an experiment,
  once the callback was inlined, the compiler moved the `box(0)` store after the
  recursive call.
- `Entry` has `.null`, so safe code can clear the slot. The unsafe function added
  to the trusted base without guaranteeing the order, which has to be checked in
  the compiled code either way.

## Size maintenance

The native map does not store its size, so `Map` caches it. The specification
`insertSized` is `insert` together with the size update, which adds one exactly
when the key was absent. Its `@[csimp]` theorem makes compiled code use
`insertSizedImpl`, a single traversal that:

- carries the whole map's count in a `SizedRaw`, returns it together with the
  updated node, and changes it at the insertion site;
- at a collision node, compares the array lengths before and after the existing
  insertion scan, before any promotion rebuild, which then uses plain
  `insertNode`.

This avoids a second lookup, a `Bool × Node` result at every level, and any
conversion at the public entry point, since `Map.insert` passes its own
`SizedRaw`. `insertSizedEntries` clears the slot before the recursive call in the
same way as `insertEntries`, so the path is still updated in place. The
equivalence proof needs no routing, uniqueness, or lawful-equality assumption. On malformed short arrays the count follows the membership-based
specification, which is the true key count whenever the bundled invariants hold.
`containsThenInsert` reuses the traversal with an initial count of zero and builds
its Boolean only at the end. Using `@[csimp]` keeps the logical specification
simple and preserves the bundled API's definitional equalities.

### Inspiration from `Std.TreeMap`

In Lean v4.32.0, `Std.TreeMap` wraps `Std.DTreeMap`. Its internal
[`Impl.insert` and `Impl.containsThenInsert`](https://github.com/leanprover/lean4/blob/8c9756b28d64dab099da31a4c09229a9e6a2ef35/src/Std/Data/DTreeMap/Internal/Operations.lean#L327-L365)
return updated trees with cached sizes and erased proofs. `containsThenInsert`
saves the old size, inserts, and compares the two sizes, building the Boolean at
the outer boundary instead of passing a `Bool × Tree` result through every level.
HAMT nodes have no cached subtree sizes, so this project carries the whole map's
count instead. TreeMap uses ordinary insertion and a size comparison there, not a
`@[csimp]` replacement; the rewrite here is a separate choice. `insertIfNew` would
leave an existing value unchanged, so it cannot replace the overwriting
`Map.insert`.

## Size-insertion tuning

The design was reached in three steps:

1. Fusing `contains` and `insert` into a traversal returning `Bool × Node` removed
   the second lookup but made insertion slower. Generated C showed a pair
   allocation at each level and lost `Node.entries` constructor reuse; their
   individual costs were not measured separately.
2. Following the TreeMap idea, a prototype carried the tree and the total count
   together and reconstructed parents directly in each branch. A short pilot
   measured 1.169× native, but the public map still converted to and from a
   separate traversal container.
3. Making `Map` extend `SizedRaw` removed those conversions. The next pilot
   measured 1.068× native, and the full evaluation 1.074×.

The pilots used one process, five paired samples per case, and 10 ms target
batches, so their figures are exploratory. The full evaluation ran the 18 set
insertion workloads, which exercise `Map α Unit`, on Lean v4.32.0 and macOS ARM64.
Each version ran in three sequential processes, with nine paired samples per
workload per process and 20 ms target batches, after all builds had finished. The
table gives the equal-weight geometric mean over workloads of the median paired
verified/native time ratio; lower is better.

| Implementation | Time / native |
| --- | ---: |
| Historical implementation without a cached size | 1.022× |
| Cached size using `contains` then `insert` | 1.478× |
| Fused traversal returning `Bool × Node` | 1.595× |
| Reusable `SizedRaw`, shared with `Map` | 1.074× |

The final native-normalized time is 32.7% lower than the pair-returning version's
and 27.3% lower than the two-pass version's, and all 18 workloads improved against
both. A 5.1% aggregate overhead remains relative to the version without a size.
These ratios describe these workloads on this machine, and normalizing by native
timings does not remove all measurement noise. The raw reports, source snapshots,
and generated-code evidence are kept locally in untracked comparison directories
under `Benchmarks/results/`.

The `Array.modifyWithCallBackProof` refactoring moved the sized traversal's slot
clearing after the recursive call, and a pilot then measured set insertion at
2.34× native. With the clearing restored before the call, a full evaluation with
the settings above measured 1.071×.
