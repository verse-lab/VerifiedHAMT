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

`HAMTVerifyTests/MapIR.lean` and `HAMTVerifyTests/SetIR.lean` check this as part
of `lake test`. On Lean v4.32.0, the bundled `Nat` insertion and lookup compile to
the same IR signatures and bodies, including ownership annotations, as direct
calls of the verified operations on `SizedRaw`, ignoring only declaration names.
These entry points therefore do no proof computation and no work beyond
maintaining the size. The check is a compiler regression test for these entry
points, not a timing guarantee or an equivalence with upstream. To run one check
alone:

```sh
lake env lean HAMTVerifyTests/MapIR.lean
```

## Cached-hash insertion

The proof model `insertNode` takes a hash function and shifts it at every
descent. The executable `insert` runs `insertNodeCached` instead. It passes the
remaining hash and the consumed-bit offset down as machine words and recomputes
hashes only while rebuilding promoted buckets; `@[specialize]` removes the
indirect calls from the rebuild loop. Entries updates use `Array.modify`, like
upstream, so the old child reference is released before the child is updated.
`insertCollision` scans and updates a collision node directly, so its constructor
can be reused and no intermediate `Bucket` is allocated. `insert_root_eq` proves
the result equal to the model's; see
[Verification.md](Verification.md#executable-code-and-proof-models).

## Size maintenance

The native map does not store its size, so `Map` caches it. The specification
`insertSized` is `insert` together with the size update, which adds one exactly
when the key was absent. Its `@[csimp]` theorem makes compiled code use
`insertSizedImpl`, a single traversal that:

- carries the whole map's count in one `SizedRaw`, reused on descent and return,
  and changes the count at the insertion site;
- reconstructs each parent directly in its branch, so the `Node.entries`
  constructor can be reused too;
- at a collision node, compares the array lengths before and after the existing
  insertion scan, before any promotion rebuild.

This avoids a second lookup, a `Bool × Node` result at every level, and any
conversion at the public entry point, since `Map.insert` passes its own
`SizedRaw`. The equivalence proof needs no routing, uniqueness, or lawful-equality
assumption. On malformed short arrays the count follows the membership-based
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

## Size-insertion tuning, 2026-10-02

The current design was reached in three steps:

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
and generated-code evidence are kept locally in the untracked
`Benchmarks/results/fused-insert-20261002/` and
`Benchmarks/results/sized-carrier-20261002/` directories.
