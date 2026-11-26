# Lean verification

**Full formalization in progress.** The computer-assisted proof establishes both bounds. Lean now proves the all-length upper bound starting from legal moves. [Full mathematical proof](proof.md)

| Lean declaration | Verified statement |
| --- | --- |
| `Staircase.adj_iff_grid` | The encoded edges are precisely unit moves of the original square grid on the strip. The coordinate map is injective and covers the strip. |
| `Staircase.optimal_upper` | For every positive length the minimum mass of a solvable distribution is at most the ceiling of five-fourths of the length plus three. |
| `Staircase.pointwise` | A certified cut walk for fifteen copies implies the pointwise lower bound. |

The checker replays concrete upper-bound paths, embeds the old placement into the longer strip and checks all sixteen new targets. Each target begins with the same placement. [Graph and legal move definitions](../Staircase/Graph.lean) · [Integer-grid coordinates](../Staircase/Coordinates.lean) · [Upper bound](../Staircase/Upper.lean)

The unconditional lower bound currently uses the separately checked Python and C++ certificates. The remaining formal work connects those window and transfer calculations to the original graph in Lean.

Use the pinned Lean 4.36.0 toolchain and mathlib revision. From the repository root run

```sh
lake exe cache get Mathlib.Data.Multiset.Count Mathlib.Data.Multiset.MapFold Mathlib.Data.Multiset.AddSub Mathlib.Data.Nat.Find
lake build
lake env lean research/CheckLean.lean
LEAN_NUM_THREADS=1 lake env leanchecker --fresh Staircase
```

The audit checks the theorem signature and permits only `propext`, `Classical.choice`, and `Quot.sound` as transitive axioms. [Audit source](CheckLean.lean)
