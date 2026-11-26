# Lean verification of Conjecture 3.2

**Resolved · Complete Lean 4 proof.** For every positive integer $n$,

$$
\left\lceil\frac{5n}{4}\right\rceil\leq \pi_{\rm opt}(S_{8,n})
\leq \left\lceil\frac{5n}{4}\right\rceil+3.
$$

Lean also proves the original asymptotic statement directly. Each target is reachable separately from the same initial multiset, and the number of pebbles on a vertex is unrestricted. [Pointwise theorems](../Staircase/Resolution.lean) · [Asymptotic theorem](../Staircase/Asymptotics.lean) · [Verification receipt](lean-receipt.json)

| Lean declaration | Statement |
| --- | --- |
| `Staircase.adj_iff_grid` | An encoded edge is precisely a unit step in the original square grid between vertices of the strip. The accompanying coordinate lemmas prove injectivity and surjectivity. |
| `Staircase.solvable_lower` | Every solvable initial distribution at positive length $n$ contains at least $\lceil5n/4\rceil$ pebbles. |
| `Staircase.optimal_bounds` | The optimum lies between $\lceil5n/4\rceil$ and $\lceil5n/4\rceil+3$, inclusive. |
| `Staircase.conjecture32` | The real-valued difference $\pi_{\rm opt}(S_{8,n})-5n/4$ is $O(1)$ as $n\to\infty$. |

## From legal moves to the bounds

1. A placement is a multiset of vertices. A move replaces two copies of one vertex by one copy of a neighbor. The upper bound replays explicit legal paths at the base lengths and in the four-slash extension. The placement serving the old strip and the sixteen new targets costs five more pebbles. [Graph and reachability](../Staircase/Graph.lean) · [Square-grid coordinates](../Staircase/Coordinates.lean) · [Upper construction](../Staircase/Upper.lean)
2. Lean projects any successful sequence on the full strip to a window by collecting possible arrivals at two auxiliary vertices. Every reachable pebble has a binary ancestry tree. For each of the 231 forbidden windows, a finite table covers the resources needed by any such tree. A subdivision of the possible initial placements then identifies an unreachable target in each part. This verifies the exclusions even when different targets use different sequences. [Window projection](../Staircase/Windows.lean) · [Ancestry](../Staircase/Ancestry.lean) · [Checker soundness](../Staircase/WindowCheck.lean) · [All 231 proofs](../Staircase/AllWindows.lean)
3. The transfer certificate tracks prefixes of the forbidden windows at successive cuts. Its 1,111 prefix positions are indexed separately for the 231 rules. Its 6,516 rows comprise 1,369 starting pairs and 5,147 additional rows with positive debt. Lean checks the masks, successor inequalities, and the debt limit of 14. Large cut coordinates are covered by a separate arithmetic inequality. Induction gives $16|P|-20n\geq-56$ for an arbitrary solvable placement. Applying it to fifteen copies removes the boundary loss. [Prefix semantics](../Staircase/Matcher.lean) · [Transfer argument](../Staircase/Transfer.lean) · [Fifteen-copy argument](../Staircase/Copies.lean)

The Python exporters generate witnesses. Lean verifies their contents using its kernel. The earlier Python and C++ programs check the same mathematical bounds using separate implementations and a different transfer certificate. The exact value $\pi_{\rm opt}(S_{8,8})=11$ also has its own whole-graph computational verification. [Computer-assisted proof](proof.md) · [Finite-case certificates](finite.md)

## Reproduce the Lean verification

Use the repository’s pinned Lean 4.36.0 toolchain and mathlib revision. From the repository root, run

```sh
lake exe cache get Mathlib.Analysis.Asymptotics.Defs Mathlib.Analysis.Normed.Group.Real \
  Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Order.Filter.AtTopBot.Basic \
  Mathlib.Algebra.Order.Monoid.Multiset Mathlib.Data.List.Induction \
  Mathlib.Data.Multiset.AddSub Mathlib.Data.Multiset.Bind Mathlib.Data.Multiset.Count \
  Mathlib.Data.Multiset.Filter Mathlib.Data.Multiset.MapFold Mathlib.Data.Multiset.Replicate \
  Mathlib.Data.Nat.Find
lake build
lake env lean research/CheckLean.lean
LEAN_NUM_THREADS=1 lake env leanchecker --fresh --verbose Staircase
```

The audit checks the endpoint types and the transitive axioms of every project declaration in the imported environment. Its allowlist consists of `propext`, `Classical.choice`, and `Quot.sound`. The stock checker’s `--fresh` mode replays the root and its imported declarations starting from an empty kernel. To repeat the additional module-by-module replay, run `LEAN_NUM_THREADS=1 lake env python3 research/replay_lean.py`. [Audit source](CheckLean.lean) · [Module replay](replay_lean.py) · [Machine-readable receipt](lean-receipt.json)

On the verification machine, running the non-fresh checker on the whole package in one process exited with signal 11 while resolving module paths. The module replay script invokes the stock checker once per source module. Independent processes can be run concurrently with `--jobs 4`.

To regenerate the committed certificate modules, run the following in a clean checkout. An empty diff confirms byte-for-byte reproduction.

```sh
python3 -B research/lean_upper.py
python3 -B research/lean_windows.py
python3 -B research/lean_transfer.py
python3 -B research/lean_header.py
git diff --exit-code -- Staircase
```
