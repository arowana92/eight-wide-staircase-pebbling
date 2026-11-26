# Eight-wide staircase pebbling

**Resolved · ✅ Complete Lean 4 proof of Conjecture 3.2.** For every positive integer $n$,

$$
\left\lceil\frac{5n}{4}\right\rceil
\le \pi_{\mathrm{opt}}(S_{8,n})
\le \left\lceil\frac{5n}{4}\right\rceil+3 .
$$

The bounds apply to the original staircase graph. Each target may use a different sequence of moves from the same initial distribution. [Lean verification and reproduction](research/lean-status.md) · [Mathematical proof](research/proof.md) · [Original conjecture](https://arxiv.org/abs/1611.09686)

The lower bound describes how many pebbles the rest of the strip can supply to a short window. An integer potential then bounds the total mass along any solvable strip, with a fixed loss at the ends. Fifteen disjoint copies of any putative counterexample would exceed that loss. For the upper bound an explicit construction adds four slashes for five pebbles. [Window obstructions](certificates/five-fourths-windows.txt) · [Potential certificate](certificates/five-fourths-dual.txt) · [Upper construction](research/upper.py)

Lean proves both bounds from legal moves, verifies all 231 local exclusions and checks a 6,516-row transfer certificate. The final theorem states the bounded additive error in mathlib’s Big-O notation. Two independently implemented Python and C++ checkers also verify the computer-assisted argument. The result has not undergone external peer review. [Lean theorem](Staircase/Asymptotics.lean) · [Verification receipt](research/lean-receipt.json) · [Python checker](research/proof.py) · [C++ checker](research/audit.cpp)

## Reproduce the result

With the pinned Lean 4.36.0 toolchain, run the following from the repository root. The verification guide includes the dependency-cache command, certificate regeneration and module-by-module replay. [Lean verification guide](research/lean-status.md)

```sh
lake build
lake env lean research/CheckLean.lean
LEAN_NUM_THREADS=1 lake env leanchecker --fresh --verbose Staircase
```

To reproduce the independent C++17 lower-bound and Python upper-bound checks, run

```sh
c++ -O3 -std=c++17 research/audit.cpp -o /tmp/staircase-audit
/tmp/staircase-audit certificates/five-fourths-windows.txt
python3 -B research/upper.py
```

The separate forward-move lower-bound verification runs with `python3 -B research/proof.py`. [Certificate construction and verification](research/proof.md)

## Research milestones

- The exact optimal masses at lengths 8, 9 and 10 are 11, 13 and 14. The first reproduces the value reported by the original authors. Each upper witness gives a legal sequence per target. [Finite-case results and replay](research/finite.md)
- Earlier window certificates gave the all-length lower bounds $21n/20$ and $9n/8$. [First certificate](research/projection.md) · [Nine-eighths certificate](research/window-bound.md)
- Concatenation and cut estimates bound the additive error around the limiting slope. A separate finite-state argument establishes that the slope is rational. [Uniform bounds](research/bounds.md) · [Finite-state reduction](research/finite-state.md)
- Small-period searches ruled out unassisted periodic counterexamples through period eight. [Periodic checks](research/periodic.md)
- The literature search covers the original paper, Papp's dissertation and later citing work. [Literature record](research/literature.md)
