# Eight-wide staircase pebbling

**Conjecture 3.2 is proved by a computer-assisted argument.** For every positive integer $n$,
$$
\left\lceil\frac{5n}{4}\right\rceil
\le \pi_{\mathrm{opt}}(S_{8,n})
\le \left\lceil\frac{5n}{4}\right\rceil+3 .
$$
The bounds apply to the original staircase graph. Each target may use a different sequence of moves from the same initial distribution. [Proof and reproduction instructions](research/proof.md) · [Original conjecture](https://arxiv.org/abs/1611.09686)

The lower bound describes how many pebbles the rest of the strip can supply to a short window. An integer potential then bounds the total mass along any solvable strip, with a fixed loss at the ends. Fifteen disjoint copies of any putative counterexample would exceed that loss. For the upper bound an explicit construction adds four slashes for five pebbles. [Window obstructions](certificates/five-fourths-windows.txt) · [Potential certificate](certificates/five-fourths-dual.txt) · [Upper construction](research/upper.py)

Two independently implemented checkers verified all 231 window obstructions, covering 969,273 placements. One checks the saved potential on 1,727,870 edges. The other derives its own potential from the window list using a different representation of the states. Lean checks the integer estimates extending the calculation to arbitrarily large stocks and lengths. These checks were performed in this project. The result has not undergone external peer review. [Python checker](research/proof.py) · [C++ checker](research/audit.cpp) · [Lean lemmas](research/ProofKernel.lean)

**Lean formalization in progress.** Lean proves the upper bound for the original graph at every positive length. The formal lower bound is in development. [Lean endpoints and audit](research/lean-status.md)

## Reproduce the result

From the root of the checkout, run the standalone C++17 lower-bound verifier and the Python upper-bound verifier.

```sh
c++ -O3 -std=c++17 research/audit.cpp -o /tmp/staircase-audit
/tmp/staircase-audit certificates/five-fourths-windows.txt
python3 -B research/upper.py
```

For the separate forward-move lower-bound verification, run `python3 -B research/proof.py`. The proof gives the regeneration and optional Lean commands.

## Research milestones

- The exact optimal masses at lengths 8, 9 and 10 are 11, 13 and 14. The first reproduces the value reported by the original authors. Each upper witness gives a legal sequence per target. [Finite-case results and replay](research/finite.md)
- Earlier window certificates gave the all-length lower bounds $21n/20$ and $9n/8$. [First certificate](research/projection.md) · [Nine-eighths certificate](research/window-bound.md)
- Concatenation and cut estimates bound the additive error around the limiting slope. A separate finite-state argument establishes that the slope is rational. [Uniform bounds](research/bounds.md) · [Finite-state reduction](research/finite-state.md)
- Small-period searches ruled out unassisted periodic counterexamples through period eight. [Periodic checks](research/periodic.md)
- The literature search covers the original paper, Papp's dissertation and later citing work. [Literature record](research/literature.md)
