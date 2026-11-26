# Eight-wide staircase pebbling

**Work in progress.**

Conjecture 3.2 of Győri, Katona, Papp and Tompkins predicts that the optimal pebbling number of the width-eight staircase graph of length *n* differs from 5*n*/4 by at most a constant independent of *n*.

A pebbling move removes two pebbles from one vertex and puts one on an adjacent vertex. An initial placement is solvable if each vertex can receive a pebble, starting afresh from that placement for each target. The optimal pebbling number is the smallest number of pebbles in a solvable placement.

The goal is to prove the uniform additive bound or exhibit unbounded deviations. Individual graph sizes provide test cases for constructions and lower bounds.

[Original conjecture and graph definitions, *The Optimal Pebbling Number of Staircase Graphs* (2016 preprint)](https://arxiv.org/abs/1611.09686)

## Research milestones

- An exhaustive integer search reproduces $\pi_{\rm opt}(S_{8,8})=11$ and gives $\pi_{\rm opt}(S_{8,9})=13$. Each upper certificate contains one legal move sequence per target. [Reproduction commands and search proof](research/finite.md)
- Concatenation makes the conjectured lower bound equivalent to $4\pi_{\rm opt}(S_{8,n})\ge5n$ for every finite length. A cut argument bounds the additive error relative to the unknown limiting slope by 40. Its value is still undetermined. [Uniform bounds](research/bounds.md)
- The original paper and Papp's dissertation give the width-eight upper construction. [Literature record](research/literature.md)
- A local replacement argument bounds every optimal slash by 254 pebbles. It reduces the unknown slope to the minimum cycle mean of an explicit finite graph. The graph has not been evaluated. [Finite-state reduction](research/finite-state.md)
- Exhaustive checks exclude an unassisted periodic counterexample of period at most eight, including odd periods with row reflection. [Periodic obstructions and replay](research/periodic.md)
