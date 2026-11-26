# Exact finite cases

Commands run at the checkout root with a C++17 compiler and Python 3.

```sh
c++ -O3 -std=c++17 research/finite.cpp -o /tmp/staircase-finite
/tmp/staircase-finite 8 10
python3 research/witness.py certificates/s8-8.json
/tmp/staircase-finite 9 12
python3 research/witness.py certificates/s8-9.json
```

| Length | Infeasible budget | Complete placements passing the weight test | Certified optimum |
| ---: | ---: | ---: | ---: |
| 8 | 10 | 19,751 | 11 |
| 9 | 12 | 18,182,744 | 13 |

The lower search enumerates multisets of exactly the indicated budget on the whole graph, adding pebbles in nondecreasing vertex order. This covers smaller placements by padding. For every target $t$, give $v$ weight $2^{-d(v,t)}$. No move increases total weight. During enumeration the current weight plus the remaining budget times the greatest available vertex weight must reach one for every target. This upper estimate permits pruning entire subtrees. All weights are scaled by two to the power of the diameter, so all comparisons are exact.

For each surviving complete placement the search tries all legal moves for one target at a time, restoring the placement after each attempt. It stops that branch upon reaching the target or dropping below weight one. Each move consumes a pebble, so the search terminates. A placement is rejected as soon as any target is unreachable. The procedure assumes no pile cap, directional restriction, or simultaneous coverage. To search for an upper witness directly, rerun the executable with the larger budget.

The upper files use the original square-grid coordinates $(x,y)$ and zero-based vertex indices. The Python checker reconstructs the induced grid, starts afresh for each target, and checks adjacency, stock and final occupancy on every path. Its optional certificate generator uses breadth-first search. For length 8 the eleven pebbles occupy slash/row positions $(2,2),(2,6),(5,5),(6,2),(7,7)$ with counts $2,2,4,2,1$. For length 9 the counts are $1,8,2,2$ on $(3,7),(4,4),(8,2),(8,6)$.
