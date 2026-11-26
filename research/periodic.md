# Short periods on the infinite strip

For each $1\le p\le8$, every solvable unassisted pattern on the doubly infinite strip, invariant under a shift of $p$ slashes (and row reflection for odd $p$), has at least $\lceil5p/4\rceil$ pebbles per period. Solvability uses a finite sequence for each target. The assertion concerns these periodic initial placements. The accepting cycles of the general finite-state reduction can also use support from finite end regions. [General reduction](finite-state.md)

## Reproduce

```sh
c++ -std=c++17 -O3 research/periodic.cpp -o /tmp/staircase-periodic
python3 research/periodic.py /tmp/staircase-periodic
```

The Python command checks a positive control at period four, reruns the C++ enumerator, compares the entire set of survivors against the certificate file, and checks one unreachable target for each remaining motif. Both stages use exact integers. The finite-window checker also uses rational arithmetic to set its boundary allowances.

| Period | Budget | Placements with an anchored maximum tested, counting ties | Distinct motifs needing the window check |
| ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 0 |
| 2 | 2 | 4 | 0 |
| 3 | 3 | 48 | 0 |
| 4 | 4 | 544 | 0 |
| 5 | 6 | 33,976 | 26 |
| 6 | 7 | 367,636 | 13 |
| 7 | 8 | 4,034,128 | 4 |
| 8 | 9 | 44,726,432 | 0 |

## Why the exclusions are valid

Padding reduces the search to budget $\lfloor(5p-1)/4\rfloor$. Patterns containing only piles of size at most one cannot make a first move. A symmetry takes a maximum pile to the first slash. The enumerator fixes its location and size and tries every way to place the remaining budget. An odd shift is accompanied by the reflection $r\mapsto9-r$.

For a target $t$, use weight $2^{-\max(|s-s_t|,|r-r_t|)}$ at $(s,r)$. A move changes the exponent by at most one, so the initial sum bounds the number collectable at $t$. It converges for periodic sources. For each source orbit, sum the contributions at slash offsets from $-7$ through $7$ directly. On each remaining side the contribution forms a geometric series with ratio $2^{-p}$. If $D$ is the first absolute offset in that tail, its scaled contribution is $2^{7+p-D}$ in units of $1/[128(2^p-1)]$.

A vertex with weight below two can never send a pebble. Drop its initial pebbles when testing reachability elsewhere and repeat. For a sharper test, take an acyclic sequence for one target and follow a branch backward to a supplier $u$. Its supply must be obtainable without using the descendant vertices $F$ already on the branch. Subtract their individual contributions from the weight at $u$, keeping all other remaining sources. The floor is an upper bound. Another upper bound is the initial pile at $u$ plus the sum over neighbors $v\notin F$ of half their respective supply bounds, rounded down, with $u$ added to the forbidden set for each child. This follows by collecting each sender's incoming pebbles before its departures in topological order. These estimates allow different neighbors to reuse resources and therefore give upper bounds. The code uses the smaller estimate, to depth at most six. Deletion is always by physical vertex along the branch, even if another translated copy contributes to the same orbit. Every empty target needs at least one eligible neighbor able to send.

For each surviving motif retain its period and seven extra slashes on each side. Add the two-sided cut allowance $\lfloor B_j\rfloor$ at **each** vertex of each window end, computed by summing the periodic slash masses exactly. Any finite sequence for a retained target could be replayed inside this enlarged placement by omitting outside moves. Thus an unreachable target in the window proves an obstruction on the full infinite strip. [Cut-potential proof](bounds.md)

The Python checker removes impossible senders using shortest-path weights on the remaining induced graph. It keeps the target and the component that could feed it. For demand one at the target, let $b$ be initial stock minus demand. A negative entry $b_v$ requires an incoming move from some neighbor $u$. Branch over every eligible $u$, replace $b$ by $b+e_v-2e_u$, and repeat. Acyclic solutions may omit all departures from the target. Every feasible family of balance counts contains some incoming edge at a deficit, so one branch preserves feasibility. Conversely each accepted branch supplies balanced integer counts, which can be executed after cycle cancellation. A negative distance-weighted sum rules out the branch. The total balance decreases by one per step, and the search memoizes repeated balances.

The positive control has four pebbles at $(1,5)$ and one at $(2,2)$ per four slashes. The four-pebble piles reach rows 3 through 7 within two steps. Two adjacent piles can each send one pebble to their midpoint on row 3 or row 7, which reaches the neighboring outer targets on rows 2 and 8. The added singletons on row 2 can then receive a second pebble and reach all targets on row 1.
