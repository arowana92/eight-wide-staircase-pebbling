# An all-length lower bound by cut potentials

**Proposition.** Every solvable placement $P$ on $S_{8,n}$ satisfies $20|P|\ge21n$. There is no restriction on pile sizes. Each target is tested separately from the same initial stock.

The finite certificate and all exhaustive checks use Python 3's standard library. From the checkout root, run the command below. The optional flag regenerates the 1.3 KB integer potential before checking it.

```sh
python3 research/projection.py
python3 research/audit_projection.py
python3 research/projection.py --regenerate
```

The independent audit builds edges from the original square-grid coordinates. It enumerates the 56,810 transitions from pairs of interfaces and checks 82,556 finite placements by a second reachability algorithm. That algorithm splits the initial tokens into two disjoint groups. If each group can produce a pebble at the same vertex, the groups together can reach any neighbor. Recursing through all splits is complete by tracing the two parents of the last pebbling move. The audit shares the numerical potential file with the first checker and imports none of its implementation.

## How much help can come from outside a window?

Let $p_i$ be the total on slash $i$. Define
$$
H_0=J_{n+1}=0,\qquad H_i=p_i+\lfloor H_{i-1}/2\rfloor,\qquad J_i=p_i+\lfloor J_{i+1}/2\rfloor .
$$
For a window $[a,b]$, keep the actual four vertices in each slash inside the window. At its left and right ends attach one auxiliary vertex each, adjacent to all four vertices of that end. Give the left auxiliary vertex $H_{a-1}$ pebbles and the right one $J_{b+1}$. Every window target reachable in the original strip remains reachable in this graph.

Indeed, collapse every exterior slash to one vertex, initially carrying its slash total. A physical move maps to a legal move in the collapsed graph. For a target inside the window take an acyclic solution and discard moves outside the ancestral dependencies of the target pebble. Beyond the first auxiliary vertex the exterior is a pendant path. Each used edge of this path must point toward the window since it is a bridge. Greedy inward moves gather the maximum contribution before the auxiliary vertex is used, giving exactly the recurrence above. Transfers between the window and an auxiliary vertex remain allowed in the check. At a physical end an optional zero-stock auxiliary vertex enlarges the possibilities further. [Integer balance and cycle cancellation](finite-state.md)

## Irreducible pieces and three window tests

If no sequence can make a move across a particular interface in either direction, cutting it leaves two separately solvable placements. Repeat these cuts. In any resulting piece, each inner slash must be able to hold two pebbles in total at some time. Otherwise no move can leave it, and deliveries to it from opposite sides could be executed independently. Deliveries from both sides would put two pebbles there, so at least one adjacent interface would be unused. This is the paper's cut lemma. Collapsing all slashes to the path therefore gives the necessary inner-slash inequality
$$
p_i+\lfloor H_{i-1}/2\rfloor+\lfloor J_{i+1}/2\rfloor\ge2 .
$$
On a path only moves toward the target are needed, by the same bridge argument. [Original paper, Lemmas 2.3–2.5](https://arxiv.org/abs/1611.09686)

The following configurations are impossible in any solvable piece.

- If $p_i=2$, one cannot have both $H_{i-1}\le1$ and $J_{i+1}\le1$ at an inner slash. Write $a=p_{i-1}$ and $c=p_{i+1}$, both zero or one. The two auxiliary stocks outside the three-slash window are at most $3-2a$ and $3-2c$, by the recurrences. The checker distributes the masses $(a,2,c)$ in all 250 possible ways across the four choices of $(a,c)$, even granting these upper stocks. Every placement misses a target.
- If $p_i=4$, one cannot have $H_{i-1}=J_{i+1}=0$. The two neighboring slashes are empty and the next exterior stocks are at most one. All 35 placements of the four pebbles fail on this three-slash window.
- Five consecutive unit-mass slashes cannot have exterior stocks at most two on both sides. The checker exhausts $4^5=1024$ placements with two pebbles on each auxiliary vertex.

For each placement the checker takes the union of vertices occupied over all reachable states. It follows every legal move and uses the fall in total mass to terminate. Each vertex in that union has its own move sequence.

## A telescoping integer certificate

At the interface before slash $i$ store $x=(L,R,k)=(H_{i-1},J_i,k)$. The integer $k$ tracks successive unit slashes starting with a left exterior stock at most two, capped at five. For the state $y=(l,r,j)$ after reading $p=p_i$, the recurrences are
$$
l=p+\lfloor L/2\rfloor,\qquad R=p+\lfloor r/2\rfloor .
$$
When $p=1$ and either $k>0$ or $L\le2$, set $j=\min(5,k+1)$. Otherwise set $j=0$. A run that starts with $H\le2$ keeps $H\le2$ along the ones. Thus $j=5$ and $r\le2$ would violate the five-slash test. Discard these transitions, those forbidden by the two three-slash tests, and those violating the inner-slash inequality.

The supplied integer table defines $d(x)$, with value zero on unlisted states. Its entries lie between $-132$ and zero. Put $F(x)=d(x)+20(L-R)$. For every remaining transition the certificate proves
$$
80p-84\ \ge\ F(y)-F(x).
$$
Inside the box $0\le L,R,l,r\le23$ the verifier checks all 56,810 remaining transitions, including every run state. Outside the box, use the identity
$$
80p-20[(l-r)-(L-R)] = 20(2p+\lceil L/2\rceil+\lceil r/2\rceil).
$$
If $L$ or $r$ is at least 24, the right side is at least 240. If $l$ or $R$ is at least 24, the recurrences give the same lower bound. This covers arbitrary input masses, since $240-84\ge132$. [Integer potential](../certificates/projection-dual.json)

## The two physical ends

For $n\ge6$, reserve the first two and last four slashes. Let $x$ be the state after the first two, with run count reset to zero, and $y$ the state before the last four. With $S_{\rm left}$ and $S_{\rm right}$ their respective masses, the endpoint checks establish
$$
80S_{\rm left}-2\cdot84-F(x)\ge32,\qquad
80S_{\rm right}-4\cdot84+F(y)\ge-32 .
$$

Here is why these are finite checks. View either end from its physical extremity. For a tuple of local stocks let $S$ be its mass and $h$ the effective stock at its last slash, computed by the one-sided recurrence, giving $h\le S$. Give the one exterior auxiliary vertex an arbitrary integer stock $K\ge0$. For the left end use $x=(h,K,0)$. For the right end allow all six states $y=(K,h,k)$, reversing the slash order and reflecting the rows if parity requires. For an end of length $w$, the left expression is at least $60S+20K-84w$. The right expression is at least $60S+20K-84w-132$. Thus only finitely many $(S,K)$ can fall below the indicated thresholds. For each actual stock tuple whose expression is too small the verifier exhausts its moves and finds a missed end-window target. It checks 108 such tuples with bank stock at the left and 34,355 at the right.

The transition inequalities telescope between $x$ and $y$. The endpoint terms cancel, giving $80|P|-84n\ge0$. For length six there are no intermediate transitions and the two boundary states coincide. For lengths one through five a direct exhaustive check rules out budget $n$, which suffices by integrality. Adding the inequalities for all irreducible pieces proves the proposition. ∎
