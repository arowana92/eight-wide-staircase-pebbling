# The optimal pebbling number of eight-wide staircase graphs

**Theorem.** Every solvable placement on $S_{8,n}$ has at least $\lceil5n/4\rceil$ pebbles. For every positive integer $n$,
$$
\left\lceil\frac{5n}{4}\right\rceil
\le \pi_{\rm opt}(S_{8,n})
\le \left\lceil\frac{5n}{4}\right\rceil+3.
$$
In particular, Conjecture 3.2 of Győri, Katona, Papp and Tompkins holds. The lower bound uses a finite set of forbidden local placements and an integer potential on cuts. The finite claims can be checked by either of two programs. [Original paper, §3](https://arxiv.org/abs/1611.09686) · [Literature record](literature.md)

## From the strip to a window

Write $s=x-y$ and $r=x+y$ in the original square grid. The vertices are the pairs with $1\le s\le n$, $1\le r\le8$ and $s\equiv r\pmod 2$. An edge changes both coordinates by one in absolute value. Each slash (fixed $s$) has four vertices. An interval of $w$ slashes is a copy of $S_{8,w}$. Translate the slash coordinate and, for an odd translation, reflect $r$ to $9-r$.

A move consumes two pebbles at one vertex and creates one at a neighbor. Fix any solvable initial placement, and let $p_i$ be its total on slash $i$. Define integers from the two ends by
$$
 H_0=J_{n+1}=0,\qquad
 H_i=p_i+\lfloor H_{i-1}/2\rfloor,\qquad
 J_i=p_i+\lfloor J_{i+1}/2\rfloor .
$$

**Window lemma.** Keep all original vertices and pebbles in slashes $[a,b]$. Attach a left auxiliary vertex to all four vertices of slash $a$ and a right auxiliary vertex to all four of slash $b$. Give them $H_{a-1}$ and $J_{b+1}$ pebbles respectively. Every retained target is reachable in this augmented window.

**Proof.** On the left exterior, for any current distribution with slash totals $q_i$, set
$$
 W=\sum_{i<a}2^{i-(a-1)}q_i .
$$
Initially its floor is $H_{a-1}$, by induction using $\lfloor t/2\rfloor=\lfloor\lfloor t\rfloor/2\rfloor$ for $t\ge0$. A move wholly in the exterior cannot increase $W$. A move from the exterior to the window removes exactly two units of $W$. Its legality implies $W\ge2$ before the move. A move in the reverse direction adds exactly one unit. Use the reflected weight on the right exterior.

Take a solution for one target. At every prefix, keep the physical window stocks equal to the original stocks and each auxiliary stock at least the floor of its current exterior weight. Ignore moves wholly outside, copy moves wholly inside, and replace an exterior endpoint of a crossing move by the corresponding auxiliary vertex. Each replacement is legal and preserves the invariant. Empty exteriors have initial weight zero and no original crossing moves. Starting again from the same initial placement gives the claim for every target. ∎

## The finite local assertions

Each line of the window certificate contains integers $A,u_1,\ldots,u_w,B$. Its assertion is that **every** distribution of exactly $u_j$ pebbles among the four vertices of slash $j$, with stocks $A,B$ on the auxiliary vertices, misses at least one physical target. Which target fails may depend on the distribution. For a concrete example the line `3 0 2 0 3` tests all ten ways to put two pebbles on the middle slash of a three-slash window with three pebbles on each auxiliary vertex. [Window certificate](../certificates/five-fourths-windows.txt)

By padding any smaller placement to the specified totals and using monotonicity of reachability, the window lemma rules out the simultaneous inequalities
$$
 H_{a-1}\le A,\quad p_{a+j-1}\le u_j\ (1\le j\le w),\quad J_{a+w}\le B .
$$
This applies wherever the window occurs. Reflection handles either starting parity.

The rules were found by looking for cycles of mean mass below $5/4$ in a relaxed transfer graph, then testing short windows from those cycles. For the proof, the list only needs to satisfy the two finite assertions below. Every listed window is impossible, and the surviving transitions admit the stated potential.

| Window length | Rules | Placements checked |
| ---: | ---: | ---: |
| 3 | 36 | 1,909 |
| 4 | 39 | 17,030 |
| 5 | 96 | 181,362 |
| 6 | 53 | 429,422 |
| 7 | 7 | 339,550 |
| **Total** | **231** | **969,273** |

The number of placements for a line is $\prod_j\binom{u_j+3}{3}$. The largest of these finite tests uses sixteen pebbles including both auxiliary stocks. The Python verifier enumerates those placements and computes reachable targets by induction on total mass. For stock $P$, take the union of its occupied physical vertices and the target sets of all legal one-move successors. Every successor has one fewer pebble. Taking this union permits different move sequences for different targets. [Forward reachability and enumeration](projection.py) · [Certificate replay](proof.py)

The C++ verifier constructs the graph directly in $(x,y)$ coordinates. For each submultiset $Q$ of the starting tokens it computes the vertices where those tokens can be the exact ancestors of one pebble. A singleton can end at its own site. For a larger $Q$, split it in every way into two nonempty disjoint multisets. Intersect their possible endpoint sets, take all neighbors, and take the union over splits. The two derivations can be executed consecutively because they use disjoint tokens. Conversely the last move in an ancestry tree gives such a split. The union over all submultisets is exactly the set of reachable sites. The verifier first discards placements where an empty target has distance weight below one, or every neighbor has weight below two. These are valid necessary tests since $\sum_v P(v)2^{-d(v,t)}$ never increases and a final move into an empty target needs two pebbles at a neighbor. All comparisons use integers. [Independent ancestry verifier](audit.cpp)

## An integer potential on cuts

At the cut before slash $i$, record $(L,R)=(H_{i-1},J_i)$. After that slash write $(l,r)=(H_i,J_{i+1})$. With $p=p_i$ the relations are
$$
 l=p+\lfloor L/2\rfloor,\qquad R=p+\lfloor r/2\rfloor .
$$
Call a cut *low* when both coordinates are at most 36. Along a run of low cuts the state also remembers the still-matching proper prefixes of the forbidden words. Start with empty memory at the initial cut and on reentry from a cut outside the box.

On a transition between two low cuts, start each word with $L\le A$, and advance both new and previously active words if $p$ is at most the next letter. Discard a word whose letter test fails. Keep incomplete matches for the next step. If a word finishes with $r\le B$, reject this transition. A finish with $r>B$ has no further effect. Whenever at least one endpoint cut lies outside the box, allow the step and clear the memory. Every solvable placement gives a walk, since each rejection exhibits one of the forbidden windows. Forgetting a prefix can only remove a reason for rejection.

**Finite potential lemma.** On the low states reachable from any pair in $\{0,\ldots,36\}^2$ with empty memory, there are integers $-56\le d\le0$ such that each allowed low-to-low edge $x\to y$ satisfies
$$
 d(y)-d(x)\le C,\qquad
 C=4\bigl(2p+\lceil L/2\rceil+\lceil r/2\rceil\bigr)-20. \tag{1}
$$
The Python checker numbers the states by breadth-first discovery from the empty-memory pairs ordered lexicographically. For each source it tries $p=0,\ldots,R$ in order and the two possible $r=2(R-p),2(R-p)+1$ in order. It retains exactly the transitions just defined. It assigns the listed integer to each state in the sparse potential file and zero to unlisted states. It checks (1) directly on all 1,727,870 edges of the 55,558-state graph. [Sparse potential](../certificates/five-fourths-dual.txt) · [Verifier and optional regeneration](proof.py)

The C++ checker retains distinct *remaining suffixes* with their right thresholds, so common suffixes from different rules coalesce. It enumerates edges by choosing $r$ and deriving $p$. It finds a potential afresh on 26,778 states and 804,381 edges by repeated relaxation from the zero vector, then tests every inequality. This calculation uses only the window file, with the same resulting range $[-56,0]$. Either finite computation suffices for the lemma. [Independent transfer verifier](audit.cpp)

**Extension to arbitrary stocks.** Put $d=0$ on cuts outside the box. If $L$ or $r$ is at least 37 then at least one rounded-up term in (1) is at least 19. If $l$ is at least 37 then $2p+\lceil L/2\rceil\ge l$, and if $R$ is at least 37 then $2p+\lceil r/2\rceil\ge R$. In every case $C\ge4\cdot19-20=56$. Since the difference of any two potentials is at most 56, (1) holds for every transition involving an outside cut, including entry into a low state with empty memory. This step covers arbitrary nonnegative slash totals.

For a state $x$ at $(L,R)$ set $F(x)=d(x)+4(L-R)$. The cut recurrences give the identity
$$
 C+4\bigl((l-r)-(L-R)\bigr)=16p-20 .
$$
Consequently $F(y)-F(x)\le16p-20$ on every step. Sum over the full strip of length $n$ and mass $m$. The first left coordinate is zero and the last right coordinate is zero, so
$$
 16m-20n\ \ge\ F(\mathrm{last})-F(\mathrm{first})
 \ \ge\ -56+4(H_n+J_1)\ \ge\ -56. \tag{2}
$$

**Removal of the boundary loss.** Place fifteen copies of this very placement on consecutive disjoint $n$-slash blocks of $S_{8,15n}$. Reflect the rows of a block when required by parity. Each target can use the solution inside its own block, so (2) applies to the resulting placement of mass $15m$. If $4m-5n$ were negative, it would be at most $-1$, giving $16(15m)-20(15n)\le-60$. This contradicts (2). Thus $4m\ge5n$ for every finite solvable placement. ∎

## A construction with at most three extra pebbles

The authors already obtain the asymptotic upper bound by adding a diagonal to their seven-wide construction. In the present coordinates, rows 1 through 7 induce the authors’ primed width-seven strip. For $n\ge8$ Theorem 2.14 gives it a solvable distribution with at most $n+3$ pebbles. Pair the row-8 vertices in slash order. Put one extra pebble on the common row-7 neighbor of each pair and on a row-7 neighbor of any singleton. The number added is $\lceil\lfloor n/2\rfloor/2\rceil\le\lceil n/4\rceil$. The old placement can bring one pebble to any marked site, making two available there for a move to the selected row-8 target. This gives the asserted upper bound in the range of the conjecture. [Theorem 2.14, Figure 10 and Claim 3.1](https://arxiv.org/pdf/1611.09686)

Here is a second construction covering **every** $n\ge1$. In the table an entry $(s,r)^p$ denotes $p$ pebbles at $(s,r)$, with exponent one omitted. The verifier finds and replays a path to each target from these stocks. [Construction and base checks](upper.py) · [Move-sequence checker](witness.py)

| $n$ | Starting piles | Mass |
| ---: | --- | ---: |
| 1 | $(1,1),(1,3),(1,5),(1,7)$ | 4 |
| 2 | $(1,1)^2,(1,7)^2,(2,4)^2$ | 6 |
| 3 | $(1,3),(1,5)^4,(1,7),(2,2)$ | 7 |
| 4 | $(1,1)^2,(1,5)^4,(2,2),(3,7)$ | 8 |
| 5 | $(1,5)^4,(2,2),(5,1),(5,5)^4$ | 10 |
| 6 | $(1,1),(1,5)^4,(1,7),(3,3),(5,3)^2,(5,7)^2$ | 11 |

For $n\ge3$ maintain a pile of four at $(1,5)$. Translate a solvable placement four slashes to the right and add four pebbles at $(1,5)$ and one at $(2,2)$. All old targets retain their solutions. For the first four slashes consider just the two four-pebble piles at $(1,5),(5,5)$ and the singleton.

* Every site in rows 3 through 7 of these slashes is within two steps of one four-pebble pile. Four pebbles can send one along a path of length two.
* Each pile can send one pebble to $(3,3)$ in two steps, using distinct starting stocks. Combining them there reaches either row-2 vertex. Combining them instead at $(3,7)$ reaches either row-8 vertex.
* Send the first such combined pebble to $(2,2)$. Together with the singleton there it reaches either row-1 vertex.

Each target uses its own sequence. The new block again has the required four-pebble pile on its first slash. Lengths 3, 4, 5 and 6 give the four residue classes. Every extension adds five pebbles while $\lceil5(n+4)/4\rceil=\lceil5n/4\rceil+5$. The base table proves the upper bound, completing the theorem. ∎

## Reproduction

From the root of the checkout, use Python 3 and a C++17 compiler. Each of the first two methods checks the entire finite part of the lower bound. The C++ program reads just the window list and derives its own potential.

```sh
c++ -O3 -std=c++17 research/audit.cpp -o /tmp/staircase-audit
/tmp/staircase-audit certificates/five-fourths-windows.txt
python3 -B research/proof.py
python3 -B research/upper.py
```

To regenerate the saved potential, run `python3 -B research/proof.py --part dual --regenerate`. To print the explicit construction at a chosen length, run e.g. `python3 -B research/upper.py --length 100`.

Lean 4 formalizes the entire proof from legal moves, including the physical window exclusions and the numerical transfer certificate. The formal development derives the two-sided integer bounds and the original real-valued Big-O statement. Its transfer checker uses a second certificate with separate positions for each rule prefix. The verification guide gives the clean build, axiom audit and fresh kernel replay commands. [Lean verification guide](lean-status.md) · [Pointwise theorem](../Staircase/Resolution.lean) · [Asymptotic theorem](../Staircase/Asymptotics.lean)

The additive constant three relative to the ceiling is attained at length two. Running the whole-graph checker at length two and budget five excludes all 54 placements surviving its weight test, and the construction above supplies six pebbles. This concerns the uniform bound over all positive lengths.

The exact $8\times8$ test uses a separate whole-graph search. Budget ten leaves 19,751 complete placements after integer weight pruning, and each fails at least one target. At budget eleven a saved placement admits legal paths to all 32 targets. The repository also contains the exhaustive checks at lengths nine and ten. [Finite-case proofs, witnesses and commands](finite.md)
