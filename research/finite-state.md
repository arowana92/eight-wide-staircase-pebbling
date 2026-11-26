# A finite-state reduction for the unknown slope

Write $a_n=\pi_{\rm opt}(S_{8,n})$ and $\lambda=\inf_n a_n/n$. The preceding cut estimate gives $a_h\le5h/4+40$ at every positive length. The following argument bounds the alphabet and interface flows needed to compute $\lambda$ by a finite minimum-cycle-mean problem. The cycle mean has yet to be evaluated. [Cut estimate](bounds.md)

## A uniform bound on the mass of an optimal slash

Fix an arbitrary optimal placement $P$ on a finite strip, with slash masses $p_s$ extended by zero outside the strip. Write $B_j$ for the potential of the cut between slashes $j,j+1$ defined in the cut estimate. For any interval $I=[l,r]$ intersecting the strip in $h$ slashes,
$$
\sum_{s\in I}p_s\le 5h/4+40+4(B_{l-1}+B_r).
$$

To see this, replace the restriction to $I$ by a solvable placement on those $h$ slashes. At each vertex immediately **outside** either end, add the floor of that cut's potential if the vertex exists. Every exterior target can replay its old solution with all moves involving $I$ erased. At each retained vertex the bonus covers the omitted incoming moves, including at every intermediate step. Interior targets use the replacement alone. Thus optimality bounds the removed mass by the cost of the replacement and the bonuses. The argument includes intervals extending past an end of the strip.

Fix a slash $i$ and put $\rho=31/32$. Apply the inequality to $[i-h,i+h]$ for integer radii $h\ge0$, weighting it by $(1-\rho)\rho^h$. The left side sums to $S_i=\sum_s\rho^{|s-i|}p_s$. The mean interval length is at most $(1+\rho)/(1-\rho)=63$. Each cut $j$ occurs at exactly one radius, its distance $d(i,j)$ to $i$, where $d(s,j)=\mathrm{dist}(s,\{j,j+1\})$. Since $|s-i|\le d(i,j)+1+d(s,j)$,
$$
\sum_j\rho^{d(i,j)}2^{-d(s,j)}
\le \rho^{|s-i|-1}\sum_j(2\rho)^{-d(s,j)}
=\frac{4}{2\rho-1}\rho^{|s-i|}.
$$
There are two cuts at each distance from $s$, including distance zero. The averaged bonus is therefore at most $16(1-\rho)S_i/(2\rho-1)=(8/15)S_i$. It follows that
$$
S_i\le (5/4)63+40+(8/15)S_i,\qquad
p_i\le S_i\le 7125/28<255.
$$
In particular **every optimal distribution has at most 254 pebbles on any one slash**. This bound was derived by replacement and imposes no hypothesis on the distributions used to define $a_n$.

## Integer flows with a fixed interface bound

On any placement with at most 254 pebbles per slash, a target $u$ in slash $i$ has initial distance weight at most $\sum_s 254\,2^{-|s-i|}\le762$. This bounds the maximum number of pebbles that can be collected at $u$.

For one target, record the number of moves on each directed edge. The required balances are initial stock plus incoming counts minus twice outgoing counts, at least one at the target and at least zero elsewhere. These conditions on nonnegative integer counts suffice. On a directed cycle subtract one from every edge, improving the balance at each cycle vertex. After eliminating all cycles, process the remaining vertices in topological order, executing all their outgoing moves when visited. The balances ensure legality. Conversely, legal sequences give balances by counting.

In such an acyclic realization, all pebbles used for departures from a vertex are available together before its outgoing moves there. There are at most 381 departures at any vertex. Each of the seven edges at an interface can therefore be described by a signed integer from $-381$ through $381$, positive for a rightward flow and negative for a leftward flow. The no-cycle argument justifies using a single sign per edge.

## Explicit finite graph

Use a four-tuple $p$ of nonnegative integers with sum at most 254 as the letter for one slash. Keep the parity of the slash to determine the seven cross edges. Let $F=\{-381,\ldots,381\}^7$ be the interface alphabet. For $x,y\in F$, write $T_p^d(x,y)$ if the incoming and outgoing counts encoded on the left by $x$ and on the right by $y$ give final balance at least $d$ coordinatewise on this slash. Use $d=0$ for a slash with no demand, or one of the four unit vectors $e_i$ for a target.

At each interface keep two subsets $L,R$ of $F$. $L$ records feasible interface flows through the prefix with no target. $R$ does the same for the suffix. Across a slash with letter $p$, join state $(L,R)$ to state $(L',R')$ exactly when
$$
L'=\{y:\exists x\in L,\ T_p^0(x,y)\},\qquad
R=\{x:\exists y\in R',\ T_p^0(x,y)\}
$$
and for each $i=1,2,3,4$ there exist $x\in L,y\in R'$ satisfying $T_p^{e_i}(x,y)$. The existential choices can depend on $i$. Alternate the parity in the states. Require $L=\{0\}$ at the left end, the usual first-slash parity, and $R=\{0\}$ at the right end. Here $0$ denotes the all-zero interface flow.

The boundary conditions and recurrences determine the prefix and suffix sets on a given word. For a chosen target, glue its prefix flow, local balance and suffix flow. Cycle cancellation yields legal moves for that target. Conversely every target solution has a bounded acyclic flow that passes these tests. Thus accepted words describe exactly the solvable placements within the slash cap. Since this includes every optimum, the minimum cost of an accepted walk of length $n$ equals $a_n$ when the cost of an edge is the sum of its letter.

Discard states unreachable from a start or unable to reach a finish. Every long accepting walk decomposes into cycles and a remaining simple path of bounded length. Its asymptotic mean cost is at least the minimum cycle mean in the retained graph. A minimizing cycle can be reached, repeated, and followed by a path to a finish. Along these lengths the upper limit of the cost per slash is at most that cycle mean. The full limit exists by subadditivity. Hence $\lambda$ equals this **rational, computable minimum cycle mean**.

Equivalently, assign each edge cost $4\sum p_i-5$. Conjecture 3.2 holds precisely when the retained graph has no negative cycle. A cycle exclusion or a negative cycle with accepting access and exit walks would settle the question. The size of the power sets in this construction makes direct enumeration impractical. Repetition here concerns accepting walks with their boundary conditions. A repeated interior pattern can in principle depend on pebbles supplied from its ends.
