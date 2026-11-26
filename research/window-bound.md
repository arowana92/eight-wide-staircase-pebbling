# A uniform lower bound of nine pebbles per eight slashes

**Theorem (computer-assisted).** For every positive integer $n$ and every solvable placement $P$ on $S_{8,n}$,
$$
|P|\ \ge\ \left\lceil\frac{9n}{8}\right\rceil .
$$
All piles and lengths are unrestricted. The proof checks finitely many local obstructions, converts them into a lower bound with an additive constant, and removes the constant by concatenation. The final certificate reaches the coefficient $5/4$. [Full proof](proof.md)

```sh
python3 research/window_bound.py
python3 research/window_bound.py --ancestry
```

The first command verifies 37,778 finite placements by forward moves and 249,709 integer inequalities. The second checks the physical obstructions with a separate implementation using disjoint pebble ancestry trees. Both read the same finite dual certificate. Use the optional flag `--regenerate` to recompute the dual.

## Window obstructions

Write $p_i$ for the stock on slash $i$ and define
$$
H_0=J_{n+1}=0,\qquad H_i=p_i+\lfloor H_{i-1}/2\rfloor,\qquad
J_i=p_i+\lfloor J_{i+1}/2\rfloor .
$$
For a window beginning at $s$ and ending at $t$, keep its physical vertices and attach one hub adjacent to every vertex at each respective end. Give these hubs $H_{s-1}$ and $J_{t+1}$ pebbles. Solvability of the original strip implies reachability of every retained vertex in this window. The projection collapses each exterior slash to a path vertex. In a target's acyclic dependency graph every used pendant-path edge points toward the window, so the contribution at the adjoining hub is bounded by the recurrence. Moves involving the hub and the window remain legal. [Detailed projection argument](projection.md)

A rule $(A,w,B)$ consists of two hub stocks and a word of slash masses. Exhaustive search establishes that no placement with precisely those slash masses and hub stocks reaches all physical targets. By padding, any window with left stock at most $A$, masses componentwise at most $w$, and right stock at most $B$ is impossible in a solvable strip. There are 34 such rules, the longest spanning six slashes. [Rule data](../certificates/window-rules.json)

We also use the following table of necessary lower bounds on $p_i$ when $i$ is an inner slash. Its row is $L=H_{i-1}$ and its column is $r=J_{i+1}$.

| $L$ / $r$ | 0 | 1 | 2 | 3 |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 5 | 4 | 2 | 2 |
| 1 | 4 | 3 | 0 | 0 |
| 2 | 2 | 0 | 0 | 0 |
| 3 | 2 | 0 | 0 | 0 |

For a positive entry $z$, try all neighboring masses $a\le L$ and $c\le r$. Test every physical placement on the three slashes with masses $(a,z-1,c)$ and exterior hub stocks $2(L-a)+1$ and $2(r-c)+1$. The recurrences bound the actual exterior stocks by these amounts. An unreachable target in every placement verifies the entry. The checker exhausts the union of these tests and the word rules.

## The finite integer inequality

At the cut before slash $i$ use scalar values $(L,R)=(H_{i-1},J_i)$. After reading $p=p_i$ they become $(l,r)=(H_i,J_{i+1})$, with
$$
l=p+\lfloor L/2\rfloor,\qquad R=p+\lfloor r/2\rfloor .
$$
Store also a set of pairs (rule, prefix length). A pair records that a suffix of slashes read so far matches the corresponding initial part of that rule, with the required left hub bound and componentwise slash bounds. On a new slash start all rules with $L\le A$ and advance every matching prefix satisfying its next slash bound. A completed match excludes the transition when $r\le B$. The table above also excludes transitions. The only reachability assumptions in these checks apply to all solvable placements, including those having an interface across which no move can pass.

Inside the box $0\le L,R\le32$, start from every pair of scalars with empty memory and generate all surviving transitions whose next state is in the box. There are 9,286 states and 249,709 edges. Discard the remembered prefixes on leaving the box and start with empty memory on reentry. This weakens the necessary tests and permits arbitrary scalar values outside the box.

The file of integers $d(x)$ uses the deterministic state order in the verifier and gives zero to unlisted states and states outside the box. The verifier checks $-88\le d(x)\le0$. For every edge from $x$ to $y$ inside the box it checks
$$
d(y)-d(x)\le 8(2p+\lceil L/2\rceil+\lceil r/2\rceil)-36 .
$$
If one of $L,R,l,r$ exceeds 32, the quantity in parentheses is at least 17. This follows immediately for $L$ or $r$ and from the two recurrences for $l$ or $R$. The right side is then at least 100, exceeding the entire range of $d$. Thus the same inequality holds on every crossing of the box boundary and throughout the unbounded region. [Dual certificate](../certificates/window-dual.json)

## Returning to all lengths

Let $F(x)=d(x)+8(L-R)$. Substituting the recurrences rewrites the last inequality as $32p-36\ge F(y)-F(x)$. Apply it to the inner slashes $2,\ldots,n-1$ of an arbitrary solvable placement, initially with empty memory. At the first cut the scalar values are $(p_1,J_2)$ and at the last they are $(H_{n-1},p_n)$. Hence for $n\ge2$,
$$
32|P|\ge36(n-2)-88+24(p_1+p_n)+8(H_{n-1}+J_2)
\ge36n-160 .
$$
At length two the empty sum gives the same inequality. The weak bound $|P|\ge9n/8-5$ also holds at length one.

Concatenate $q$ copies of $P$, reflecting the rows in alternate copies if $n$ is odd. Each target uses its original block alone, so the combined placement is solvable. Apply the weak bound at length $qn$ and divide by $q$. Letting $q$ tend to infinity yields $|P|\ge9n/8$, and integrality gives the stated ceiling. ∎
