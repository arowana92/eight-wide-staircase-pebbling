# Uniform bounds for the width-eight strip

**Work in progress.** Write $a_n=\pi_{\rm opt}(S_{8,n})$. Use slash and row coordinates $s=x-y,r=x+y$. The vertices have $1\le s\le n$, $1\le r\le 8$, and $s\equiv r\pmod2$. A move changes each coordinate by one in absolute value. Each slash has four vertices.

## Published bounds and construction

Folding row 8 onto row 6 while fixing all other vertices maps every edge to an edge of the seven-wide strip on rows 1 through 7. Project all pebbles and moves. A solvable distribution projects to a solvable one of the same size, so the width-seven theorem gives $a_n\ge n+1$ for $n\ge8$. In the other direction, use the solvable seven-wide distribution of size at most $n+3$. Put one further pebble on alternate vertices of row 7, adding the last vertex if necessary. Every vertex in row 8 has a marked neighbor. A pebble can reach each marked neighbor using the original distribution, whereupon the extra pebble permits one more move. The added cost is at most $\lceil n/4\rceil+1$. Thus $a_n\le n+4+\lceil n/4\rceil$ for $n\ge8$. These arguments use Theorem 2.14 and Claim 3.1. [Győri–Katona–Papp–Tompkins](https://arxiv.org/abs/1611.09686)

## A sharp reformulation of the missing lower bound

For positive $m,n$, partition the slashes of $S_{8,m+n}$ into intervals of lengths $m,n$. Translate slash indices on the second interval, also reflecting $r\mapsto9-r$ when $m$ is odd to preserve parity. Both induced blocks are copies of the canonical strips. A separately solvable placement on each block solves the union, using only moves within the target's block. Hence $a_{m+n}\le a_m+a_n$.

In particular, for any $k\ge1$, a placement of size $b<5k/4$ would imply
$$
5qk/4-a_{qk}\ge q(5k/4-b)
$$
for every positive $q$. Conversely, $a_k\ge\lceil5k/4\rceil$ for every $k$ gives the conjecture with the published upper bound. Thus even one strict finite saving would refute the conjecture, and a uniform additive lower bound implies the pointwise bound with zero lower-side constant. Fekete's lemma gives $\lambda=\lim a_n/n=\inf a_n/n$. Here a proof that $\lambda=5/4$ would also establish the required additive estimate, by subadditivity and the independent upper bound.

## Localizing an arbitrary solvable distribution

The following estimate gives a certified approximation to the unknown slope from finite optima.
$$
\frac{a_n}{n+32}\le\lambda\le\frac{a_n}{n},\qquad n\ge1.
$$

**Proof.** Tile the doubly infinite strip by copies of a solvable $k$-slash block of size $a_k$, reflecting alternate blocks in the rows when needed. This gives a periodic initial placement $P$ of mean mass $\mu=a_k/k$ per slash. Each target has a finite solution using only its own block.

For the interface between slashes $j,j+1$, define
$$
B_j=\sum_{s\in\mathbb Z}2^{-\mathrm{dist}(s,\{j,j+1\})}p_s
$$
where $p_s$ is the number of initial pebbles on slash $s$. The sum converges. A move across this interface decreases its potential by one. Every other move has nonpositive effect since the receiving weight is at most twice the sending weight. Consequently every finite move sequence crosses this interface at most $\lfloor B_j\rfloor$ times, counting both directions.

Keep an $n$-slash interval and its original pebbles. At each of its four vertices on the left boundary, add $\lfloor B_{\rm left}\rfloor$ pebbles. Use the corresponding right allowance at the other end, adding both allowances if $n=1$. For each target take its full-strip solution and replay only the moves internal to the interval. At each boundary vertex the added stock covers every omitted incoming move throughout the sequence. Omitting an outgoing move leaves two extra pebbles available. Prefix by prefix, each retained move is legal and the target is reached.

Average the resulting size over all starting slashes in one period. The original window has mean size $n\mu$. The coefficients in $B_j$ sum to $2+2\sum_{h\ge1}2^{-h}=4$, so each of the two interfaces has mean potential $4\mu$. The four boundary vertices at each end give total mean repair cost at most $32\mu$. Some window therefore proves $a_n\le(n+32)a_k/k$. Take the infimum over $k$. The other inequality is subadditivity. ∎

This supplies an absolute additive error about the *unknown* slope, $0\le a_n-\lambda n\le32\lambda\le40$. Identifying that slope, or finding a strict finite saving, remains open in this work.
