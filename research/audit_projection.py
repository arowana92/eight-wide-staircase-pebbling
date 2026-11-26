"""Independent replay of the lower-bound certificate via pebble ancestry trees."""
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations_with_replacement, product
import json
from pathlib import Path


def ancestry_solver(n, hubs):
    # Build the board from the square grid in (x,y), independently of slash edges.
    v = sorted(((x,y) for x in range(1,n+9) for y in range(-n,9)
                if 1 <= x-y <= n and 1 <= x+y <= 8), key=lambda u: (u[0]-u[1], sum(u)))
    edges = [{j for j,(a,b) in enumerate(v) if abs(x-a)+abs(y-b) == 1} for x,y in v]
    for slash in hubs:
        near = {j for j,(x,y) in enumerate(v) if x-y == slash}
        for j in near:
            edges[j].add(len(edges))
        edges.append(near)
    weights = []
    unit = 1 << len(edges)
    for t in range(len(v)):
        dist = {t: 0}
        q = deque([t])
        while q:
            u = q.popleft()
            for z in edges[u]-dist.keys():
                dist[z] = dist[u]+1
                q.append(z)
        weights.append([unit >> dist[u] if u in dist else 0 for u in range(len(edges))])

    @lru_cache(None)
    def neighbors(mask):
        return sum(1 << z for z,nb in enumerate(edges) if any(mask & (1 << j) for j in nb))

    @lru_cache(maxsize=300000)
    def roots(tokens):
        if not tokens:
            return 0
        if len(tokens) == 1:
            return 1 << tokens[0]
        counts = Counter(tokens)
        choices = [[(u,)*j for j in range(c+1)] for u,c in counts.items()]
        mask = 0
        for split in product(*choices):
            a = sum(split, ())
            if not a or len(a) > len(tokens)//2:
                continue
            b = tuple(u for part,(u,count) in zip(split,counts.items())
                      for _ in range(count-len(part)))
            ra, rb = roots(a), roots(b)
            mask |= ra | rb | neighbors(ra & rb)
        return mask

    def solves(tokens):
        if any(sum(row[u] for u in tokens) < unit for row in weights):
            return False
        return roots(tokens) & ((1 << len(v))-1) == (1 << len(v))-1
    return solves


def verify():
    data = Path(__file__).resolve().parents[1]/"certificates"/"projection-dual.json"
    table = {tuple(row[:3]):row[3] for row in json.loads(data.read_text())}
    assert min(table.values()) >= -132 and max(table.values()) <= 0
    def f(L,R,k):
        return table.get((L,R,k),0)+20*(L-R)

    # Recover the same physical slash from its two adjacent interface states.
    checked = 0
    for L,R,l,r in product(range(24),repeat=4):
        p = l-L//2
        if p < 0 or R-r//2 != p or p+L//2+r//2 < 2:
            continue
        if p == 2 and L < 2 and r < 2 or p == 4 and not (L or r):
            continue
        for k in range(6):
            j = min(k+1,5) if p==1 and (L <= 2 or k>0) else 0
            if j < 5 or r > 2:
                assert 80*p-84 >= f(l,r,j)-f(L,R,k)
                checked += 1
    assert checked == 56810

    failures = 0
    def exclude(solves,tokens):
        nonlocal failures
        if solves(tokens):
            raise ValueError(f"counterexample in certificate audit {tokens}")
        failures += 1

    for n in range(1,6):
        solves = ancestry_solver(n, [])
        for tokens in combinations_with_replacement(range(4*n),n):
            exclude(solves,tokens)

    for shape,left,right in [((0,2,0),3,3),((1,2,0),1,3),((0,2,1),3,1),
                             ((1,2,1),1,1),((0,4,0),1,1),((1,1,1,1,1),2,2)]:
        n = len(shape)
        solves = ancestry_solver(n, [1,n])
        pools = [combinations_with_replacement(range(4*i,4*i+4),p)
                 for i,p in enumerate(shape)]
        for parts in product(*pools):
            exclude(solves,sum(parts,())+(4*n,)*left+(4*n+1,)*right)

    for n in (2,4):
        solves = ancestry_solver(n, [n])
        for s in range(8):
            for tokens in combinations_with_replacement(range(4*n),s):
                # H_n = floor(sum p_i / 2^(n-i)), evaluated without the recurrence.
                h = sum(1 << (u//4) for u in tokens) >> (n-1)
                for bank in range(22):
                    if n==2:
                        bad = 80*s-168-f(h,bank,0) < 32
                    else:
                        bad = 80*s-336+min(f(bank,h,k) for k in range(6)) < -32
                    if bad:
                        exclude(solves,tokens+(4*n,)*bank)
    print(f"ancestry-tree audit passed: {failures} window placements, {checked} transitions")


if __name__ == "__main__":
    verify()
