"""Replay the infinite-strip sieve and its remaining finite obstructions."""
import argparse
import json
import subprocess
from collections import deque
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


def distances(root, adj, allowed):
    dist = {root: 0}
    queue = deque([root])
    while queue:
        u = queue.popleft()
        for v in adj[u]:
            if v in allowed and v not in dist:
                dist[v] = dist[u]+1
                queue.append(v)
    return dist


def target_reachable(stock, adj, target):
    """Exact balances on a finite graph, expanding unmet demands backwards."""
    if stock[target]:
        return True
    senders = set(stock)
    scale = len(stock)
    while True:
        remaining = set()
        for u in senders:
            dist = distances(u, adj, senders)
            value = sum(stock[v] << (scale-d) for v, d in dist.items())
            if value >= 2 << scale:
                remaining.add(u)
        if remaining == senders:
            break
        senders = remaining

    allowed = senders | {target}
    vertices = sorted(distances(target, adj, allowed))
    index = {v: i for i, v in enumerate(vertices)}
    size = len(vertices)
    weights = []
    parents = []
    for u in vertices:
        dist = distances(u, adj, allowed)
        weights.append([1 << (size-dist[v]) for v in vertices])
        parents.append([index[v] for v in adj[u] if v in index and v != target])
    costs = {(u,v): tuple(2*row[u]-row[v] for row in weights)
             for v in range(size) for u in parents[v]}
    initial = tuple(stock[u]-int(u == target) for u in vertices)

    @lru_cache(None)
    def possible(balance):
        deficits = [i for i, q in enumerate(balance) if q < 0]
        if sum(balance) < 0:
            return False
        if not deficits:
            return True
        value = [sum(x*y for x,y in zip(row,balance)) for row in weights]
        if min(value) < 0:
            return False
        v = min(deficits, key=lambda z: (value[z],balance[z]))
        for u in parents[v]:
            if any(w < c for w,c in zip(value,costs[u,v])):
                continue
            updated = list(balance)
            updated[v] += 1
            updated[u] -= 2
            if possible(tuple(updated)):
                return True
        return False

    return possible(initial)


def check_window(period, placement, target):
    motif = {(s,r): q for s,r,q in placement}

    def count(s, r):
        turns, k = divmod(s-1, period)
        return motif.get((k+1, 9-r if turns*period%2 else r), 0)

    def cut_bank(j):
        # The slash totals repeat after one period even for a glide.
        block = sum(Fraction(sum(count(s,r) for s in (j-h,j+h+1) for r in range(1,9)),
                             2**h) for h in range(period))
        return int(block/(1-Fraction(1,2**period)))

    left, right = 1-7, period+7
    left_bonus, right_bonus = cut_bank(left-1), cut_bank(right)
    stock = {(s,r): count(s,r) + (s==left)*left_bonus + (s==right)*right_bonus
             for s in range(left,right+1) for r in range(1,9) if (s-r)%2 == 0}
    adj = {(s,r): [(s+a,r+b) for a in (-1,1) for b in (-1,1) if (s+a,r+b) in stock]
           for s,r in stock}
    if target_reachable(stock, adj, target):
        raise ValueError(f"failed obstruction for period {period}, target {target}")


def sieve(binary, period, budget=None):
    args = [str(binary), str(period)]
    if budget is not None:
        args.append(str(budget))
    result = subprocess.run(args, check=True, stdout=subprocess.PIPE, text=True)
    return {tuple(tuple(map(int, entry.split(","))) for entry in line.split())
            for line in result.stdout.splitlines()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sieve", type=Path)
    args = parser.parse_args()
    binary = args.sieve.resolve()
    data = Path(__file__).resolve().parents[1]/"certificates"/"periodic-obstructions.json"
    cases = json.loads(data.read_text())
    if ((1,5,4),(2,2,1)) not in sieve(binary, 4, 5):
        raise ValueError("the published-density positive control failed")
    for p in range(1,9):
        targets = {tuple(map(tuple,c["placement"])): tuple(c["target"])
                   for c in cases if c["period"] == p}
        if sieve(binary,p) != set(targets):
            raise ValueError(f"unaccounted or unmatched patterns for period {p}")
        for placement, target in targets.items():
            check_window(p, placement, target)
        print(f"period {p}: excluded every motif below 5/4, {len(targets)} window checks",
              flush=True)


if __name__ == "__main__":
    main()
