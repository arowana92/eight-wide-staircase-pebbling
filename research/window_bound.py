"""Check the unrestricted 9n/8 lower bound using local windows and an integer dual."""
import argparse
import json
from functools import lru_cache
from itertools import chain, product
from pathlib import Path

from projection import Window, placements

ROOT = Path(__file__).resolve().parents[1]/"certificates"
BOX = 32
CENTRE = ((5,4,2,2), (4,3,0,0), (2,0,0,0), (2,0,0,0))


def window_tests(rules):
    for L,R in product(range(4), repeat=2):
        lower = CENTRE[L][R]
        if lower:
            for a,c in product(range(L+1),range(R+1)):
                yield 2*(L-a)+1, (a,lower-1,c), 2*(R-c)+1
    yield from rules


def verify_windows(rules, ancestry):
    checked = 0
    for n in range(1,1+max(max(len(w) for _,w,_ in rules),3)):
        if ancestry:
            from audit_projection import ancestry_solver
            solves = ancestry_solver(n,[1,n])
        else:
            board = Window(n,True,True)
        for L,word,R in sorted(set(window_tests(rules))):
            if len(word) != n:
                continue
            for cols in product(*(placements(4,p) for p in word)):
                stock = tuple(chain.from_iterable(cols))+(L,R)
                if ancestry:
                    tokens = tuple(i for i,c in enumerate(stock) for _ in range(c))
                    feasible = solves(tokens)
                else:
                    feasible = board.solves(stock)
                if feasible:
                    raise ValueError(f"invalid obstruction {L}, {word}, {R}: {stock}")
                checked += 1
    print(f"verified {checked} physical placements")


def graph(rules):
    @lru_cache(None)
    def extend(matches, left, p):
        # Each entry (rule, j) has already matched the first j slash caps.
        partial = list(matches) + [(i,0) for i,(a,w,b) in enumerate(rules) if left <= a]
        after = []
        forbidden_right = -1
        for i,j in partial:
            _,word,bank = rules[i]
            if p <= word[j]:
                if j+1 == len(word):
                    forbidden_right = max(forbidden_right,bank)
                else:
                    after.append((i,j+1))
        return tuple(sorted(after)),forbidden_right

    # Every entrance into the box may start with empty match memory.
    states = [(L,R,()) for L in range(BOX+1) for R in range(BOX+1)]
    ids = {x:i for i,x in enumerate(states)}
    edges = []
    for i,(L,R,matches) in enumerate(states):
        for p in range(R+1):
            l = p+L//2
            if l > BOX:
                continue
            after,forbidden = extend(matches,L,p)
            for r in (2*(R-p),2*(R-p)+1):
                if r > BOX or r <= forbidden:
                    continue
                if max(L,r) <= 3 and p < CENTRE[L][r]:
                    continue
                y = l,r,after
                if y not in ids:
                    ids[y] = len(states)
                    states.append(y)
                cost = 8*(2*p+(L+1)//2+(r+1)//2)-36
                edges.append((i,ids[y],cost))
    return states,edges


def verify_dual(rules, generate):
    states,edges = graph(rules)
    path = ROOT/"window-dual.json"
    if generate:
        d = [0]*len(states)
        for _ in range(len(states)):
            changed = False
            for x,y,cost in edges:
                if d[x]+cost < d[y]:
                    d[y] = d[x]+cost
                    changed = True
            if not changed:
                break
        else:
            raise ValueError("negative cycle in the relaxation")
        path.write_text(json.dumps([(i,t) for i,t in enumerate(d) if t],
                                   separators=(",",":"))+"\n")
    d = [0]*len(states)
    for i,t in json.loads(path.read_text()):
        d[i] = t
    if min(d) < -88 or max(d) > 0:
        raise ValueError("potential range exceeds the certificate")
    for x,y,cost in edges:
        if d[y]-d[x] > cost:
            raise ValueError(f"dual fails at {states[x]}, {states[y]}")
    # Outside: some interface value >=33, so local reweighted cost >=8*17-36.
    if 8*((BOX+2)//2)-36 < 88:
        raise ValueError("unbounded interface inequality failed")
    print(f"verified {len(edges)} dual inequalities on {len(states)} states")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate",action="store_true")
    parser.add_argument("--ancestry",action="store_true",help="use disjoint token trees for windows")
    args = parser.parse_args()
    rules = [(a,tuple(w),b) for a,w,b in json.loads((ROOT/"window-rules.json").read_text())]
    verify_windows(rules,args.ancestry)
    verify_dual(rules,args.regenerate)
    print("verified the unrestricted 9n/8 lower bound")


if __name__ == "__main__":
    main()
