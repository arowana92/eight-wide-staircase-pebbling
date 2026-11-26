"""Exact local obstructions and a telescoping lower-bound certificate."""
import argparse
import itertools
import json
from functools import lru_cache
from pathlib import Path

BOUND = 23
SCALE = 80
RATE = 84  # 80*(21/20)
DATA = Path(__file__).resolve().parents[1]/"certificates"/"projection-dual.json"


class Window:
    """Eight-wide staircase with optional hubs at its two ends."""
    def __init__(self, n, left=False, right=False):
        vertices = [(s,r) for s in range(1,n+1) for r in range(1,9) if (s-r)%2 == 0]
        adj = [[j for j,(q,k) in enumerate(vertices) if abs(s-q) == abs(r-k) == 1]
               for s,r in vertices]
        self.size = len(vertices)
        for attach, end in [(left, range(4)), (right, range(self.size-4,self.size))]:
            if attach:
                hub = len(adj)
                adj.append(list(end))
                for j in end:
                    adj[j].append(hub)
        self.full = (1 << self.size)-1

        @lru_cache(maxsize=200000)
        def reachable(stock):
            mask = sum(1 << i for i in range(self.size) if stock[i])
            for u, q in enumerate(stock):
                if q < 2:
                    continue
                for v in adj[u]:
                    next_stock = list(stock)
                    next_stock[u] -= 2
                    next_stock[v] += 1
                    mask |= reachable(tuple(next_stock))
                    if mask == self.full:
                        return mask
            return mask
        self.reachable = reachable

    def solves(self, stock):
        return self.reachable(tuple(stock)) == self.full


def placements(sites, mass):
    for indices in itertools.combinations_with_replacement(range(sites), mass):
        counts = [0]*sites
        for i in indices:
            counts[i] += 1
        yield tuple(counts)


def local_obstructions():
    cases = [((a,2,c), 3-2*a, 3-2*c) for a,c in itertools.product(range(2), repeat=2)]
    cases += [((0,4,0),1,1), ((1,1,1,1,1),2,2)]
    for shape, left, right in cases:
        board = Window(len(shape), True, True)
        tested = 0
        for columns in itertools.product(*(placements(4,p) for p in shape)):
            stock = tuple(itertools.chain.from_iterable(columns))+(left,right)
            if board.solves(stock):
                raise ValueError(f"invalid local obstruction {shape}, {stock}")
            tested += 1
        print(f"ruled out {tested} placements on {shape} with end hubs {left},{right}")


def transitions():
    for left in range(BOUND+1):
        for right_after in range(BOUND+1):
            for p in range(BOUND-max(left//2,right_after//2)+1):
                left_after = p + left//2
                right = p + right_after//2
                if p + left//2 + right_after//2 < 2:
                    continue
                if p == 2 and max(left,right_after) <= 1:
                    continue
                if p == 4 and left == right_after == 0:
                    continue
                for run in range(6):
                    run_after = min(5,run+1) if p == 1 and (run or left <= 2) else 0
                    if run_after == 5 and right_after <= 2:
                        continue
                    yield (left,right,run), (left_after,right_after,run_after), p


def build_certificate():
    edges = list(transitions())
    d = {}
    for _ in range(100):
        changed = False
        for x,y,p in edges:
            reweighted = 20*(2*p+(x[0]+1)//2+(y[1]+1)//2)
            z = d.get(x,0) + reweighted - RATE
            if z < d.get(y,0):
                d[y] = z
                changed = True
        if not changed:
            DATA.write_text(json.dumps([list(k)+[v] for k,v in sorted(d.items())],
                                       separators=(",",":"))+"\n")
            return
    raise RuntimeError("potential search did not stabilize")


def read_certificate():
    d = {(left,right,run): v for left,right,run,v in json.loads(DATA.read_text())}
    if any(not (0 <= L <= BOUND and 0 <= R <= BOUND and 0 <= k <= 5 and -132 <= v <= 0)
           for (L,R,k),v in d.items()):
        raise ValueError("potential out of bounds")

    def potential(L,R,k):
        return d.get((L,R,k),0) + 20*(L-R)

    tested = 0
    for x,y,p in transitions():
        if SCALE*p-RATE < potential(*y)-potential(*x):
            raise ValueError(f"invalid dual inequality at {x}, {y}")
        tested += 1
    print(f"verified {tested} transitions inside 0..{BOUND}")
    # An edge outside the box has reweighted cost at least 80*3.
    if 80*3-RATE < 132:
        raise ValueError("outside-box inequality failed")
    return potential


def check_end(length, side, transfer_potential):
    board = Window(length, right=True)
    # Thresholds in units of 1/80. The right run state is arbitrary.
    threshold = 32 if side == "left" else -32
    # H <= S. For either end the scaled contribution is at least
    # 60*S + 20*K - 84*length + (0 on the left, -132 on the right).
    limit = threshold + RATE*length + (132 if side == "right" else 0)
    tested = 0
    for mass in range(limit//60+1):
        for stock in placements(board.size, mass):
            h = 0
            for i in range(0,board.size,4):
                h = sum(stock[i:i+4]) + h//2
            for bank in range((limit-60*mass)//20+1):
                if side == "left":
                    correction = -transfer_potential(h,bank,0)
                else:
                    correction = min(transfer_potential(bank,h,k) for k in range(6))
                value = SCALE*mass - RATE*length + correction
                if value < threshold:
                    tested += 1
                    if board.solves(stock+(bank,)):
                        raise ValueError(f"invalid {side} end bound {stock}, {bank}")
    print(f"verified {side} end bound {threshold}/80 with {tested} exclusions")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true")
    if parser.parse_args().regenerate:
        build_certificate()
    local_obstructions()
    potential = read_certificate()
    check_end(2,"left",potential)
    check_end(4,"right",potential)
    for n in range(1,6):
        board = Window(n)
        if any(board.solves(p) for p in placements(4*n,n)):
            raise ValueError(f"small case failed at {n}")
    print("verified the 21n/20 lower bound, including lengths 1..5")


if __name__ == "__main__":
    main()
