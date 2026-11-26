"""Replay the finite certificate for Conjecture 3.2 of Győri et al."""
import argparse
from itertools import chain, product
from pathlib import Path

from projection import Window, placements

CERT = Path(__file__).resolve().parents[1]/"certificates"
BOX = 36


def read_rules():
    rules = []
    for line in (CERT/"five-fourths-windows.txt").read_text().splitlines():
        a, *word, b = map(int, line.split())
        if not word or min(a,b,*word) < 0:
            raise ValueError("invalid window")
        rules.append((a,tuple(word),b))
    return rules


def physical_check(rules):
    total = 0
    for length in sorted({len(word) for _,word,_ in rules}):
        board = Window(length, left=True, right=True)
        checked = 0
        for left,word,right in rules:
            if len(word) != length:
                continue
            for columns in product(*(placements(4,p) for p in word)):
                stock = tuple(chain.from_iterable(columns))+(left,right)
                if board.solves(stock):
                    raise ValueError(f"solvable obstruction {left}, {word}, {right}: {stock}")
                checked += 1
        total += checked
        print(f"length {length}: {checked} placements excluded", flush=True)
    return total


class Matcher:
    """One bit per position in a forbidden word. Memory identifies the next positions."""
    def __init__(self, rules):
        self.starts = [0]*(BOX+1)
        self.letters = [0]*(BOX+1)
        self.ends = [0]*(BOX+1)
        self.last = 0
        position = 0
        for a,word,b in rules:
            for left in range(min(a,BOX)+1):
                self.starts[left] |= 1 << position
            for maximum in word:
                for p in range(min(maximum,BOX)+1):
                    self.letters[p] |= 1 << position
                position += 1
            final = 1 << (position-1)
            self.last |= final
            for right in range(min(b,BOX)+1):
                self.ends[right] |= final

    def advance(self, memory, left, p):
        matched = (memory | self.starts[left]) & self.letters[p]
        return matched, (matched & ~self.last) << 1


def transfer_graph(matcher):
    states = [(L,R,0) for L in range(BOX+1) for R in range(BOX+1)]
    ids = {state:i for i,state in enumerate(states)}
    edges = []
    for i,(L,R,memory) in enumerate(states):
        for p in range(R+1):
            l = p+L//2
            if l > BOX:
                continue
            matched,after = matcher.advance(memory,L,p)
            for r in (2*(R-p),2*(R-p)+1):
                if r > BOX or matched & matcher.ends[r]:
                    continue
                y = l,r,after
                if y not in ids:
                    ids[y] = len(states)
                    states.append(y)
                cost = 4*(2*p+(L+1)//2+(r+1)//2)-20
                edges.append((i,ids[y],cost))
    return states,ids,edges


def dual_check(rules, regenerate):
    matcher = Matcher(rules)
    states,ids,edges = transfer_graph(matcher)
    path = CERT/"five-fourths-dual.txt"
    if regenerate:
        d = [0]*len(states)
        for _ in range(len(states)):
            changed = False
            for i,j,cost in edges:
                if d[i]+cost < d[j]:
                    d[j] = d[i]+cost
                    changed = True
            if not changed:
                break
        else:
            raise ValueError("negative cycle")
        path.write_text("".join(f"{i} {z}\n" for i,z in enumerate(d) if z))

    d = [0]*len(states)
    for line in path.read_text().splitlines():
        i,z = map(int,line.split())
        if not 0 <= i < len(states) or d[i] or not -56 <= z < 0:
            raise ValueError("invalid sparse potential")
        d[i] = z
    for i,j,cost in edges:
        if d[j]-d[i] > cost:
            raise ValueError(f"failed dual inequality on edge {i} -> {j}")
    if 4*((BOX+2)//2)-20 < max(d)-min(d):
        raise ValueError("potential range fails at the box boundary")

    # A period-four word at density 5/4 gives a tight cycle.
    example = [(0,4,4,1),(4,1,1,1),(3,1,0,2),(1,2,0,4)]  # L,R,p,r
    memory = 0
    for repetition in range(5):
        previous = memory
        for L,R,p,r in example:
            matched,after = matcher.advance(memory,L,p)
            if matched & matcher.ends[r]:
                raise ValueError("the period-four construction was rejected")
            i,j = ids[L,R,memory],ids[p+L//2,r,after]
            cost = 16*p-20-4*((p+L//2-r)-(L-R))
            if repetition == 4 and d[j]-d[i] != cost:
                raise ValueError("positive control is not a tight cycle")
            memory = after
        if repetition == 4 and memory != previous:
            raise ValueError("positive control did not close")
    print(f"{len(states)} states, {len(edges)} inequalities, potential range {min(d)}..{max(d)}")
    print("period-four tight cycle verified")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regenerate", action="store_true", help="recompute the sparse integer dual")
    parser.add_argument("--part", choices=("all","windows","dual"), default="all")
    args = parser.parse_args()
    rules = read_rules()
    if args.part != "dual":
        total = physical_check(rules)
        print(f"{len(rules)} windows, {total} placements")
    if args.part != "windows":
        dual_check(rules,args.regenerate)


if __name__ == "__main__":
    main()
