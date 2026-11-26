"""Construct a solvable width-eight placement and check its finite building blocks."""
import argparse
import json

from projection import Window
from witness import generate, replay

# Triples give the slash, row, and number of pebbles.
BASE = {
    1: [(1,1,1), (1,3,1), (1,5,1), (1,7,1)],
    2: [(1,1,2), (1,7,2), (2,4,2)],
    3: [(1,3,1), (1,5,4), (1,7,1), (2,2,1)],
    4: [(1,1,2), (1,5,4), (2,2,1), (3,7,1)],
    5: [(1,5,4), (2,2,1), (5,1,1), (5,5,4)],
    6: [(1,1,1), (1,5,4), (1,7,1), (3,3,1), (5,3,2), (5,7,2)],
}


def construction(n):
    if n < 1:
        raise ValueError("the length must be positive")
    copies = max(0, (n-3)//4)
    pebbles = []
    for j in range(copies):
        pebbles.extend([(4*j+1,5,4), (4*j+2,2,1)])
    pebbles.extend((s+4*copies,r,p) for s,r,p in BASE[n-4*copies])
    return pebbles


def check():
    for n in BASE:
        placement = construction(n)
        if sum(p for _,_,p in placement) > (5*n+3)//4+3:
            raise ValueError("base exceeds the claimed bound")
        if n >= 3 and (1,5,4) not in placement:
            raise ValueError("missing four-pebble pile for extension")
        cert = generate(n, placement)
        replay(cert)

    # Entries are in slash order, then row order. The fifth slash contains
    # the four pebbles supplied by the old block, translated by four.
    stock = (0,0,4,0, 1,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,4,0)
    reached = Window(5).reachable(stock)
    first_four = (1 << 16)-1
    if reached & first_four != first_four:
        raise ValueError("a new target is unreachable")
    print("four-slash extension reaches all 16 new targets")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--length", type=int, help="print a placement as [slash,row,count] triples")
    args = parser.parse_args()
    if args.length is None:
        check()
    else:
        print(json.dumps(construction(args.length)))
