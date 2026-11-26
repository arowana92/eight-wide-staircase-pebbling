"""Create or replay a certificate in the original square-grid coordinates."""
import argparse
import json
from collections import deque
from pathlib import Path


def vertices(length):
    # x=(slash+row)/2 and y=(row-slash)/2.
    return sorted((x, y) for x in range(1, length+9)
                  for y in range(-length, 9)
                  if 1 <= x-y <= length and 1 <= x+y <= 8)


def neighbors(v):
    x, y = v
    return [(x-1,y), (x+1,y), (x,y-1), (x,y+1)]


def generate(length, placement):
    board = vertices(length)
    index = {v: i for i, v in enumerate(board)}
    initial = [0]*len(board)
    for slash, row, count in placement:
        if (slash-row)%2 or count < 1:
            raise ValueError("invalid placement")
        initial[index[(slash+row)//2, (row-slash)//2]] += count
    initial = tuple(initial)
    parent = {initial: None}
    queue = deque([initial])
    paths = {}
    while queue and len(paths) < len(board):
        state = queue.popleft()
        for i, count in enumerate(state):
            if count and i not in paths:
                path = []
                step = state
                while parent[step] is not None:
                    step, move = parent[step]
                    path.append(move)
                paths[i] = path[::-1]
        for i, count in enumerate(state):
            if count < 2:
                continue
            for v in neighbors(board[i]):
                if v not in index:
                    continue
                next_state = list(state)
                next_state[i] -= 2
                next_state[index[v]] += 1
                key = tuple(next_state)
                if key not in parent:
                    parent[key] = state, [i, index[v]]
                    queue.append(key)
    if len(paths) != len(board):
        raise ValueError("placement cannot reach every vertex")
    return dict(length=length, vertices=[list(v) for v in board], initial=list(initial),
                paths=[paths[i] for i in range(len(board))])


def replay(cert):
    board = vertices(cert["length"])
    if [list(v) for v in board] != cert["vertices"]:
        raise ValueError("vertex list differs from the induced square grid")
    initial = cert["initial"]
    if (len(initial) != len(board) or len(cert["paths"]) != len(board)
            or any(type(p) is not int or p < 0 for p in initial)):
        raise ValueError("invalid initial distribution or target list")
    for target, path in enumerate(cert["paths"]):
        pebbles = initial.copy()
        for u, v in path:
            if not (type(u) is int and type(v) is int and
                    0 <= u < len(board) and 0 <= v < len(board) and
                    board[v] in neighbors(board[u]) and pebbles[u] >= 2):
                raise ValueError(f"illegal move for target {target}")
            pebbles[u] -= 2
            pebbles[v] += 1
        if pebbles[target] < 1:
            raise ValueError(f"target {target} missed")
    print(f"S(8,{cert['length']}): {sum(initial)} pebbles reach all {len(board)} targets")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--generate", type=int, metavar="LENGTH")
    parser.add_argument("--placement", type=json.loads, help="JSON triples [slash,row,count]")
    args = parser.parse_args()
    if args.generate:
        cert = generate(args.generate, args.placement)
        args.certificate.write_text(json.dumps(cert, separators=(",", ":"))+"\n")
    replay(json.loads(args.certificate.read_text()))
