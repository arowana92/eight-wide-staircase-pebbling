"""Regenerate the explicit legal-move certificates used by Lean."""
from collections import deque
from pathlib import Path
from upper import BASE


def number(s, r):
    return 4*(s-1) + ((r-1)//2 if s % 2 else (8-r)//2)


def make(n, k, piles):
    tokens = sorted(number(s,r) for s,r,p in piles for _ in range(p))
    init = tuple(tokens)
    moves = {init: None}
    paths = {}
    queue = deque([init])
    while len(paths) < k:
        state = queue.popleft()
        for t in set(state):
            if t >= k or t in paths:
                continue
            v = state
            path = []
            while moves[v] is not None:
                v, edge = moves[v]
                path.append(edge)
            paths[t] = path[::-1]
        for u in set(state):
            if state.count(u) < 2:
                continue
            for v in range(4*n):
                if abs(u//4 - v//4) != 1 or u%4+v%4 not in (3,4):
                    continue
                after = list(state)
                after.remove(u)
                after.remove(u)
                after.append(v)
                succ = tuple(sorted(after))
                if succ not in moves:
                    moves[succ] = state,(u,v)
                    queue.append(succ)
    return tokens,[paths[t] for t in range(k)]


def main():
    output = ['module', '', 'public import Staircase.Paths', '', '@[expose] public section',
              'namespace Staircase.UpperData', '']
    cases = [(n,4*n,BASE[n],f'base{n}') for n in BASE]
    cases.append((5,16,[(1,5,4),(2,2,1),(5,5,4)],'extension'))
    for n,k,piles,name in cases:
        tokens,paths = make(n,k,piles)
        output += [f'def {name} : List Nat := {tokens}', '',
                   f'theorem {name}_reaches (t : Nat) (ht : t < {k}) :',
                   f'    Reaches (Adj {n}) (↑{name}) t := by',
                   f'  apply covers_sound (k := {k}) (paths := [']
        output += [('    '+str(p)+(',' if i+1 < k else '])'))
                   for i,p in enumerate(paths)]
        output += ['  · decide','  · exact ht','']
    output += ['end Staircase.UpperData','']
    path = Path(__file__).resolve().parents[1]/'Staircase'/'UpperData.lean'
    path.write_text('\n'.join(output))


if __name__ == '__main__':
    main()
