"""Produce untrusted finite ancestry and placement certificates for the Lean checker."""
import argparse
from collections import defaultdict
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = 64
LANE = 6


def encode(values):
    return sum(x << (LANE*i) for i,x in enumerate(values))


def packed(values):
    bits = max(1, max(values, default=0).bit_length())
    limbs = [sum(x << (bits*j) for j,x in enumerate(values[i:i+32]))
             for i in range(0,len(values),32)]
    def tree(xs):
        if len(xs)<=1:
            return f'(.leaf {hex(xs[0]) if xs else "0"})'
        return '(.fork '+tree(xs[::2])+' '+tree(xs[1::2])+')'
    return f'⟨{len(values)},{bits},'+tree(limbs)+'⟩'


class Window:
    def __init__(self, line):
        self.left,*word,self.right = line
        self.word = word
        self.caps = [self.left,self.right]+word
        self.groups = [[0],[1]]+[[2+4*s+j for j in range(4)] for s in range(len(word))]
        self.size = 2+4*len(word)
        self.owner = [0,1]+[2+s for s in range(len(word)) for _ in range(4)]
        self.adj = [[] for _ in range(self.size)]
        for u in range(2,self.size):
            for v in range(2,u):
                if (u-2)//4 == (v-2)//4+1 and (u-2)%4+(v-2)%4 in (3,4):
                    self.join(u,v)
            if u<6:
                self.join(0,u)
            if u>=self.size-4:
                self.join(1,u)
        self.groups_bits = LANE*len(self.caps)
        self.cap = encode(self.caps)
        self.group_guard = encode([32]*len(self.caps))
        self.all_guard = encode([32]*(len(self.caps)+self.size))
        self.site_guard = encode([32]*self.size)

    def join(self,u,v):
        self.adj[u].append(v)
        self.adj[v].append(u)

    def fits_caps(self,total):
        g=self.group_guard
        return ((g+self.cap-total)&g)==g

    def origins(self):
        """Minimal realizable resource vectors, by total number of leaves."""
        roots=[[] for _ in self.adj]
        layers=[[] for _ in self.adj]
        for u,g in enumerate(self.owner):
            leaf=(1<<(LANE*g))+(1<<(self.groups_bits+LANE*u))
            layers[u].append([leaf] if self.caps[g] else [])
            roots[u].extend(layers[u][0])
        guard=self.all_guard
        for k in range(2,sum(self.caps)+1):
            candidates=[set() for _ in self.adj]
            for u,neighbors in enumerate(self.adj):
                for i in range(1,k//2+1):
                    for x in layers[u][i-1]:
                        for y in layers[u][k-i-1]:
                            if i==k-i and x>y:
                                continue
                            total=x+y
                            if self.fits_caps(total):
                                for v in neighbors:
                                    candidates[v].add(total)
            for v,possible in enumerate(candidates):
                new=[z for z in sorted(possible)
                     if not any(((guard+z-x)&guard)==guard for x in roots[v])]
                layers[v].append(new)
                roots[v].extend(new)
        return roots


def certificate(window, roots):
    n=window.size
    bits=window.groups_bits
    mask=(1<<bits)-1
    profiles=[]
    lookup=[]
    for values in roots:
        by_group=defaultdict(list)
        for value in values:
            by_group[value&mask].append(value>>bits)
        groups=sorted(by_group.items())
        profiles.append(groups)
        ids={(site<<bits)+group:1024*i+k for i,(group,sites) in enumerate(groups)
             for k,site in enumerate(sites)}
        assert all(len(sites)<=1024 for _,sites in groups)
        lookup.append(ids)
    tips=[]
    nodes=[]
    guard=window.all_guard

    @lru_cache(None)
    def witness(v,budget):
        for term in roots[v]:
            if ((guard+budget-term)&guard)==guard:
                return lookup[v][term]
        raise ValueError('failed ancestry closure')

    for u,groups in enumerate(profiles):
        offsets=[]
        for first,xs in groups:
            for second,ys in groups:
                g=first+second
                if not window.fits_caps(g):
                    offsets.append(0)
                    continue
                offsets.append(len(tips))
                for x in xs:
                    for y in ys:
                        budget=((x+y)<<bits)+g
                        tips.extend(witness(v,budget) for v in window.adj[u])
        leaf=(1<<(LANE*window.owner[u]))+(1<<(bits+LANE*u))
        seed=lookup[u].get(leaf,0)
        ps=','.join(f'⟨{hex(g)},{packed(sites)}⟩' for g,sites in groups)
        ns=','.join(map(str,window.adj[u]))
        nodes.append(f'⟨#[{ns}],#[{ps}],{packed(offsets)},{seed}⟩')
    return f'⟨{len(window.word)},{hex(window.cap)},#[\n'+',\n'.join(nodes)+f'],{packed(tips)}⟩'


def boxes(window, roots):
    """Refine slot bounds until one target has no compatible origin."""
    caps,groups=window.caps,window.groups
    forms=[[z>>window.groups_bits for z in row] for row in roots]
    guard=window.site_guard

    def visit(upper,lower):
        allowance=encode(upper)
        live=[[z for z in row if ((guard+allowance-z)&guard)==guard] for row in forms[2:]]
        empty=[i+2 for i,values in enumerate(live) if not values]
        if empty:
            target=min(empty,key=lambda t:len(forms[t]))
            return f'(.miss {target} {hex(allowance)})'
        best=None
        for c,us in zip(caps[2:],groups[2:]):
            if sum(upper[u] for u in us)<=c:
                continue
            for u in us:
                for threshold in range(lower[u]+1,upper[u]+1):
                    left=upper.copy()
                    left[u]=threshold-1
                    new_lower=lower.copy()
                    new_lower[u]=threshold
                    right=upper.copy()
                    for v in us:
                        right[v]=min(right[v],c-sum(new_lower[j] for j in us if j!=v))
                    if any(new_lower[v]>right[v] for v in us):
                        continue
                    score=[]
                    for child in (left,right):
                        limit=encode(child)
                        score.append(min(sum(((guard+limit-z)&guard)==guard for z in terms)/len(terms)
                                         for terms in live))
                    key=(max(score),sum(score),sum(left)+sum(right),u,threshold)
                    if best is None or key<best[0]:
                        best=key,left,right,new_lower
        if best is None:
            raise ValueError('a solvable window survived')
        key,left,right,lo=best
        return f'(.cut {key[-2]} {key[-1]} '+visit(left,lower)+' '+visit(right,lo)+')'
    return visit([caps[g] for g in window.owner],[0]*window.size)


def render(i,line):
    w=Window(line)
    roots=w.origins()
    orig=certificate(w,roots)
    splits=boxes(w,roots)
    dependency = 'Staircase.WindowCheck' if i<4 else f'Staircase.WindowData.R{i-4:03d}'
    header = (f'module\n\npublic import {dependency}\n\n@[expose] public section\n'
              f'namespace Staircase.WindowData.R{i:03d}\n\n'
              f'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
              f'def rule : Rule := ⟨⟨{w.word},{w.right}⟩,{w.left}⟩\n'
              f'def origins : OriginCert := {orig}\n'
              f'def boxes : BoxProof := {splits}\n\n')
    if len(orig)<8000:
        proof='theorem valid : rule.Valid := checkWindow_sound origins boxes rule (by decide +kernel)\n'
    else:
        facts=[f'private theorem n{u} : origins.nodeOK {u} = true := by decide +kernel' for u in range(w.size)]
        names=','.join(f'n{u}' for u in range(w.size))
        facts += ['','theorem valid : rule.Valid := by',
                  '  apply checkWindow_parts (C := origins) (box := boxes)',
                  '  · decide +kernel','  · apply every_iff.mp',
                  f'    change every {w.size} origins.nodeOK = true',
                  f'    simp only [every,{names}, Bool.true_and]',
                  '  · decide +kernel']
        proof='\n'.join(facts)+'\n'
    if i<4:
        cumulative = ('def rules : List Rule := [rule]\n'
                      'theorem all_valid (r : Rule) (h : r ∈ rules) : r.Valid := by\n'
                      '  have eq : r=rule := by simpa [rules] using h\n'
                      '  exact eq ▸ valid\n')
    else:
        prev=f'Staircase.WindowData.R{i-4:03d}'
        cumulative = (f'def rules : List Rule := rule :: {prev}.rules\n'
                      'theorem all_valid (r : Rule) (h : r ∈ rules) : r.Valid := by\n'
                      '  rcases List.mem_cons.mp h with rfl | tail\n'
                      f'  · exact valid\n  · exact {prev}.all_valid r tail\n')
    return header+proof+'\n'+cumulative+f'\nend Staircase.WindowData.R{i:03d}\n'


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('indices',nargs='*',type=int)
    parser.add_argument('--out',type=Path,default=ROOT/'Staircase'/'WindowData')
    args=parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    rules=[list(map(int,l.split())) for l in
           (ROOT/'certificates'/'five-fourths-windows.txt').read_text().splitlines()]
    for i in args.indices or range(len(rules)):
        (args.out/f'R{i:03d}.lean').write_text(render(i,rules[i]))
