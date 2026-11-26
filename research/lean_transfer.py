"""Export a finite closure certificate for deficit states of the slash-word automaton."""
from collections import defaultdict, deque
from pathlib import Path
from lean_windows import packed

ROOT=Path(__file__).resolve().parents[1]
BOX=36


def ordered_rules():
    lines=(ROOT/'certificates'/'five-fourths-windows.txt').read_text().splitlines()
    order=[i for start in range(4) for i in reversed(range(start,len(lines),4))]
    return [list(map(int,lines[i].split())) for i in order]


def array(values):
    return '#['+','.join(hex(x) for x in values)+']'


def main():
    rules=ordered_rules()
    values=[f'⟨⟨{r[1:-1]},{r[-1]}⟩,{r[0]}⟩' for r in rules]
    (ROOT/'Staircase/RuleValues.lean').write_text(
        'module\n\npublic import Staircase.Local\n\n@[expose] public section\nnamespace Staircase\n\n'
        'def listedRules : List Rule := [\n'+',\n'.join(values)+']\n\nend Staircase\n')
    positions=[]
    starts=[0]*37
    letters=[0]*37
    ends=[0]*37
    cont=0
    for idx,(left,*word,right) in enumerate(rules):
        for j,v in enumerate(word):
            i=len(positions)
            positions.append(f'⟨⟨{word[j:]},{right}⟩,{idx if j==0 else len(rules)}⟩')
            bit=1<<i
            if j==0:
                for l in range(left+1):
                    starts[l]|=bit
            for p in range(v+1):
                letters[p]|=bit
            if j+1<len(word):
                cont|=bit
            else:
                for r in range(right+1):
                    ends[r]|=bit

    table=defaultdict(list)
    queue=deque()

    def add(l,r,d,mem):
        group=table[l,r]
        if any(e>=d and (s&mem)==s for e,s in group):
            return
        group[:]=[(e,s) for e,s in group if not (d>=e and (mem&s)==mem)]
        group.append((d,mem))
        queue.append((l,r,d,mem))

    for l in range(37):
        for r in range(37):
            add(l,r,0,0)

    def dangerous(L,R,d,mem):
        for p in range(R+1):
            for r in (2*(R-p),2*(R-p)+1):
                debt=d+5-(2*p+(L+1)//2+(r+1)//2)
                if debt<=0:
                    continue
                active=(mem|starts[L])&letters[p]
                if active&ends[r]:
                    continue
                assert debt<=14
                yield p,r,p+L//2,debt,(active&cont)<<1

    while queue:
        L,R,d,m=queue.popleft()
        if (d,m) in table[L,R]:
            for _,r,l,e,after in dangerous(L,R,d,m):
                add(l,r,e,after)
    seeds=[(L,R,0,0) for L in range(37) for R in range(37)]
    extras=sorted((L,R,d,m) for (L,R),group in table.items() for d,m in group if d)
    states=seeds+extras
    ids={s:i for i,s in enumerate(states)}
    hints=[0]*(74*len(states))
    for i,(L,R,d,m) in enumerate(states):
        for p,r,l,need,after in dangerous(L,R,d,m):
            best=next((debt,s) for debt,s in table[l,r] if debt>=need and (s&after)==s)
            hints[74*i+2*p+r%2]=ids[(l,r)+best]

    target=ROOT/'Staircase'/'DualData.lean'
    target.write_text('module\n\npublic import Staircase.Transfer\npublic import Staircase.RuleValues\n'
        'public import Staircase.Batch\n\n@[expose] public section\nnamespace Staircase.Certificate\n\n'
        'set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n\n'
        'def machine : Machine := ⟨[\n'+',\n'.join(positions)+'],\n'+
        ',\n'.join([array(starts),array(letters),array(ends),hex(cont)])+'⟩\n\n'
        'def dual : Dual := ⟨\n'+',\n'.join(packed([s[j] for s in extras]) for j in range(4))+
        ',\n'+packed(hints)+'⟩\n\ndef stateTest := dual.rowOK machine\n\nend Staircase.Certificate\n')

    step=16
    def combine(names):
        if len(names)==1:
            return names[0]
        mid=len(names)//2
        return '(batch_join '+combine(names[:mid])+' '+combine(names[mid:])+')'

    groups=[]
    for lane in range(4):
        first=len(states)*lane//4
        last=len(states)*(lane+1)//4
        out=['module','','public import Staircase.DualData','','@[expose] public section',
             'namespace Staircase.Certificate','','set_option maxRecDepth 100000','set_option maxHeartbeats 0','']
        names=[]
        for start in range(first,last,step):
            span=min(step,last-start)
            name=f'b{start}'
            out.append(f'private theorem {name} : Batch stateTest {start} {span} := batch_checked (by decide +kernel)')
            names.append(name)
        label=f'states{lane}'
        out+=['',f'theorem {label} : Batch stateTest {first} {last-first} :=',
              '  '+combine(names),'','end Staircase.Certificate','']
        (ROOT/'Staircase'/f'DualPart{lane}.lean').write_text('\n'.join(out))
        groups.append(label)
    print(len(states),len(extras),len(positions),flush=True)


if __name__=='__main__':
    main()
