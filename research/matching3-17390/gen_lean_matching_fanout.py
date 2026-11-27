"""Generate Lean bitvector satisfiability certificates for the three one-primitive cases."""
from check_matching import BIT
from itertools import combinations
from pathlib import Path

def disj(items):return '('+' || '.join(items or ['false'])+')'
def conj(items):
    if not items: return 'true'
    if len(items)==1: return '('+items[0]+')'
    n=len(items)//2
    return '('+conj(items[:n])+' && '+conj(items[n:])+')'

def count(items,width=4):return '('+' + '.join(f'(if {q} then 1#{width} else 0#{width})' for q in items)+')'
def het(x,y):return f'!({x} == {y})'
def pick(sel,values):
    out='0#21'
    for j in reversed(range(len(values))):
        out=f'(if {sel} == {j}#5 then {values[j]} else {out})'
    return out

import sys
# K, mode (0 AND / 1 OR), adjacent/disjoint shape, shared internals, extra shared raw or -1.
cases=[tuple(map(int,line.split())) for line in Path('lean-fanout-cases.txt').read_text().splitlines() if line]
for K,mode,shape,shared,third in cases:
    nm=f'K{K}O{mode}S{shape}I{shared}X{third if third>=0 else "n"}'
    op=bool(mode)
    q=(1,4)[shape]
    raws=[f'w{j}' for j in range(9)]
    gs=[f'g{j}' for j in range(K)]
    wires=raws+gs
    txt=['import Std.Tactic.BVDecide','',f'namespace ProofLantern.Matching{nm}',
         'set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in',
         'theorem noModelWithOnePrimitive',
         '    ('+' '.join(f'{lr}{j}' for j in range(1,K) for lr in ['a','b'])+' : BitVec 5)',
         '    ('+' '.join(f'o{j}' for j in range(1,K))+' : Bool)',
         '    ('+' '.join(f'{r}{j}' for r in ['A','B','g'] for j in range(1,K))+' : BitVec 21) :']
    for x in range(9):
        v=sum(((u>>x)&1)<<j for j,(u,_) in enumerate(BIT))
        txt.append(f'  let w{x} : BitVec 21 := {v}#21')
    txt.append(f'  let g0 : BitVec 21 := w0 {"|||" if op else "&&&"} w{q}')
    fs=[f'g{K-1} == 63#21']
    for j in range(1,K):
        fs += [f'a{j}.ult b{j}', f'b{j}.ult {9+j}#5']
        if j>1:
            fs.append(f'(!(o{j} == o{j-1}) || !(b{j}.ult {8+j}#5) || !(b{j}.ult b{j-1}))')
        for k,w in enumerate(wires[:9+j]):
            fs += [f'(!(a{j} == {k}#5) || (A{j} == {w}))', f'(!(b{j} == {k}#5) || (B{j} == {w}))']
        fs.append(f'g{j} == (if o{j} then A{j} ||| B{j} else A{j} &&& B{j})')
    for x in range(9):
        expect=(2 if x in (0,q,third) else 1)-(1 if x in (0,q) else 0)
        readers=count([disj([f'a{j} == {x}#5',f'b{j} == {x}#5']) for j in range(1,K)])
        fs.append(f'!({readers}.ult {expect}#4)' if x in (0,q,third) else f'{readers} == {expect}#4')
        if x not in (0,q,third):
            for j in range(1,K):
                fs.append(f'(!(a{j} == {x}#5) || !(b{j}.ult 9#5))')
    for x in range(K-1):
        txt.append(f'  let load{x} : BitVec 4 := '+count([disj([f'a{j} == {9+x}#5',f'b{j} == {9+x}#5']) for j in range(x+1,K)]))
        fs.append(f'!(load{x} == 0#4)')
    fs.append(count([f'!(load{x}.ult 2#4)' for x in range(K-1)])+f' == {shared}#4')
    fs += [het(a,b) for a,b in combinations(wires,2)]
    for x in range(9):
        for row,(u,tr) in enumerate(BIT):
            if bool(u>>x&1)!=bool(tr):continue
            signals=[]
            if x in (0,q):
                other=x^q
                if bool(u>>other&1)!=op:continue
            for j in range(1,K):
                signals += [conj([f'a{j} == {x}#5',het(f'o{j}',f'B{j}.getLsbD {row}')]),
                            conj([f'b{j} == {x}#5',het(f'o{j}',f'A{j}.getLsbD {row}')])]
            fs.append(disj(signals))
    txt.append('  '+conj(fs).replace(' && ',' &&\n    ')+' = false := by')
    txt.append('    bv_decide (config := { timeout := 150 })')
    txt.append(f'end ProofLantern.Matching{nm}')
    Path(f'MatchingFanout{nm}.lean').write_text('\n'.join(txt)+'\n')
