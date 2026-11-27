"""Necessary Crown7 p=3 repeated-input profiles. This does not count circuits."""
from itertools import product,combinations
def canon(x,y):
    return min(tuple(sorted(zip(x,y))),tuple(sorted(zip(y,x))))
def prior(x,y):
    if sum(t!='O' for t in x+y)<3 or 'R' not in x+y:return False
    for u,v in ((x,y),(y,x)):
        for i,t in enumerate(u):
            p=[a for j,a in enumerate(v) if j!=i]
            if t=='A' and ('A' in p or p.count('R')>1):return False
            if t=='R' and sum(a!='O' for a in p)>2:return False
    return True
before=set();masking=set();reciprocal=set()
for a in product('ORA',repeat=8):
    x,y=a[:4],a[4:]
    if not prior(x,y):continue
    c=canon(x,y);before.add(c)
    if any(i!=j and {x[i],y[j]}=={'A','R'} for i in range(4) for j in range(4)):continue
    masking.add(c)
    if any(x[i]==y[i]==x[j]==y[j]=='R' and any('O'!=t for k in range(4) if k not in (i,j) for t in (x[k],y[k]))
           for i,j in combinations(range(4),2)):continue
    reciprocal.add(c)
assert [len(s) for s in (before,masking,reciprocal)]==[34,17,15]
priority=sorted(','.join(map(''.join,c)) for c in reciprocal if sum(t=='R' for p in c for t in p)==1)
assert priority==['AO,AO,AO,RO','AO,AO,OO,RO']
print('Canonical necessities:',*[len(s) for s in (before,masking,reciprocal)])
print('One-repeat priority:', *priority)
print('Remaining profiles:')
for c in sorted(reciprocal):print(','.join(map(''.join,c)))

def erased(c):
    t=''.join(map(''.join,c))
    return t.count('O')+(t.count('A')+1)//2>=6
excluded=sorted(','.join(map(''.join,c)) for c in reciprocal if erased(c))
assert excluded==['AO,AO,AO,RO','AO,AO,OO,RO','AO,OO,RO,RO','AR,OO,OO,RO']
print('Clean erasure excluded:',*excluded)
print('Remaining',sum(not erased(c) for c in reciprocal))
