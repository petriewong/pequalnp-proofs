"""Construct circuits for a fixed 4x4 one-hot table with an OR/AND rectangle cover."""
from collections import deque
from functools import lru_cache
import argparse,json

p=argparse.ArgumentParser()
p.add_argument('rows',type=int,nargs=4)
p.add_argument('--limit',type=int,default=8)
a=p.parse_args()
assert all(0<=r<16 for r in a.rows)
want=sum(r<<(4*i) for i,r in enumerate(a.rows))
FULL=65535
SINGLE=(1,2,4,8)
ONES=sum(1<<i for i in SINGLE)

def or_prefixes():
    history={ONES:()}
    q=deque([ONES])
    while q:
        state=q.popleft()
        vs=[i for i in range(1,16) if state>>i&1]
        for i,x in enumerate(vs):
            for y in vs[i+1:]:
                z=x|y
                dest=state|(1<<z)
                if dest in history: continue
                history[dest]=history[state]+((x,y,z),)
                q.append(dest)
    out={}
    # A state with extra available masks may produce multiple requested unions
    # more cheaply than their separate minimal OR trees.
    for s,c in history.items():
        payload=s&~ONES
        while True:
            if payload not in out or len(c)<len(out[payload]):out[payload]=c
            if payload==0:break
            payload=(payload-1)&(s&~ONES)
    return out
PLAN=or_prefixes()

def rect(R,C): return sum(C<<(4*i) for i in range(4) if R>>i&1)
def flag(x):return (1<<x) if x!=15 and x not in SINGLE else 0
def evalC(g,out,row,col):
    w=[u==row for u in range(4)]+[v==col for v in range(4)]
    for op,x,y in g:w.append(not w[x] if op=='not' else w[x] and w[y] if op=='and' else w[x] or w[y])
    return w[out]
def realize(parts,rm,cm,inv):
    gates=[]
    def add(op,x,y=None): gates.append((op,x,y));return 7+len(gates)
    wi=[{s:i+o for i,s in enumerate(SINGLE)} for o in [0,4]]
    for plans,W in zip((PLAN[rm],PLAN[cm]),wi):
        for x,y,z in plans:W[z]=add('or',W[x],W[y])
    terms=[]
    for R,C,_ in parts:
        if R==15: terms.append(wi[1][C])
        elif C==15: terms.append(wi[0][R])
        else:terms.append(add('and',wi[0][R],wi[1][C]))
    out=terms[0]
    for w in terms[1:]:out=add('or',out,w)
    if inv:out=add('not',out)
    return gates,out

best=a.limit+1; witness=None
for invert,targ in [(False,want),(True,FULL^want)]:
    if targ in (0,FULL):
        if targ==FULL:
            g=[('or',0,1),('or',2,3),('or',8,9)]
            if invert:g.append(('not',10,None))
            if len(g)<best:best=len(g);witness=(g,7+len(g))
        continue
    opts=[(R,C,rect(R,C)) for R in range(1,16) for C in range(1,16) if not rect(R,C)&~targ]
    opts.sort(key=lambda x:(-x[2].bit_count(),x[0]!=15 and x[1]!=15))
    by=[[o for o in opts if o[2]>>i&1] for i in range(16)]
    seen={}
    def dfs(miss,rm,cm,part,na):
        global best,witness
        current=na+max(0,len(part)-1)+len(PLAN[rm])+len(PLAN[cm])+int(invert)
        if current>=best:return
        if not miss:
            witness=realize(part,rm,cm,invert)
            best=len(witness[0]);return
        if part and current+1>=best:return
        key=(miss,rm,cm,bool(part))
        if key in seen and seen[key]<=current:return
        seen[key]=current
        i=min((j for j in range(16) if miss>>j&1),key=lambda j:len(by[j]))
        for R,C,M in by[i]:
            dfs(miss&~M,rm|flag(R),cm|flag(C),part+[(R,C,M)],na+int(R!=15 and C!=15))
    dfs(targ,0,0,[],0)
if not witness:
    print(json.dumps({'found':False,'scope':'one-hot rectangle model only'}))
else:
    g,o=witness
    for i in range(4):
        for j in range(4):assert evalC(g,o,i,j)==bool(a.rows[i]>>j&1)
    print(json.dumps({'found':True,'gates':g,'output':o,'count':len(g),'not_count':sum(x[0]=='not' for x in g),'rows_checked':16}))
