from check_matching import BIT, N, verify, target
from itertools import combinations
import json,z3,sys,time
K, op0, shape, seconds, internals, third = map(int,sys.argv[1:])
# With independent row/column relabeling and transposition, the first two distinct edge
# primaries have two orbits: adjacent (0,1) or vertex disjoint (0,4).
second = (1,4)[shape]
b=len(BIT)
s=z3.Then("simplify","propagate-values","solve-eqs","card2bv","bit-blast","tseitin-cnf","sat").solver()
s.set(timeout=seconds*1000)
w=[z3.BitVecVal(sum(((x>>j)&1)<<i for i,(x,_) in enumerate(BIT)),b) for j in range(N)]
ops=[]
ls=[]
rs=[]
for k in range(K):
    n=N+k
    l=[z3.Bool(f'l{k}_{i}') for i in range(n)]
    r=[z3.Bool(f'r{k}_{i}') for i in range(n)]
    op=z3.Bool(f'o{k}')
    a,q,g=[z3.BitVec(f'{x}{k}',b) for x in ('a','b','g')]
    s.add(z3.PbEq([(x,1) for x in l],1), z3.PbEq([(x,1) for x in r],1))
    for j,(x,y,v) in enumerate(zip(l,r,w)):
        s.add(z3.Implies(x,z3.And(a==v,z3.Or(r[j+1:]))),z3.Implies(y,q==v))
    if k>1:
        for j,y in enumerate(r[:-1]):
            s.add(z3.Implies(z3.And(y,ops[-1]==op),z3.Or(rs[-1][:j+1])))
    s.add(g==z3.If(op,a|q,a&q))
    w.append(g)
    ops.append(op)
    ls.append(l)
    rs.append(r)
s.add(ls[0][0],rs[0][second],ops[0]==bool(op0))
s.add(w[-1]==z3.BitVecVal(sum(val<<i for i,(_,val) in enumerate(BIT)),b))
s.add(z3.Distinct(*w))
for j in range(N+K-1):
    s.add(z3.Or([q[j] for k in range(K) for q in (ls[k],rs[k]) if j<len(q)]))

# Pivotal cap: with exactly one x-reader, every pivotal assignment must leave
# that reader sensitive to x. Every maximal negative omitting x is pivotal,
# as is each minimal positive containing x after turning off x.
for x in range(N):
    readers=[z3.Or(l[x],r[x]) for l,r in zip(ls,rs)]
    one=z3.PbEq([(r,1) for r in readers],1)
    for i,(l,r,op) in enumerate(zip(ls,rs,ops)):
        # Respect canonical topology but use normalized operand bit-vector.
        a=z3.BitVec(f'a{i}',b);q=z3.BitVec(f'b{i}',b)
        for rowside,comp in ((l,q),(r,a)):
            pivot=[j for j,(u,truth) in enumerate(BIT) if bool(u & (1<<x))==bool(truth)]
            v=sum(1<<j for j in pivot)
            s.add(z3.Implies(z3.And(one,rowside[x]),z3.If(op,(comp & v)==0,(comp & v)==v)))
        for y in range(N):
            if y==x:continue
            s.add(z3.Implies(z3.Or(z3.And(l[x],r[y]),z3.And(l[y],r[x])),z3.Not(one)))


# A pivotal row needs some responding direct reader, even if x has more than one.
for x in range(N):
    for j,(u,truth) in enumerate(BIT):
        if bool(u & (1<<x))!=bool(truth):
            continue
        signal=[]
        for i,(l,r,op) in enumerate(zip(ls,rs,ops)):
            a=z3.Extract(j,j,z3.BitVec(f'a{i}',b))==1
            q=z3.Extract(j,j,z3.BitVec(f'b{i}',b))==1
            signal.extend((z3.And(l[x],op!=q),z3.And(r[x],op!=a)))
        s.add(z3.Or(signal))
def fanout(node):
    return [z3.Or(l[node],r[node]) for l,r in zip(ls,rs) if node<len(l)]
def shared(node):return z3.PbGe([(v,1) for v in fanout(node)],2)
raw_shared={0,second}|({third} if third!=-1 else set())
for j in range(N):
    s.add(shared(j)==(j in raw_shared))
ks=[shared(j) for j in range(N,N+K-1)]
s.add(z3.PbEq([(x,1) for x in ks],internals))

types={}
for x,y in combinations(sorted(raw_shared),2):
    for wanted_op in (False,True):
        types[x,y,wanted_op]=z3.Or([
            z3.And(l[x],r[y],o==wanted_op) for l,r,o in zip(ls,rs,ops)])
def typ(x,y,o):
    return types[min(x,y),max(x,y),o]
for x in sorted(raw_shared):
    piv=[s for s in range(512) if not(s>>x&1) and not target(s) and target(s|(1<<x))]
    exactly2=z3.PbEq([(v,1) for v in fanout(x)],2)
    for y,z in combinations(sorted(raw_shared-{x}),2):
        blocks={(bool(u>>y&1),bool(u>>z&1)) for u in piv}
        for a,b2 in blocks:
            s.add(z3.Not(z3.And(exactly2,typ(x,y,a),typ(x,z,b2))))
for x,y in combinations(sorted(raw_shared),2):
    # Two fully saturated pair consumers (one AND, one OR) would make these raw
    # edge labels interchangeable, but PM3 is not invariant under swapping just them.
    s.add(z3.Not(z3.And(z3.PbEq([(v,1) for v in fanout(x)],2),
                        z3.PbEq([(v,1) for v in fanout(y)],2),
                        typ(x,y,True),typ(x,y,False))))
print('matching',K,'first-or',op0,'shape',shape,'rows',b,'internal shared',internals,'raw shared',sorted(raw_shared),flush=True)
t=time.perf_counter()
res=s.check()
print(str(res),s.reason_unknown() if res==z3.unknown else '',time.perf_counter()-t,flush=True)
if res==z3.sat:
    m=s.model()
    circ=[[('or' if z3.is_true(m[o]) else 'and'),
           next(i for i,q in enumerate(l) if z3.is_true(m[q])),
           next(i for i,q in enumerate(r) if z3.is_true(m[q]))] for o,l,r in zip(ops,ls,rs)]
    assert verify(circ)
    print(json.dumps(circ))
