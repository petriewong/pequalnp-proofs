import argparse,time
from z3 import *
p=argparse.ArgumentParser()
p.add_argument('placement',choices=['same','opposite'])
p.add_argument('--seconds',type=int,default=240)
p.add_argument('--ands',type=int,nargs=2,default=[4,7])
a=p.parse_args()
# Only the fourteen support singletons, 49 promises, and zero.
rows=[0]+[1<<i for i in range(14)]+[(1<<i)|(1<<(7+j)) for i in range(7) for j in range(7)]
val=[sum(1<<t for t,r in enumerate(rows) if r&(1<<j)) for j in range(14)]
goal=sum(1<<t for t,r in enumerate(rows) if (r&127 and r>>7 and (r&127)!=(r>>7)))
width=len(rows)
repeat={2, 3 if a.placement=='same' else 10}
others=set(range(14))-{0,1,7,8}-repeat
mates={j+7 if j<7 else j-7 for j in repeat}
pure=[(0,7),(1,8)]
K=22; N=14+K
X=[BitVec(f'x{i}',6) for i in range(K)]
Y=[BitVec(f'y{i}',6) for i in range(K)]
V=[BitVecVal(v,width) for v in val]+[BitVec(f'v{i}',width) for i in range(K)]
A=[Bool(f'and{i}') for i in range(K)]
# Tactic does not use internet and only decides this finite fixed branch.
s=SolverFor('QF_BV'); s.set(timeout=a.seconds*1000)
def count(xs,maxn): return Sum([If(b, BitVecVal(1,7), BitVecVal(0,7)) for b in xs]) if xs else BitVecVal(0,7)
for i in range(K):
  x,y=X[i],Y[i]
  left,right=BitVec(f'l{i}',width),BitVec(f'r{i}',width)
  s.add(ULT(x,y), ULT(y,14+i))
  s.add(*[Implies(x==j,left==V[j]) for j in range(14+i)])
  s.add(*[Implies(y==j,right==V[j]) for j in range(14+i)])
  s.add(V[14+i]==If(A[i],left&right,left|right))
  # Every gate except output lies on a path to output.
  if i<K-1: s.add(Or([z==14+i for q in range(i+1,K) for z in [X[q],Y[q]]]))
  for j in range(i):
    s.add(Or(x!=X[j],y!=Y[j],A[i]!=A[j]))
for i,(x,y) in enumerate(pure): s.add(X[i]==x,Y[i]==y,Not(A[i]))
s.add(V[-1]==goal)
andcount=count(A,7); s.add(UGE(andcount,a.ands[0]),ULE(andcount,a.ands[1]))
for j in range(14):
  touched=[Or(X[i]==j,Y[i]==j) for i in range(K)]
  s.add(count(touched,2)==(2 if j in repeat else 1))
  s.add(*[Implies(touched[i],Not(A[i])) for i in range(K)])
  if j in mates:
    opp=j-7 if j>=7 else j+7
    # With exactly one reader of this mate, its other operand depends on its
    # repeated twin, hence this gate is already high at that twin alone.
    s.add(*[Implies(touched[i], Extract(1+opp,1+opp,V[14+i])==1) for i in range(K)])
if a.placement=='opposite':
  x,y=sorted(repeat)
  s.add(Or([And(X[i]==x,Y[i]==y) for i in range(2,K)]))
# A mismatched raw cannot directly share an ordinary raw's sole OR.
for j in others:
  for k in range(14):
    if k%7 != j%7:
      x,y=sorted([j,k])
      s.add(*[Or(X[i]!=x,Y[i]!=y) for i in range(2,K)])
    elif j!=k and k not in repeat:
      x,y=sorted([j,k])
      s.add(*[Or(X[i]!=x,Y[i]!=y) for i in range(2,K)])
print('scope',a.placement,'ands',a.ands,'timeout_s',a.seconds,'rows',len(rows),flush=True)
t=time.monotonic(); result=s.check(); print(result,s.reason_unknown() if result==unknown else '',time.monotonic()-t,flush=True)
if result==sat:
  m=s.model()
  gates=[(is_true(m.eval(A[i])),m.eval(X[i]).as_long(),m.eval(Y[i]).as_long()) for i in range(K)]
  for i in range(7):
    for j in range(7):
      wire=[k in (i,7+j) for k in range(14)]
      for an,x,y in gates: wire.append(wire[x] and wire[y] if an else wire[x] or wire[y])
      assert wire[-1]==(i!=j),(i,j)
  print('verified all 49 promises independently:',gates)
