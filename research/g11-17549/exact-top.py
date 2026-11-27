from z3 import *
import argparse,time,json
p=argparse.ArgumentParser();p.add_argument('terms',type=int);p.add_argument('--seconds',type=int,default=240);a=p.parse_args()
k=22-2*a.terms
row=list(map(int,open('oracle.txt').readline().split()))
P,N=row[11:13]; target=(1<<P)-1
neg=((1<<N)-1)^target
V=[BitVecVal(i,N) for i in row[:11]]+[BitVec(f'v{i}',N) for i in range(k)]
s=SolverFor('QF_BV');s.set(timeout=a.seconds*1000)
A=[Bool(f'junk{i}') for i in range(k)]
x=[BitVec(f'x{i}',6) for i in range(k+a.terms)]
y=[BitVec(f'y{i}',6) for i in range(k+a.terms)]
s.add(Sum([If(a,BitVecVal(1,5),BitVecVal(0,5)) for a in A])==2)
T=[]
for i in range(k+a.terms):
  bound=11+min(i,k)
  vx,vy=BitVec(f'l{i}',N),BitVec(f'r{i}',N)
  s.add(ULT(x[i],y[i]),ULT(y[i],bound))
  s.add(*[Implies(x[i]==j,vx==V[j]) for j in range(bound)])
  s.add(*[Implies(y[i]==j,vy==V[j]) for j in range(bound)])
  if i<k:
    s.add(V[11+i]==If(A[i],vx&vy,vx|vy),Implies(A[i],V[11+i]&neg!=0))
    s.add(Or([Or(x[j]==11+i,y[j]==11+i) for j in range(i+1,k+a.terms)]))
    for j in range(i):
      s.add(Or(x[i]!=x[j],y[i]!=y[j],A[i]!=A[j]))
  else:
    t=vx&vy;s.add(t!=0,t&neg==0);T.append(t)
    if i>k: s.add(ULT(x[i-1],x[i])|And(x[i-1]==x[i],ULT(y[i-1],y[i])))
from functools import reduce
s.add(reduce(lambda a,b:a|b,T)==target)
print('terms',a.terms,'routing',k,'scope strict 2 junk and all clean products terminal',flush=True)
t=time.monotonic();r=s.check()
print(str(r),s.reason_unknown() if r==unknown else '',time.monotonic()-t,flush=True)
if r==sat:
  m=s.model();g=[]
  for i in range(k+a.terms):
    g.append((m.eval(x[i]).as_long(),m.eval(y[i]).as_long(),int(i<k and not is_true(m.eval(A[i])))))
  cur=11+k
  for j in range(1,a.terms): g.append((cur,11+k+j,1));cur=10+len(g)
  E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  assert len(g)==21
  for mask in range(2048):
    w=[bool(mask>>i&1) for i in range(11)]
    for i,j,o in g:w.append(w[i] or w[j] if o else w[i] and w[j])
    assert w[-1]==any(w[i] and w[j] for i,j in E),mask
  print('verified all 2048',json.dumps(g),flush=True)
