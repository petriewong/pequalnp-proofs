"""Necessary ten-slot routing model for the three-pair, four-star, two-helper residual."""
from itertools import combinations
import z3,sys,time
first,seconds,seed=map(int,sys.argv[1:])
k=10; N=7
edges=[(i,j) for i,j in combinations(range(7),2) if i<3]
W=7+len(edges); positives=(1<<W)-128
c=z3.Then("simplify","propagate-values","solve-eqs","card2bv","bit-blast","tseitin-cnf","sat").solver()
c.set(timeout=seconds*1000,random_seed=seed)
w=[z3.BitVecVal((1<<i)|sum(1<<(7+j) for j,e in enumerate(edges) if i in e),W) for i in range(N)]
target=[positives|(127^(1<<i)) for i in range(3,7)]
active=[]; during=[]; ls=[];rs=[]
for i in range(k):
 n=len(w)
 l=[z3.Bool(f'l{i}_{j}') for j in range(n)]; r=[z3.Bool(f'r{i}_{j}') for j in range(n)]
 a,b,g=[z3.BitVec(f'{s}{i}',W) for s in 'abg']
 act=z3.Bool(f'act{i}');op=z3.Bool(f'or{i}')
 if i>0:c.add(z3.Implies(act,active[-1]))
 for q in (l,r):c.add(z3.PbEq([(b,1) for b in q],1))
 for j,v in enumerate(w):
  c.add(z3.Implies(l[j],z3.And(a==v,z3.Or(r[j+1:]))),z3.Implies(r[j],b==v))
 c.add(g==z3.If(act,z3.If(op,a|b,a&b),0))
 c.add(z3.Implies(act,z3.And(g!=0,*[g!=v for v in w])))
 c.add(z3.Implies(z3.And(act,z3.Not(op)),z3.Extract(6,0,g)!=0))
 c.add(z3.Implies(z3.Or([g==t for t in target]),op))
 w.append(g);active.append(act);during.append(op);ls.append(l);rs.append(r)
 assert n==N+i
c.add(active[0],active[1],during[0],during[1])
a,b=[(0,1),(0,3),(3,4)][first]
c.add(ls[0][a],rs[0][b])
c.add(z3.PbEq([(z3.And(a,z3.Not(o)),1) for a,o in zip(active,during)],2))
for v in target:c.add(z3.Or([q==v for q in w[N:]]))
# Neither residual operand can be a bare primary (must cover every pair).
fl=[z3.Bool(f'fl{i}') for i in range(k)]; fr=[z3.Bool(f'fr{i}') for i in range(k)]
X,Y=z3.BitVecs('resA resB',W)
for q in (fl,fr):c.add(z3.PbEq([(b,1) for b in q],1))
for i in range(k):
 v=w[N+i]
 c.add(z3.Implies(fl[i],z3.And(X==v,z3.Or(fr[i+1:]))),z3.Implies(fr[i],Y==v))
 readers=[z3.And(active[j],z3.Or(ls[j][N+i],rs[j][N+i])) for j in range(i+1,k)]
 c.add(z3.Implies(active[i],z3.Or(fl[i],fr[i],*[v==g for g in target],*readers)))
 if i>1:
  for j in range(N+i-1):
   c.add(z3.Implies(z3.And(active[i],rs[i][j],during[i]==during[i-1]),z3.Or(rs[i-1][:j+1])))
c.add((X&Y)==positives)
print('residual exact minimal two-helper',first,seed,'budget',seconds,flush=True)
t=time.perf_counter();q=c.check();print(q,c.reason_unknown() if q==z3.unknown else '',time.perf_counter()-t,flush=True)
if q==z3.sat:
 m=c.model()
 for i in range(k):
  if not z3.is_true(m[active[i]]):break
  print(i,int(z3.is_true(m[during[i]])),next(j for j,b in enumerate(ls[i]) if z3.is_true(m[b])),
      next(j for j,b in enumerate(rs[i]) if z3.is_true(m[b])),m.eval(w[N+i]).as_long())
 print(m.eval(X).as_long(),m.eval(Y).as_long())
