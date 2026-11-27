from itertools import combinations
import sys,z3,time
n,k,nand=7,15,5
shape,seconds=map(int,sys.argv[1:])
from importlib.machinery import SourceFileLoader
shapes=SourceFileLoader('raw_or_prefixes','evidence/raw-or-prefixes.py').load_module().all
edges=shapes[shape][1]
assert len(edges)>=4
p=[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
basic=[1<<i for i in range(n)]+p
base=(1<<n)-1
zeroSets=[1<<i for i in range(n)]+p
rows=basic+[base^x for x in zeroSets];B=len(rows)
s=z3.Then("simplify","propagate-values","solve-eqs","card2bv","bit-blast","tseitin-cnf","sat").solver();s.set(timeout=seconds*1000)
raw=[z3.BitVecVal(sum(1<<j for j,x in enumerate(rows) if x>>i&1),B) for i in range(n)]
w=raw[:]; ls=[];rs=[];ops=[];xy=[]; deps=[z3.BoolVal(False)]*n
for i in range(k):
 l=[z3.Bool(f'l{i}_{j}') for j in range(n+i)];r=[z3.Bool(f'r{i}_{j}') for j in range(n+i)]
 ls.append(l);rs.append(r)
 s.add(z3.PbEq([(q,1) for q in l],1),z3.PbEq([(q,1) for q in r],1))
 for j,q in enumerate(l):
  s.add(z3.Implies(q,z3.Or(r[j+1:])))
 a,b,g=[z3.BitVec(f'{x}{i}',B) for x in 'abg']
 for j,x in enumerate(w):s.add(z3.Implies(l[j],a==x),z3.Implies(r[j],b==x))
 op=z3.Bool(f'o{i}');ops.append(op);xy.append((a,b));s.add(g==z3.If(op,a|b,a&b));w.append(g)
 ld=z3.Or([z3.And(sel,dep) for sel,dep in zip(l,deps)])
 rd=z3.Or([z3.And(sel,dep) for sel,dep in zip(r,deps)])
 d=z3.Bool(f'andAncestor{i}')
 s.add(d==z3.Or(z3.Not(op),ld,rd))
 if i==k-1:s.add(ld,rd, z3.Not(op))
 deps.append(d)
s.add(z3.PbEq([(z3.Not(o),1) for o in ops],nand))

s.add(w[-1]==z3.BitVecVal(sum(1<<j for j,x in enumerate(rows) if x.bit_count()>1),B))
s.add(z3.Distinct(*w))
if n==7 and k==15:
 for j in range(n):
  readers=[z3.Or(l[j],r[j]) for l,r in zip(ls,rs)]
  # A unique raw reader would OR with an earlier wire that accepts another singleton,
  # making the corresponding singleton and pair indistinguishable downstream.
  s.add(z3.PbEq([(x,1) for x in readers],2))
  for x,o in zip(readers,ops):s.add(z3.Implies(x,o))

for j,(x,y) in enumerate(edges):s.add(ops[j],ls[j][x],rs[j][y])
for j in range(len(edges),k):s.add(z3.Not(z3.And(z3.Or(ls[j][:n]),z3.Or(rs[j][:n]))))


for j in range(n+k-1):
 s.add(z3.Or([q for l,r in zip(ls,rs) if j<len(l) for q in (l[j],r[j])]))
def lit(x,j):return z3.Extract(j,j,x)==1
for i in range(k-1):
 s.add(z3.Implies(z3.Not(ops[i]),z3.Or([lit(w[n+i],j) for j in range(n)])))
la,ra=xy[-1]
for j in range(n,len(basic)):s.add(lit(la,j),lit(ra,j))

if n==7 and k==15:
 for u in range(n):
  for v in range(n):
   if u==v:continue
   s.add(z3.Or([z3.Or(z3.And(l[u],z3.Not(lit(b,v))),z3.And(r[u],z3.Not(lit(a,v))))
     for l,r,(a,b) in zip(ls,rs,xy)]))

for i,j in combinations(range(n),2):
 s.add(z3.Or([z3.And(z3.Not(op),z3.Or(
   z3.And(lit(a,i),z3.Not(lit(b,i)),lit(b,j),z3.Not(lit(a,j))),
   z3.And(lit(b,i),z3.Not(lit(a,i)),lit(a,j),z3.Not(lit(b,j))))) for op,(a,b) in zip(ops,xy)]))
for j,missing in enumerate(zeroSets,len(basic)):
 lost=[z3.Or(z3.Not(lit(a,j)),z3.Not(lit(b,j))) for a,b in xy]
 remain=n-missing.bit_count()
 s.add(z3.PbLe([(z3.And(op,g),1) for op,g in zip(ops,lost)],k-nand-(2*remain-4)))
 # Valid for n' >=4 by published strict threshold count floor.
 total=k-(13 if remain==6 else (2*remain-3+(remain-1).bit_length()))
 if total>=0:s.add(z3.PbLe([(g,1) for g in lost],total))
print('four dirty AND helpers, both cones, degree exactly two, canonical raw-OR graph',shape,edges,'budget',seconds,flush=True)
t=time.perf_counter();q=s.check();print(q,s.reason_unknown() if q==z3.unknown else '',time.perf_counter()-t,flush=True)
if q==z3.sat:
 m=s.model()
 for op,l,r in zip(ops,ls,rs):
  print(int(z3.is_true(m[op])),next(i for i,x in enumerate(l) if z3.is_true(m[x])),next(i for i,x in enumerate(r) if z3.is_true(m[x])))
