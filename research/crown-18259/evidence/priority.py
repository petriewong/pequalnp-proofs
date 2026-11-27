"""Crown7 two remaining priority three-pure-pair reader profiles."""
import sys,z3,time
from itertools import combinations
mode,profile,seconds=sys.argv[1],sys.argv[2],int(sys.argv[3])
assert profile in ('AOAOAORO','AOAOOORO')
N,K=14,22
goal=sum(1<<(i*7+j) for i in range(7) for j in range(7) if i!=j)
rows=[(1<<i)|(1<<(7+j)) for i in range(7) for j in range(7)]
rows += [1<<i for i in range(14)]
cuts=[(6,7+i) for i in (3,4,5)] if mode=='guarded' else []
zrows=[0]+[1<<i for i in range(7)]+[(1<<i)|(1<<j) for i,j in combinations(range(7),2)]
base=len(rows)
for a,b in cuts:
 rows += [(z|(z<<7)) & ~((1<<a)|(1<<b)) for z in zrows]
W=len(rows)
target=goal|sum(1<<(base+d*len(zrows)+j) for d in range(len(cuts)) for j,z in enumerate(zrows) if z.bit_count()>=2)
s=z3.Then('simplify','propagate-values','solve-eqs','card2bv','bit-blast','tseitin-cnf','sat').solver()
s.set(timeout=seconds*1000)
w=[z3.BitVecVal(sum((1<<j) for j,x in enumerate(rows) if x>>i&1),W) for i in range(N)]
L=[];R=[];op=[];operands=[]
for i in range(K):
 n=N+i
 l=z3.Bools(' '.join(f'l{i}_{j}' for j in range(n)));r=z3.Bools(' '.join(f'r{i}_{j}' for j in range(n)))
 a,b,g=[z3.BitVec(f'{v}{i}',W) for v in 'abg'];o=z3.Bool(f'OR{i}')
 for v in (l,r):s.add(z3.PbEq([(q,1) for q in v],1))
 for j,v in enumerate(w):
  s.add(z3.Implies(l[j],z3.And(a==v,z3.Or(r[j+1:]))),z3.Implies(r[j],b==v))
 s.add(g==z3.If(o,a|b,a&b),g & goal!=0)
 L.append(l);R.append(r);op.append(o);w.append(g);operands.append((a,b))
s.add(w[-1]==target,z3.Distinct(*w))
def literal(w,j):return z3.Extract(j,j,w)==1
def readers(j):return [(i,z3.Or(L[i][j],R[i][j])) for i in range(max(0,j-N+1),K)]
def pair(i,a,b):
 if a>b:a,b=b,a
 return z3.And(L[i][a],R[i][b])
for i in range(3):s.add(pair(i,i,7+i),op[i])
tags={i:'O' for i in range(N)}
for i,t in enumerate(profile):tags[3+i//2+(7 if i%2 else 0)]=t
for j in range(N+K-1):s.add(z3.Or([v for _,v in readers(j)]))
for j,t in tags.items():
 rd=readers(j); s.add(z3.PbEq([(b,1) for _,b in rd],2 if t=='R' else 1))
 for i,b in rd:s.add(z3.Implies(b,op[i] if t!='A' else z3.Not(op[i])))
 if j%7>=3 and tags[(j+7)%14]!='R' and t!='R' and j<7:s.add(*[z3.Not(pair(i,j,j+7)) for i in range(3,K)])
 for row in [49+b for b in range(N) if (b<7)!=(j<7) and b%7!=j%7]+[8*b for b in range(7) if b!=j%7]:
  s.add(z3.Or([z3.Or(z3.And(L[i][j],op[i]!=literal(b,row)),z3.And(R[i][j],op[i]!=literal(a,row))) for i,(a,b) in enumerate(operands)]))
s.add(z3.PbLe([(z3.Not(o),1) for o in op],6),z3.PbGe([(z3.Not(o),1) for o in op],4))
for j,t in tags.items():
 if t!='A':continue
 for i,use in readers(j):
  rr=readers(N+i)
  s.add(z3.Implies(use,z3.PbEq([(b,1) for _,b in rr],1) if rr else z3.BoolVal(False)))
  for k,b in rr:s.add(z3.Implies(z3.And(use,b),op[k]))
for d,_ in enumerate(cuts):
 lo=base+d*len(zrows);hi=lo+len(zrows)-1
 masks=[z3.Extract(hi,lo,v) for v in w]
 fresh=[z3.And([masks[i]!=masks[j] for j in range(i)]) for i in range(N,N+K)]
 s.add(z3.PbGe([(q,1) for q in fresh],16))
 s.add(z3.PbGe([(z3.And(q,o),1) for q,o in zip(fresh,op)],10))
print(mode,profile,'rows',W,'cuts',cuts,'seconds',seconds,flush=True)
t=time.perf_counter();q=s.check();print(q,s.reason_unknown() if q==z3.unknown else '',time.perf_counter()-t,flush=True)
if q==z3.sat:
 m=s.model();gates=[(int(z3.is_true(m[o])),next(j for j,b in enumerate(l) if z3.is_true(m[b])),next(j for j,b in enumerate(r) if z3.is_true(m[b]))) for o,l,r in zip(op,L,R)]
 for i in range(7):
  for j in range(7):
   w0=[s in (i,7+j) for s in range(14)]
   for o,a,b in gates:w0.append(w0[a] or w0[b] if o else w0[a] and w0[b])
   assert w0[-1]==(i!=j)
 print(gates,flush=True)
