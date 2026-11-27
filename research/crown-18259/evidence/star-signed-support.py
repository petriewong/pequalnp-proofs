"""Seven-atom support model: multiple all-but-one masks via OR and exactly one AND."""
import sys,time,z3
m,k,budget=map(int,sys.argv[1:])
s=z3.Then("simplify","propagate-values","solve-eqs","card2bv","bit-blast","tseitin-cnf","sat").solver()
s.set(timeout=budget*1000)
# Zero and reflexive gates allow honest padding of a smaller network.
w=[z3.BitVecVal(x,7) for x in [0,1,2,4,8,16,32,64]]
ors=[]
for i in range(k):
 n=len(w); l=[z3.Bool(f"l{i}_{j}") for j in range(n)];r=[z3.Bool(f"r{i}_{j}") for j in range(n)]
 a,b,g=[z3.BitVec(f'{x}{i}',7) for x in 'abg']
 for q in l,r:s.add(z3.PbEq([(x,1) for x in q],1))
 for j,t in enumerate(w):
  s.add(z3.Implies(l[j],z3.And(a==t,z3.Or(r[j:]))),z3.Implies(r[j],b==t))
 op=z3.Bool(f'op{i}');ors.append(op);s.add(g==z3.If(op,a|b,a&b));w.append(g)
s.add(z3.PbEq([(z3.Not(o),1) for o in ors],1))
for j in range(m):
 z=127^(1<<(3+j))
 s.add(z3.Or([wire==z for wire in w]))
print('star masks',m,'gates',k,'one AND',flush=True)
t=time.perf_counter(); r=s.check(); print(r,s.reason_unknown() if r==z3.unknown else '',time.perf_counter()-t,flush=True)
if r==z3.sat:
 a=s.model()
 print([a.eval(x).as_long() for x in w],flush=True)
