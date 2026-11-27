"""Independent bottom-up topology enumeration + exact Z3 set cover."""
from itertools import combinations
import z3
from functools import lru_cache
@lru_cache(None)
def states(parts):
 if len(parts)==1:return frozenset({()})
 out=set()
 for a,b in combinations(parts,2):
  c=a|b
  new=tuple(sorted(set(parts)-{a,b}|{c}))
  for t in states(new):out.add(tuple(sorted((*t,c))))
 return frozenset(out)
trees=states((1,2,4,8,16,32))
assert len(trees)==945
def at(tag,i,j):
 a=int(tag[1]);return a==i or a==j if tag[0]=='p' else a==(i if tag[0]=='x' else j)
rows=[(i,j) for i in range(7) for j in range(7)]
bad={a for a,p in enumerate(rows) if p[0]==p[1]}
rest={a for a,p in enumerate(rows) if p[0]!=3 and p[0]!=p[1]}
def outs(words):
 return {i for i,row in enumerate(rows) if any(at(t,*row) for t in words)}
atoms=['p0','p1','p2','y4','y5','y6']
raw={t:outs([t]) for t in atoms+['y3','x4','x5','x6']}
for name,rs,o in [('AO,RO,RO,RO',['x4','x5','x6'],'y3'),('AR,OO,RO,RO',['x5','x6','y3'],'x4')]:
 count=0
 for tree in trees:
  signals=[raw[t] for t in atoms+[o]]+[raw[a]|raw[b] for a,b in combinations(rs,2)]
  signals += [outs([t for i,t in enumerate(atoms) if m>>i&1]) for m in tree]
  pieces={frozenset((x&y)&rest) for x,y in combinations(signals,2) if not (x&y)&bad and (x&y)&rest}
  ps=list(pieces)
  if not ps or set().union(*ps)!=rest:count+=1;continue
  s=z3.Solver()
  chosen=[z3.Bool('term'+str(i)) for i in range(len(ps))]
  for r in rest:s.add(z3.Or([a for a,p in zip(chosen,ps) if r in p]))
  s.add(z3.PbLe([(x,1) for x in chosen],5))
  assert s.check()==z3.unsat
  count+=1
 print(name,'independent exact no cover',count,flush=True)
