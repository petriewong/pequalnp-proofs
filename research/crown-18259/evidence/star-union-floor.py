"""Exact straight-line OR sharing for all-but-one six-atom star sums."""
from functools import lru_cache
from itertools import combinations
G=127
splits={}
for z in range(1,128):
 parts=[x for x in range(1,z) if x&z==x]
 splits[z]=[(a,b) for a,b in combinations(parts,2) if a|b==z]

def canonical(goals):
 return tuple(sorted({m for m in goals if m.bit_count()>1}))

def fn(goals,k,rich=True):
 @lru_cache(None)
 def solve(Q,b):
  if not Q:return True
  if len(Q)>b:return False
  for s in Q:
   if (s.bit_count()-1+sum(t&s!=t for t in Q))>b:return False
  if rich:
   for s,t in combinations(Q,2):
    if (s|t).bit_count()-(1 if s&t else 2)+sum((m&s!=m and m&t!=m) for m in Q)>b:return False
  z=max(Q,key=lambda m:(m.bit_count(),m))
  Q=tuple(m for m in Q if m!=z)
  terms=sorted({canonical((*Q,a,b)) for a,b in splits[z]},key=lambda o:(len(o),sum(x.bit_count() for x in o)))
  return any(solve(w,b-1) for w in terms)
 return solve(canonical(goals),k),solve.cache_info()

if __name__=='__main__':
 for m,k in ((2,6),(3,8),(4,10)):
  Gs=tuple(G^(1<<(3+i)) for i in range(m))
  low,st=fn(Gs,k-1)
  high,st2=fn(Gs,k)
  assert not low and high
  print(m,'star masks',Gs,'minimum OR routing',k,'negative states',st.currsize,'positive states',st2.currsize)
