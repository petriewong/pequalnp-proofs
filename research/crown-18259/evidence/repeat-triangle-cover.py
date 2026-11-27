"""Exact six-atom OR-tree replay for the two three-repeat/one-AND profiles."""
from functools import lru_cache
from itertools import combinations
N=7
full=sum(1<<(7*i+j) for i in range(N) for j in range(N) if i!=j)
def atom(name):
 if name[0]=='p':
  k=int(name[1]);return sum(1<<(7*i+j) for i in range(7) for j in range(7) if i==k or j==k)
 if name[0]=='x':return 127<<(7*int(name[1]))
 return sum(1<<(7*i+int(name[1])) for i in range(7))
def submasks(v):
 s=(v-1)&v
 while s:
  yield s;s=(s-1)&v
@lru_cache(None)
def trees(v):
 if v.bit_count()==1:return ((),)
 return tuple(tuple(sorted((*a,*b,v))) for u in submasks(v) if u&(v&-v)
              for a in trees(u) for b in trees(v^u))

U=['p0','p1','p2','y4','y5','y6']
u=[atom(x) for x in U]
unions=[0]*64
for i in range(1,64): unions[i]=unions[i&(i-1)]|u[(i&-i).bit_length()-1]
star=atom('x3')&unions[63]
assert star and not star&~full
rem=full&~star
def check(r,allowed,cap):
 pop=len(trees(63));n=0
 for t in trees(63):
  w=[atom(x) for x in allowed]+[atom(a)|atom(b) for a,b in combinations(r,2)]+[unions[x] for x in t]
  cuts=set()
  for a,b in combinations(w,2):
   v=a&b
   if v and not (v&~full) and v&rem:cuts.add(v&rem)
  cuts=[x for x in cuts if not any(x!=y and x&y==x for y in cuts)]
  table={1<<i:tuple(x for x in cuts if x&(1<<i)) for i in range(49) if rem>>i&1}
  @lru_cache(None)
  def cover(s,b):
   if not s:return True
   if not b:return False
   if max(((x&s).bit_count() for x in cuts),default=0)*b<s.bit_count():return False
   choices=min((v for k,v in table.items() if k&s),key=len)
   return any(cover(s&~q,b-1) for q in choices)
  n+=1
  if cover(rem,cap):return n,'FOUND_RELAXED_COVER',t
 return n,'no cover',None
ts=trees(63)
assert len(ts)==len(set(ts))==945
for name,r,allowed in [
 ('AO,RO,RO,RO',('x4','x5','x6'),U+['y3']),
 ('AR,OO,RO,RO',('x5','x6','y3'),U+['x4'])]:
 print(name,check(r,allowed,5),flush=True)
