"""Concrete replay of physical gate removal under Crown projections."""
from pathlib import Path
import re
import sys
files=sys.argv[1:] or ['CrownFivePure23.lean','CrownFiveOneDirty25.lean']
N=7
def source(f):
 s=Path(f).read_text()
 gs=[(o,int(a),int(b)) for o,a,b in re.findall(r'⟨\.(or|and),\s*\[(\d+)\s*,\s*(\d+)\]⟩',s)]
 out=int(re.search(r'\],\s*(\d+)\s*⟩',s)[1])
 return gs,out
def ctr(gate,op,c,d):return (c&d) if gate=='and' else (c|d)
def promised(n):return [(1<<u)|(1<<(n+v)) for u in range(n) for v in range(n)]
def check(gs,out,n,rows,wanted):
 for row,win in zip(rows,wanted):
  xs=[(row>>i)&1 for i in range(n)]
  for o,a,b in gs:xs.append(ctr(o,0,xs[a],xs[b]))
  assert xs[out]==win
def shrink(gs,out,newN,mapping,rows,semantic):
 zero=-1
 valves={i:u for i,u in enumerate(mapping)}
 masks={j:sum(1<<k for k,r in enumerate(rows) if r>>j&1) for j in range(newN)}
 masks[zero]=0
 got={m:k for k,m in masks.items()}
 ng=[]
 for i,(o,x,y) in enumerate(gs):
  a,b=valves[x],valves[y]
  if a==b:t=a
  elif a==zero or b==zero:t=zero if o=='and' else (b if a==zero else a)
  else:
   val=ctr(o,0,masks[a],masks[b])
   if semantic and val in got:t=got[val]
   else:
    t=newN+len(ng);ng.append((o,a,b));masks[t]=val
    got.setdefault(val,t)
  valves[2*N+i]=t
 result=valves[out]
 live=set()
 def visit(i):
  if i<newN or i in live:return
  live.add(i)
  _,a,b=ng[i-newN]
  visit(a);visit(b)
 visit(result)
 mp={i:i for i in range(newN)};really=[]
 for j,(o,a,b) in enumerate(ng,newN):
  if j not in live:continue
  mp[j]=len(really)+newN
  really.append((o,mp[a],mp[b]))
 return really,mp[result]
def score(g):return (len(g),sum(o=='and' for o,_,_ in g))
for f in files:
 g,o=source(f)
 check(g,o,2*N,promised(N),[i!=j for i in range(N) for j in range(N)])
 maps=list(range(7))*2; full=list(range(128)); t=[x.bit_count()>1 for x in full]
 pair=[]
 for sem in [False,True]:
  u,v=shrink(g,o,7,maps,full,sem)
  check(u,v,7,full,t);pair.append(score(u))
 six=[]
 for cut in range(7):
  maps=[-1 if i%7==cut else i-(i//7)-int(i%7>cut) for i in range(14)]
  # When removing each matched pair, raw half 2 begins at index 6.
  assert sorted(x for x in maps if x>=0)==list(range(12)),maps
  rows=promised(6);t=[i!=j for i in range(6) for j in range(6)]
  t1,v=shrink(g,o,12,maps,rows,True);check(t1,v,12,rows,t);six.append(score(t1))
 print(f, 'raw',score(g),'identify syntactic/semantic',pair,'vertex deletion',six)
