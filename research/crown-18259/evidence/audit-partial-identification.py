"""Independent exhaustive orientation audit on validated Crown controls."""
from pathlib import Path
from itertools import permutations
import re
names=['Crown23.lean','Crown23Cuts.lean','Crown23FourCuts.lean','Crown23RawFour.lean','CrownFivePure23.lean',
       'Crown24Exception.lean','Crown24DirtyFour.lean','Crown24TwoDirty.lean','CrownFiveOneDirty25.lean','CrownThreeDirtyControl31.lean']
def source(name):
 text=Path('inputs/'+name).read_text()
 gates=[(o,int(a),int(b)) for o,a,b in re.findall(r'⟨\.(or|and),\s*\[(\d+)\s*,\s*(\d+)\]⟩',text)]
 out=int(re.search(r'\],\s*(\d+)\s*⟩',text)[1])
 return gates,out
def act(op,a,b):return a|b if op=='or' else a&b
want=sum(1<<x for x in range(128) if x.bit_count()>1)
base=[sum(1<<x for x in range(128) if x>>i&1) for i in range(7)]
for name in names:
 g,out=source(name)
 reads=[sum(a==i or b==i for _,a,b in g) for i in range(14)]
 pure={min(a,b) for o,a,b in g if o=='or' and abs(a-b)==7 and a<14 and b<14 and reads[a]==reads[b]==1}
 counts=[]
 for i,j in permutations(range(7),2):
  masks=[0 if k in (i,j+7) else base[k%7] for k in range(14)]
  alias={k:(-1 if q==0 else k%7) for k,q in enumerate(masks)}
  first={q:k for k,q in enumerate(base)};first[0]=-1
  reps={}
  for k,(o,a,b) in enumerate(g,14):
   q=act(o,masks[a],masks[b]);masks.append(q)
   alias[k]=first.setdefault(q,k)
   if alias[k]==k:reps[k]=o,alias[a],alias[b]
  kept=set()
  def visit(k):
   if k in reps and k not in kept:
    kept.add(k);_,a,b=reps[k];visit(a);visit(b)
  visit(alias[out])
  assert masks[out]==want
  counts.append(len(kept))
 print(name,'gates',len(g),'pure',len(pure),'all42 projections correct','kept',min(counts),max(counts))
