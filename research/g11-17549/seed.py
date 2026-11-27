from itertools import combinations,product
from pathlib import Path
E=[(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
P=[(1<<x)|(1<<y) for x,y in E]
N=[m for m in range(2048) if not any(m&p==p for p in P)
  and all(any((m|(1<<w))&p==p for p in P) for w in range(11) if not m>>w&1)]
assert len(P)+len(N)<=64
rows=P+N
I=[sum(1<<i for i,r in enumerate(rows) if r>>x&1) for x in range(11)]
C=[set(c) for c in combinations(range(11),7) if all(set(e)&set(c) for e in E)]
assert all(not all(set(e)&set(c) for e in E) for c in combinations(range(11),6))
seeds=[]
for cover in C:
  for stars in product(*(sorted(set(e)&cover) for e in E)):
    centers={j:[] for j in cover}
    if set(stars)!=cover: continue
    for (x,y),j in zip(E,stars): centers[j].append(x if x!=j else y)
    gates=[]
    def g(a,b,or_op):
        gates.append((a,b,or_op));return 10+len(gates)
    roots=[]
    for j,leaves in sorted(centers.items()):
        a=leaves[0]
        for b in leaves[1:]: a=g(a,b,1)
        roots.append(g(j,a,0))
    a=roots[0]
    for b in roots[1:]: a=g(a,b,1)
    assert a==32 and len(gates)==22
    wire=I.copy()
    for a,b,o in gates: wire.append(wire[a]|wire[b] if o else wire[a]&wire[b])
    assert wire[-1]==(1<<len(P))-1
    seeds.append(gates)
Path('oracle.txt').write_text(' '.join(map(str,I+[len(P),len(rows),len(seeds)]))+'\n'+'\n'.join(' '.join(str(x) for g in s for x in g) for s in seeds)+'\n')
print('positives',len(P),'maximal negatives',len(N),'minimum covers',len(C),'22-gate verified seeds',len(seeds))
