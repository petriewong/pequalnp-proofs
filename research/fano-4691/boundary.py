from collections import Counter
from baseline import E,goal,N
n=14
top=(1<<n)-1
edge_rows=sorted((1<<a)|(1<<b) for a,b in E)
negative=[r for r in range(1<<n) if not ((goal>>r)&1)]
maximal=[r for r in negative if all(r>>x&1 or goal>>(r|(1<<x))&1 for x in range(n))]
assert {r for r in range(1<<n) if any(r&e==e for e in edge_rows)}==set(range(1<<n))-set(negative)
assert {r for r in range(1<<n) if any(r&m==r for m in maximal)}==set(negative)
assert not set(edge_rows)&set(maximal)
assert all(r==top or (r&~top)==0 for r in maximal)
print('positive minimal',len(edge_rows),'negative maximal',len(maximal),
      'boundary total',len(edge_rows)+len(maximal),'maximal sizes',dict(sorted(Counter(r.bit_count() for r in maximal).items())))
print('negative masks:',','.join(map(hex,maximal)))
