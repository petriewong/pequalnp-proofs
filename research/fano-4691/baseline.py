from itertools import combinations, permutations
P=range(7)
E={(p,l+7) for l in P for p in (l,(l+1)%7,(l+3)%7)}
N={c:sorted(b if a==c else a for a,b in E if c in (a,b)) for c in range(14)}
assert len(E)==21 and all(len(n)==3 for n in N.values())
assert all(len(set(N[a])&set(N[b]))<=1 for a,b in combinations(range(14),2))
cover=[s for s in combinations(range(14),7) if all(a in s or b in s for a,b in E)]
assert cover==[tuple(range(7)),tuple(range(7,14))]
# Since the seven diagonal edges form a matching, no smaller cover is possible.
sig=[sum(1<<r for r in range(1<<14) if (r>>i)&1) for i in range(14)]
goal=0
for a,b in E:goal |= sig[a]&sig[b]
def build(centres, neighbour_order):
    g=[]
    def add(op,a,b):
        assert a!=b and max(a,b)<14+len(g)
        g.append((op,a,b));return 13+len(g)
    terms=[]
    for c in centres:
        a,b,z=neighbour_order[c]
        terms.append(add('and',c,add('or',add('or',a,b),z)))
    out=terms[0]
    for term in terms[1:]: out=add('or',out,term)
    assert len(g)==27
    return g,out
def verify(g,out):
    w=list(sig)
    anc=[set() for i in w]
    for op,a,b in g:
        anc.append({a,b}|anc[a]|anc[b])
        w.append(w[a]&w[b] if op=='and' else w[a]|w[b])
    assert w[out]==goal
    licensed=[i for i in sorted(anc[out]|{out}) if i>=14 and g[i-14][0]=='and' and (w[i]>>129)&1]
    assert len(licensed)==1
    i=licensed[0]
    operands=g[i-14][1:]
    assert not (all(not ((w[r]>>1)&1) for r in operands) and all(not ((w[r]>>128)&1) for r in operands))
stats=0
for side in cover:
    for ordering in permutations(N[side[0]]):
        neigh=N|{side[0]:ordering}
        for order in (side,side[::-1],side[1:]+side[:1]):
            verify(*build(order,neigh))
            stats+=1
print('verified Fano witnesses:',stats,'inputs per witness:',1<<14,'7-vertex covers:',cover)
