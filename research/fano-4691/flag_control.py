from baseline import N,goal,sig
g=[]
def add(op,a,b):
    assert a!=b and max(a,b)<14+len(g)
    g.append((op,a,b));return 13+len(g)
terms=[]
for c in range(7):
    a,b,z=N[c]
    term=add('and',c,add('or',add('or',a,b),z))
    if c==0:
        shared=term
        pointblocked=add('and',shared,7)
        lineblocked=add('and',shared,0)
        term=add('or',pointblocked,lineblocked)
    terms.append(term)
out=terms[0]
for t in terms[1:]:out=add('or',out,t)
ws=list(sig); deps=[set() for _ in ws]
for op,a,b in g:
    deps.append({a,b}|deps[a]|deps[b])
    ws.append(ws[a]&ws[b] if op=='and' else ws[a]|ws[b])
assert len(g)==30 and ws[out]==goal
def val(w,row):return bool(ws[w]>>row&1)
def pure(w):
    assert g[w-14][0]=='and'
    return val(w,129) and not val(w,1) and not val(w,128)
assert all(pure(t) for t in (shared,pointblocked,lineblocked))
for t,r in ((pointblocked,1),(lineblocked,128)):
    assert shared in deps[t] and t in deps[out]
    assert all(not val(x,r) for x in g[t-14][1:])
assert pointblocked not in deps[lineblocked] and lineblocked not in deps[pointblocked]
print('flag motif satisfied with',len(g),'gates; full',1<<14,'truth rows agree')
