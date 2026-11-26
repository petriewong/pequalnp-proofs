from cegis_query import run
from baseline import goal,N,build
from boundary import edge_rows,maximal

first=[(0,1),(0,2),(0,7),(0,8),(0,11),(1,2),(1,3),(1,8),(1,9),(1,11),(2,4),(2,6),(2,8),(2,10)]
seed={1,128,129,130,258,260,127,244,361,480,1539,2126,2376,10250}
boundary=set(edge_rows+maximal+[1,128])
assert seed<=boundary

def replay(model,rows):
    g,pi,lj=model
    out=13+len(g)
    cone=[set() for _ in range(14)]
    for op,a,b in g:
        assert op in ('and','or') and 0<=a<b<len(cone)
        cone.append({a,b}|cone[a]|cone[b])
    assert pi!=lj and pi in cone[out] and lj in cone[out] and pi not in cone[lj] and lj not in cone[pi]
    def ev(r):
        vals=[bool(r&(1<<i)) for i in range(14)]
        for op,a,b in g:
            vals.append(vals[a] and vals[b] if op=='and' else vals[a] or vals[b])
        return vals
    zero,seven,pair=(ev(r) for r in (1,128,129))
    def pure(i):return i>=14 and g[i-14][0]=='and' and pair[i] and not zero[i] and not seven[i]
    for w,blocked in ((pi,zero),(lj,seven)):
        assert pure(w) and any(map(pure,cone[w]))
        assert all(not blocked[a] for a in g[w-14][1:])
    return {r for r in rows if ev(r)[out]!=bool((goal>>r)&1)}

def control():
    flat,out=build(tuple(range(7)),N)
    # The standard 27-gate circuit computes incidence but has no flagged motif.
    assert run(27,5000,flat,seed,details=True)[0]=='unsat'
    g=[]
    def add(op,a,b):
        g.append((op,a,b));return 13+len(g)
    terms=[]
    for c in range(7):
        a,b,z=N[c]
        term=add('and',c,add('or',add('or',a,b),z))
        if c==0:
            term=add('or',add('and',term,7),add('and',term,0))
        terms.append(term)
    out=terms[0]
    for t in terms[1:]:out=add('or',out,t)
    status,model=run(30,5000,g,seed,details=True)
    assert status=='sat' and not replay(model,range(1<<14))
    print('fixed controls independently replayed',flush=True)

if __name__=='__main__':
    control()
    rows=set(seed)
    for attempt in range(4):
        status,model=run(27,20000,rows=rows,first_pairs=first,details=True)
        if status!='sat':break
        bad=replay(model,boundary)
        if not bad:
            assert not replay(model,range(1<<14))
            print('candidate full-table verified',model,flush=True)
            break
        assert not (bad&rows)
        rows |= bad
        print('rejected relaxed candidate: added',len(bad),'violated rows; now',len(rows),flush=True)
