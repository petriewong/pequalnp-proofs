from baseline import N,build
from tag_query import run
standard,out=build(tuple(range(7)),N)
assert out==40
g=[]
def add(op,a,b):
    g.append((op,a,b));return 13+len(g)
terms=[]
for c in range(7):
    a,b,z=N[c]
    term=add('and',c,add('or',add('or',a,b),z))
    if c==0:
        g0=term
        term=add('or',add('and',g0,7),add('and',g0,0))
    terms.append(term)
out=terms[0]
for t in terms[1:]:
    out=add('or',out,t)
assert out==43
assert run(27,5000,standard)=='unsat'
assert run(30,5000,g)=='sat'
print('passed fixed no-motif and motif controls')
