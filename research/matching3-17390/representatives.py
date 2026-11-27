"""Cone symmetries: row/column permutations, transposition, and a commutative first gate."""
from itertools import permutations,product
P=list(permutations(range(3)))
S=[tuple(3*r[(i%3 if t else i//3)]+c[(i//3 if t else i%3)] for i in range(9))
   for r,c,t in product(P,P,(0,1))]
for shape,y in enumerate((1,4)):
    groups=[]
    for j in range(9):
        if j in (0,y):continue
        orbit={p[j] for p in S if {p[0],p[y]}=={0,y}}
        if j==min(orbit):groups.append(j)
    print(shape,*groups)
