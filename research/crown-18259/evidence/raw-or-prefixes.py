from functools import lru_cache
options=[(n,t) for n in range(1,8) for t in ([0] if n<3 else [0,1])]
@lru_cache(None)
def parts(n,idx):
 if n==0:return ((),)
 return tuple((p,)+r for j,p in enumerate(options[idx:],idx) if p[0]<=n for r in parts(n-p[0],j))
all=[]
for g in parts(7,0):
 edges=[]
 label=0
 for n,cycle in g:
  edges.extend((label+i,label+i+1) for i in range(n-1))
  if cycle:edges.append((label,label+n-1))
  label+=n
 if edges:all.append((g,tuple(sorted(edges))))
all.sort(key=lambda p:(-len(p[1]),p[0]))
if __name__=='__main__':
 for i,(g,es) in enumerate(all):print(i,g,es)
 print('total',len(all))
