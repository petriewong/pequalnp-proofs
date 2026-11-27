"""Independent proposition generator for all three first-pair orbits."""
from itertools import combinations
from pathlib import Path
def fold(arr, op, comp):
 if not arr:return comp
 if len(arr)==1:return '('+arr[0]+')'
 u=len(arr)//2
 return '('+fold(arr[:u],op,comp)+' '+op+' '+fold(arr[u:],op,comp)+')'
def AND(xs):return fold(xs,'&&','true')
def OR(xs):return fold(xs,'||','false')
def impl(a,b):return f'(!({a}) || ({b}))'
def eq(a,b):return f'({a} == {b})'
def ne(a,b):return f'({a} != {b})'
e=[(i,j) for i,j in combinations(range(7),2) if i<3]
K,N,W=10,7,22
basis=[(1<<i)|sum(1<<(7+j) for j,p in enumerate(e) if i in p) for i in range(N)]
edge=(1<<W)-128
targ=[edge|(127^(1<<i)) for i in range(3,7)]
target=[f'{i}#22' for i in targ]
for o,(p,q) in enumerate([(0,1),(0,3),(3,4)]):
 nm=f'StarResidualTwoHelper{o}'
 names=[f'g{i}' for i in range(K)]
 wires=[f'{m}#22' for m in basis]+names
 a=[eq('l0',f'{p}#5'),eq('r0',f'{q}#5'),'on0','on1','op0','op1',
    'u.ult v','v.ult 17#5','!(u.ult 7#5)',eq('(leftOut &&& rightOut)',f'{edge}#22')]
 for i in range(K):
  n=N+i
  a += [f'l{i}.ult r{i}',f'r{i}.ult {n}#5']
  a += [impl(eq(f'l{i}',f'{j}#5'),eq(f'a{i}',w)) for j,w in enumerate(wires[:n])]
  a += [impl(eq(f'r{i}',f'{j}#5'),eq(f'b{i}',w)) for j,w in enumerate(wires[:n])]
  a += [eq(f'g{i}',f'(if on{i} then (if op{i} then a{i} ||| b{i} else a{i} &&& b{i}) else 0#22)'),
        impl(f'on{i}',AND([ne(f'g{i}','0#22')]+[ne(f'g{i}',v) for v in wires[:n]])),
        impl(f'(on{i} && !op{i})',ne(f'(g{i} &&& 127#22)','0#22')),
        impl(OR([eq(f'g{i}',t) for t in target]),f'op{i}')]
  if i>0:a.append(impl(f'on{i}',f'on{i-1}'))
  if i>1:
   a.append(impl(AND([f'on{i}',eq(f'op{i}',f'op{i-1}'),f'r{i}.ult {n-1}#5']),f'!(r{i}.ult r{i-1})'))
  use=[AND([f'on{j}',OR([eq(f'l{j}',f'{n}#5'),eq(f'r{j}',f'{n}#5')])]) for j in range(i+1,K)]
  a.append(impl(f'on{i}',OR([eq('u',f'{n}#5'),eq('v',f'{n}#5')]+use+[eq(f'g{i}',t) for t in target])))
  a += [impl(eq('u',f'{n}#5'),eq('leftOut',f'g{i}')),impl(eq('v',f'{n}#5'),eq('rightOut',f'g{i}'))]
 c=' + '.join(f'(if on{i} && !op{i} then 1#4 else 0#4)' for i in range(K))
 a.append(eq(f'({c})','2#4'))
 a += [OR([eq(w,t) for w in names]) for t in target]
 txt=['import Std.Tactic.BVDecide',f'namespace ProofLantern.Crown.{nm}',
      'set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in',
      'theorem noModel',
      '    (u v '+' '.join(f'{r}{i}' for r in 'lr' for i in range(K))+' : BitVec 5)',
      '    (leftOut rightOut '+' '.join(f'{xy}{i}' for xy in 'abg' for i in range(K))+' : BitVec 22)',
      '    ('+' '.join(f'{b}{i}' for b in ('on','op') for i in range(K))+' : Bool) :',
      '  '+AND(a).replace(' && ',' &&\n    ')+' = false := by',
      '  bv_decide (config := { timeout := 150 })',
      f'end ProofLantern.Crown.{nm}']
 Path('inputs/'+nm+'.lean').write_text('\n'.join(txt)+'\n')
