"""Generate independent Lean BitVec checks for necessary star support networks."""
from pathlib import Path
def conj(xs):
 if not xs:return 'true'
 if len(xs)==1:return '('+xs[0]+')'
 t=len(xs)//2
 return '('+conj(xs[:t])+' && '+conj(xs[t:])+')'
def orr(xs):
 return '('+' || '.join(xs)+')'
for m,k,allow in [(3,7,0),(4,9,0),(3,8,1),(4,8,1),(4,9,1)]:
 name=f'Star{m}At{k}With{allow}AND'
 w=[f'{v}#7' for v in [0,1,2,4,8,16,32,64]]
 properties=[]
 for i in range(k):
  j=len(w)
  properties.extend([f'!(r{i}.ult l{i})',f'r{i}.ult {j}#5'])
  for q,x in enumerate(w):
   properties += [f'(l{i} != {q}#5 || a{i} == {x})', f'(r{i} != {q}#5 || b{i} == {x})']
  t=f'(if o{i} then a{i} ||| b{i} else a{i} &&& b{i})' if allow else f'(a{i} ||| b{i})'
  properties.append(f'g{i} == {t}')
  w.append(f'g{i}')
 if allow:
  cost=' + '.join(f'(if o{i} then 0#4 else 1#4)' for i in range(k))
  properties.append(f'({cost}) == 1#4')
 for j in range(m):
  z=127^(1<<(3+j))
  properties.append(orr([f'({u} == {z}#7)' for u in w]))
 parts=['import Std.Tactic.BVDecide',f'namespace ProofLantern.Crown.{name}',
        'set_option maxHeartbeats 0 in','set_option maxRecDepth 100000 in','theorem noModel',
        '    ('+' '.join(f'{v}{j}' for v in 'lr' for j in range(k))+' : BitVec 5)',
        '    ('+' '.join(f'{v}{j}' for v in 'abg' for j in range(k))+' : BitVec 7)']
 if allow:parts.append('    ('+' '.join(f'o{j}' for j in range(k))+' : Bool)')
 parts[-1]+=' :'
 parts.append('  '+conj(properties).replace(' && ',' &&\n    ')+' = false := by')
 parts+=['    bv_decide (config := { timeout := 150 })',f'end ProofLantern.Crown.{name}']
 Path('inputs/'+name+'.lean').write_text('\n'.join(parts)+'\n')
