"""Research model only: row-major 3 x 3 bipartite perfect matching."""
from itertools import permutations
from pathlib import Path
import json
N = 9
ALL = (1 << N) - 1
MIN = sorted(sum(1 << (3*i+p[i]) for i in range(3))
             for p in permutations(range(3)))

def target(s):
    return any((s & u) == u for u in MIN)

MAX = [s for s in range(1 << N) if not target(s)
       and all(target(s | (1 << i)) for i in range(N) if not ((s >> i) & 1))]
BIT = [(x, 1) for x in MIN] + [(x, 0) for x in MAX]

def baseline():
    gates = []
    def emit(op,a,b):
        gates.append([op,a,b])
        return N + len(gates) - 1
    q = []
    for j in range(3):
        a,b = [i for i in range(3) if i != j]
        nc = emit('and',3+a,6+b)
        cr = emit('and',3+b,6+a)
        h = emit('or',nc,cr)
        q.append(emit('and',j,h))
    emit('or', emit('or',q[0],q[1]), q[2])
    return gates

def run(gates, s):
    vals = [(s >> i) & 1 for i in range(N)]
    for op,a,b in gates:
        if op not in ('and','or') or not (0 <= a < len(vals) and 0 <= b < len(vals)):
            raise ValueError((op,a,b))
        vals.append(vals[a] & vals[b] if op=='and' else vals[a] | vals[b])
    return vals[-1]

def verify(gates):
    return all(run(gates,s) == target(s) for s in range(1 << N))

if __name__ == '__main__':
    import sys
    gates = json.loads(Path(sys.argv[1]).read_text()) if len(sys.argv)>1 else baseline()
    assert verify(gates)
    assert all(any(not (s & ~m) for m in MAX) for s in range(1 << N) if not target(s))
    print(f'{len(gates)} gates, all {1<<N} rows check; {len(MIN)} minimal true and {len(MAX)} maximal false rows')
