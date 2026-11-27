"""Create independent certificates for the fanout-component lower bound."""
from itertools import combinations
from check_matching import target
from pathlib import Path

def related(i,j):
    return i//3==j//3 or i%3==j%3

def assign(i,j,p):
    return ((p&1)<<i)|((p>>1)<<j)

def row(i,j,s):
    return tuple(int(target(s|assign(i,j,p))) for p in range(4))

clashes=[]
ranks=[]
for i,j in combinations(range(9),2):
    others=[x for x in range(9) if x not in (i,j)]
    pair=(1<<i)|(1<<j)
    if not related(i,j):
        witness={}
        for s in range(512):
            if not s&pair:witness.setdefault(row(i,j,s),s)
        clashes.append((i,j,witness[(0,0,0,1)],witness[(0,1,1,1)]))
    else:
        for x,y in combinations(others,2):
            free=(1<<x)|(1<<y)
            for s in range(512):
                if s&(pair|free):continue
                f=[sum(int(target(s|assign(i,j,p)|assign(x,y,q)))<<q for q in range(4))
                   for p in range(4)]
                if len(set(f))>=3:
                    ranks.append((i,j,x,y,s))
                    break
            else:
                raise AssertionError((i,j,x,y))

from collections import Counter
print("Disjoint-pair conflicts:",len(clashes))
print("Adjacent-pair rank tests with five fixed edges:",len(ranks))
assert len(clashes)==18 and len(ranks)==378
assert Counter((i,j) for i,j,_,_,_ in ranks).values()
assert set(Counter((i,j) for i,j,_,_,_ in ranks).values())=={21}

def lean_list(a):
    return '[\n  '+',\n  '.join(', '.join('⟨'+', '.join(map(str,z))+'⟩' for z in a[i:i+4]) for i in range(0,len(a),4))+'\n  ]'
text='''import Std

namespace ProofLantern.MatchingComponents

def pm (s : Nat) : Bool :=
  (s.testBit 0 && s.testBit 4 && s.testBit 8) ||
  (s.testBit 0 && s.testBit 5 && s.testBit 7) ||
  (s.testBit 1 && s.testBit 3 && s.testBit 8) ||
  (s.testBit 1 && s.testBit 5 && s.testBit 6) ||
  (s.testBit 2 && s.testBit 3 && s.testBit 7) ||
  (s.testBit 2 && s.testBit 4 && s.testBit 6)

def pmIndependent (s : Nat) : Bool :=
  (List.range 3).any fun a => (List.range 3).any fun b => (List.range 3).any fun c =>
    a != b && b != c && a != c && s.testBit a && s.testBit (3+b) && s.testBit (6+c)

set_option maxRecDepth 60000 in
set_option maxHeartbeats 30000000 in
theorem matching_definition_checked :
    ∀ s : Fin 512, pm s.val = pmIndependent s.val := by decide

def near (i j : Nat) : Bool := i/3 == j/3 || i%3 == j%3

def code (i j p : Nat) : Nat := (p%2)*2^i + (p/2)*2^j

structure Clash where
  i : Nat
  j : Nat
  bodyAnd : Nat
  bodyOr : Nat

structure RankExample where
  i : Nat
  j : Nat
  freeA : Nat
  freeB : Nat
  baseline : Nat

def clashExamples : List Clash := CLASHES

def rankExamples : List RankExample := RANKS

def primaries : List Nat := List.range 9

def pairs : List (Nat × Nat) :=
  primaries.flatMap fun i => (primaries.filter (fun j => i < j)).map fun j => (i,j)

def expectedClashes : List (Nat × Nat) :=
  pairs.filter fun p => !(near p.1 p.2)

def expectedRanks : List (Nat × Nat × Nat × Nat) :=
  (pairs.filter fun p => near p.1 p.2).flatMap fun (i,j) =>
    (pairs.filter fun (a,b) => a != i && a != j && b != i && b != j).map fun (a,b) => (i,j,a,b)

def clashOK (w : Clash) : Bool :=
  w.bodyAnd < 512 && w.bodyOr < 512 &&
  !w.bodyAnd.testBit w.i && !w.bodyAnd.testBit w.j &&
  !w.bodyOr.testBit w.i && !w.bodyOr.testBit w.j &&
  ((List.range 4).all fun p =>
    (pm (w.bodyAnd + code w.i w.j p) == (p == 3)) &&
    (pm (w.bodyOr + code w.i w.j p) == (p != 0)))

def rankSignature (w : RankExample) (p : Nat) : List Bool :=
  (List.range 4).map fun q => pm (w.baseline + code w.i w.j p + code w.freeA w.freeB q)

def rankOK (w : RankExample) : Bool :=
  w.baseline < 512 &&
  !w.baseline.testBit w.i && !w.baseline.testBit w.j &&
  !w.baseline.testBit w.freeA && !w.baseline.testBit w.freeB &&
  3 <= (((List.range 4).map (rankSignature w)).eraseDups.length)

-- These are finite component-separation facts, not a formal gate lower-bound theorem.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem checked : (clashExamples.map (fun w => (w.i,w.j))) = expectedClashes ∧
    (rankExamples.map (fun w => (w.i,w.j,w.freeA,w.freeB))) = expectedRanks ∧
    clashExamples.all clashOK = true ∧ rankExamples.all rankOK = true := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  decide

end ProofLantern.MatchingComponents
'''
Path('MatchingComponentChecks.lean').write_text(text.replace('CLASHES',lean_list(clashes)).replace('RANKS',lean_list(ranks)))
