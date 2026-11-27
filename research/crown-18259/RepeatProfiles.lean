import Std
namespace ProofLantern.Crown.RepeatRecovery
def tag (p : Nat) (r : Bool) : Nat := if r then p%3 else p/3
def swapPair (p : Nat) : Nat := (p%3)*3+p/3
def labs := List.range 4
def lookup (p : List Nat) (i : Nat) (r : Bool) : Nat := tag (p[i]?.getD 0) r
def possibleSide (p : List Nat) (r : Bool) : Bool := labs.all fun i =>
  let me := lookup p i r
  let other := (labs.filter (· != i)).map fun j => lookup p j (!r)
  if me == 2 then !(other.contains 2) && (other.filter (· == 1)).length ≤ 1
  else if me == 1 then (other.filter (· != 0)).length ≤ 2 else true
def tags (p : List Nat) : List Nat := p.flatMap fun a => [tag a false,tag a true]
def prior (p : List Nat) : Bool :=
  ((tags p).filter (· != 0)).length ≥ 3 && (tags p).contains 1 && possibleSide p false && possibleSide p true
def mixed (p : List Nat) : Bool := labs.all fun i => labs.all fun j =>
  let a := lookup p i false
  let b := lookup p j true
  i == j || !((a==1 && b==2) || (a==2 && b==1))
def reciprocal (p : List Nat) : Bool := labs.all fun i => labs.all fun j =>
  let rr := fun a => (p[a]?.getD 0)==4
  !(i != j && rr i && rr j) || labs.all (fun a => a==i || a==j || (p[a]?.getD 0)==0)
def keepAfterErasure (p : List Nat) : Bool :=
  ((tags p).filter (·==0)).length + (((tags p).filter (·==2)).length+1)/2 < 6
def insert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b::bs => if a ≤ b then a::b::bs else b::insert a bs
def sort : List Nat → List Nat
  | [] => []
  | a::as => insert a (sort as)
def lexLT : List Nat → List Nat → Bool
  | [], _::_ => true
  | a::as,b::bs => if a==b then lexLT as bs else decide (a<b)
  | _,[] => false
def frames : List (List Nat) :=
  (List.range 9).flatMap fun a => ((List.range 9).filter (a ≤ ·)).flatMap fun b =>
    ((List.range 9).filter (b ≤ ·)).flatMap fun c =>
      ((List.range 9).filter (c ≤ ·)).map fun d => [a,b,c,d]
def stage0 := frames.filter (fun p => prior p && !(lexLT (sort (p.map swapPair)) p))
def stage1 := stage0.filter mixed
def stage2 := stage1.filter reciprocal
def stage3 := stage2.filter keepAfterErasure
set_option maxRecDepth 40000 in
set_option maxHeartbeats 15000000 in
theorem exact_counts : (stage0.length,stage1.length,stage2.length,stage3.length) = (34,17,15,11) := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 15000000 in
theorem everyRemainingHasFourOrFiveO :
    (stage3.all fun p =>
      let n := ((tags p).filter (·==0)).length
      n == 4 || n == 5) = true := by decide

theorem hidesAtTrue (f : Bool → Bool) (a b : Bool) : f (true || a) = f (true || b) := rfl
theorem twinAbsorption (z v : Bool) : z || (z && v) = z := by cases z <;> rfl
theorem erasureBudget (k removed a : Nat) (hk : k ≤ 22) (hr : removed ≤ k)
    (hdrop : 6 ≤ removed) (ha : a ≤ 6) : k-removed+(a-1) ≤ 21 := by omega
end ProofLantern.Crown.RepeatRecovery
