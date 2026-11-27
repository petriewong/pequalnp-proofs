import Std

namespace ProofLantern.Crown.CleanAndTerminal

structure Wire where
  clean : Bool
  value : Bool
  deriving Inhabited

structure Gate where
  clean : Bool
  isAnd : Bool
  lhs : Nat
  rhs : Nat

def earlier (seen : List Wire) (i : Nat) : Wire := seen[i]?.getD ⟨false,false⟩
def read (seen : List Wire) (i : Nat) : Bool :=
  let w := earlier seen i
  if w.clean then false else w.value

def eval (seen : List Wire) (g : Gate) : Bool :=
  if g.isAnd then (read seen g.lhs) && (read seen g.rhs) else (read seen g.lhs) || (read seen g.rhs)

def legal (seen : List Wire) : List Gate → Prop
  | [] => True
  | g :: gs =>
    (g.clean = true → g.isAnd = false →
      (earlier seen g.lhs).clean = true ∧ (earlier seen g.rhs).clean = true) ∧
    legal (seen ++ [⟨g.clean,eval seen g⟩]) gs

def report (andOnly : Bool) (seen : List Wire) : List Gate → Bool
  | [] => false
  | g :: gs =>
    ((g.clean && (!andOnly || g.isAnd)) && (eval seen g)) ||
    report andOnly (seen ++ [⟨g.clean,eval seen g⟩]) gs

theorem erase_terminal_clean_ors (seen : List Wire) (gates : List Gate) (ok : legal seen gates) :
    report false seen gates = report true seen gates := by
  induction gates generalizing seen with
  | nil => rfl
  | cons g gs ih =>
    change (g.clean = true → g.isAnd = false →
      (earlier seen g.lhs).clean = true ∧ (earlier seen g.rhs).clean = true) ∧
      legal (seen ++ [⟨g.clean,eval seen g⟩]) gs at ok
    have H := ih (seen ++ [⟨g.clean,eval seen g⟩]) ok.2
    simp only [report,H]
    cases hc : g.clean <;> cases ha : g.isAnd
    · simp
    · simp
    · have parents := ok.1 hc ha
      simp [ha,eval,read,parents.1,parents.2]
    · simp

theorem saving_four_pair_budget (size helpers : Nat) (h₁ : size ≤ 22)
    (h₂ : helpers ≤ 6) (h₃ : 6 ≤ size) :
    size - 6 + (helpers-1) ≤ 21 := by omega

theorem saving_three_pair_or_budget (size helpers : Nat) (h₁ : size ≤ 22)
    (h₂ : helpers ≤ 7) (h₃ : 7 ≤ size) :
    size - 7 + (helpers-1) ≤ 21 := by omega

end ProofLantern.Crown.CleanAndTerminal
