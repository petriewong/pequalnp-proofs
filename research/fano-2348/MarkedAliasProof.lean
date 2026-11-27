import Init

/- Research lemmas for the flagged Fano wire: no 27-gate exclusion is claimed. -/

namespace ProofLantern.MarkedAlias

/-- Meet every completion with the all-off and all-on extreme assignments
of the two slices to characterize the substituted wire at every input. -/
theorem determined_by_two_rows {X : Type} (flag wire : X → Bool)
    (bottomOn topOff : X)
    (onUpper : ∀ x, flag x = true → wire bottomOn = true → wire x = true)
    (offLower : ∀ x, flag x = false → wire x = true → wire topOff = true)
    (bottomHit : wire bottomOn = true) (topMiss : wire topOff = false) :
    ∀ x, wire x = flag x := by
  intro x
  cases hf : flag x with
  | true => exact onUpper x hf bottomHit
  | false =>
    cases hw : wire x with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (topMiss.symm.trans (offLower x hf hw)))

/-- A bare AND with a universally true other operand on the marked-on
slice can be replaced by the marked input, under the substitution. -/
theorem bare_and_alias {X : Type} (flag other : X → Bool) (bottomOn : X)
    (onUpper : ∀ x, flag x = true → other bottomOn = true → other x = true)
    (bottomHit : other bottomOn = true) :
    ∀ x, (flag x && other x) = flag x := by
  intro x
  cases hf : flag x with
  | false => rfl
  | true => simpa [hf] using onUpper x hf bottomHit

end ProofLantern.MarkedAlias

namespace ProofLantern.TraceSound

def op (isOr a b : Bool) : Bool := if isOr then a || b else a && b
def derivative (isOr a b da db : Bool) : Bool :=
  if isOr then da || db else (a && db) || (da && b)

private theorem step (o a b da db pa pb : Bool)
    (ha : a = true ∨ da = true → pa = true)
    (hb : b = true ∨ db = true → pb = true) :
    op o a b = true ∨ derivative o a b da db = true → op o pa pb = true := by
  cases o <;> cases a <;> cases b <;> cases da <;> cases db <;>
    cases pa <;> cases pb <;> simp_all [op,derivative]

/-- Every singleton base or first-order witness is accepted at the pair. -/
theorem trace_implies_pair (g : Nat → Option (Bool × Nat × Nat))
    (base delta pair : Nat → Bool)
    (leaf : ∀ i, g i = none → (base i = true ∨ delta i = true) → pair i = true)
    (wire : ∀ i o a b, g i = some (o,a,b) → a < i ∧ b < i ∧
      base i = op o (base a) (base b) ∧
      delta i = derivative o (base a) (base b) (delta a) (delta b) ∧
      pair i = op o (pair a) (pair b))
    (i : Nat) : (base i = true ∨ delta i = true) → pair i = true := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
    cases h : g i with
    | none => exact leaf i h
    | some x =>
      obtain ⟨o,a,b⟩ := x
      obtain ⟨ha,hb,hbase,hdelta,hpair⟩ := wire i o a b h
      rw [hbase,hdelta,hpair]
      exact step o (base a) (base b) (delta a) (delta b) (pair a) (pair b)
        (ih a ha) (ih b hb)

/-- In either Boolean orientation, an AND on two traced wires accepts the
pair, regardless of whether its own first-order trace is lost. -/
theorem marked_and_pair (g : Nat → Option (Bool × Nat × Nat))
    (base delta pair : Nat → Bool)
    (leaf : ∀ i, g i = none → (base i = true ∨ delta i = true) → pair i = true)
    (wire : ∀ i o a b, g i = some (o,a,b) → a < i ∧ b < i ∧
      base i = op o (base a) (base b) ∧
      delta i = derivative o (base a) (base b) (delta a) (delta b) ∧
      pair i = op o (pair a) (pair b))
    {i a b : Nat} (andGate : g i = some (false,a,b))
    (da : delta a = true) (db : delta b = true) :
    pair i = true := by
  have ha := trace_implies_pair g base delta pair leaf wire a (Or.inr da)
  have hb := trace_implies_pair g base delta pair leaf wire b (Or.inr db)
  have h := (wire i false a b andGate).2.2.2.2
  simp [h, op, ha, hb]

end ProofLantern.TraceSound
