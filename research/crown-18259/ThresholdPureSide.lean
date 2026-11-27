import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.PureSide

def one {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)
def two {n : Nat} (i j : Fin n) : Fin n → Bool := fun k => decide (k = i ∨ k = j)
def rawDisjunction {n : Nat} (support : Fin n → Prop) (x : Fin n → Bool) : Prop :=
  ∃ i, support i ∧ x i = true

/-- A pure side of a final AND for threshold two can miss at most one variable. -/
theorem missesAtMostOne {n : Nat} {support : Fin n → Prop}
    (allPairs : ∀ i j, i ≠ j → rawDisjunction support (two i j))
    {i j : Fin n} (hi : ¬support i) (hj : ¬support j) : i = j := by
  by_contra ne
  obtain ⟨k,hk,yes⟩ := allPairs i j ne
  simp [two] at yes
  rcases yes with rfl | rfl
  · exact hi hk
  · exact hj hk

/-- If the other operand accepts a singleton, the pure side misses exactly that singleton. -/
theorem pureSideSupport {n : Nat} {support : Fin n → Prop}
    {other : (Fin n → Bool) → Prop}
    (single : ∀ i, ¬(rawDisjunction support (one i) ∧ other (one i)))
    (allPairs : ∀ i j, i ≠ j → rawDisjunction support (two i j))
    (w : Fin n) (yes : other (one w)) :
    ∀ j, support j ↔ j ≠ w := by
  have hw : ¬support w := by
    intro h
    exact single w ⟨⟨w,h,by simp [one]⟩,yes⟩
  intro j
  constructor
  · intro hj eq
    exact hw (eq ▸ hj)
  · intro ne
    by_contra no
    exact ne (missesAtMostOne allPairs no hw)

/-- Replacing the pure operand by true preserves the other operand's behavior on every nonzero
input away from the missing coordinate. This is semantic only; no gate saving is asserted. -/
theorem pureSideReplaceOnNonzero {n : Nat} {support : Fin n → Prop}
    {other : (Fin n → Bool) → Prop} {w : Fin n}
    (exactSupport : ∀ j, support j ↔ j ≠ w) {x : Fin n → Bool}
    (deleted : x w = false) (nonzero : ∃ j, x j = true) :
    (rawDisjunction support x ∧ other x) ↔ other x := by
  constructor
  · exact And.right
  · intro ho
    obtain ⟨j,hj⟩ := nonzero
    have ne : j ≠ w := by
      intro eq
      subst j
      exact Bool.noConfusion (deleted.symm.trans hj)
    exact ⟨⟨j,(exactSupport j).2 ne,hj⟩,ho⟩

/-- Each atom of the other OR side can accept only the missing singleton. -/
theorem otherAtomsSingleton {n : Nat} {support : Fin n → Prop}
    {other atom : (Fin n → Bool) → Prop} {i w : Fin n}
    (single : ∀ i, ¬(rawDisjunction support (one i) ∧ other (one i)))
    (exactSupport : ∀ j, support j ↔ j ≠ w)
    (part : ∀ x, atom x → other x) (yes : atom (one i)) : i = w := by
  by_contra ne
  exact single i ⟨⟨i,(exactSupport i).2 ne,by simp [one]⟩,part _ yes⟩

end ProofLantern.Crown.PureSide
