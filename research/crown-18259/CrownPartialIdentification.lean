import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.PartialIdentification

def one {n : Nat} (i : Fin n) : Fin n → Bool := fun k => decide (k=i)
def pair {n : Nat} (i j : Fin n) : Fin n → Bool := fun k => decide (k=i ∨ k=j)
def mask {n : Nat} (keep x : Fin n → Bool) : Fin n → Bool := fun k => keep k && x k
def below {n : Nat} (x y : Fin n → Bool) : Prop := ∀ k, x k = true → y k = true

variable {n : Nat}
variable (f : (Fin n → Bool) → (Fin n → Bool) → Bool)
variable (mono : ∀ a b c d, below a c → below b d → f a b = true → f c d = true)
variable (crown : ∀ i j, f (one i) (one j) = decide (i ≠ j))
variable (keepL keepR : Fin n → Bool)
include mono crown

/-- Dropping either coordinate of a flagged pair cannot create a true singleton. -/
theorem singleton_false (i : Fin n) :
    f (mask keepL (one i)) (mask keepR (one i)) = false := by
  cases h : f (mask keepL (one i)) (mask keepR (one i)) with
  | false => rfl
  | true =>
    have belowMask (a : Fin n → Bool) : below (mask a (one i)) (one i) := by
      intro k hk
      exact (Bool.and_eq_true_iff.mp hk).2
    have bad := mono _ _ _ _ (belowMask keepL) (belowMask keepR) h
    simp [crown] at bad

/-- Two marked indices are true if they admit any surviving off-diagonal orientation. -/
theorem pair_true (i j : Fin n) (hne : i ≠ j)
    (survives : ((keepL i && keepR j) || (keepL j && keepR i)) = true) :
    f (mask keepL (pair i j)) (mask keepR (pair i j)) = true := by
  have p₁ (m : Fin n → Bool) (h : m i = true) : below (one i) (mask m (pair i j)) := by
    intro k hk
    have e : k=i := by simpa [one] using hk
    subst k
    simp [mask,pair,h]
  have p₂ (m : Fin n → Bool) (h : m j = true) : below (one j) (mask m (pair i j)) := by
    intro k hk
    have e : k=j := by simpa [one] using hk
    subst k
    simp [mask,pair,h]
  have ev := Bool.or_eq_true_iff.mp survives
  rcases ev with ev | ev
  · obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ev
    apply mono _ _ _ _ (p₁ keepL l) (p₂ keepR r)
    simp [crown,hne]
  · obtain ⟨l,r⟩ := Bool.and_eq_true_iff.mp ev
    apply mono _ _ _ _ (p₂ keepL l) (p₁ keepR r)
    simp [crown,Ne.symm hne]

omit mono crown
/-- Deleting one left input and one right input with distinct indices leaves a
surviving orientation on every distinct marked pair. -/
theorem delete_opposite_choices (a b i j : Fin n) (ab : a ≠ b) (ij : i ≠ j) :
    ((decide (i ≠ a) && decide (j ≠ b)) ||
     (decide (j ≠ a) && decide (i ≠ b))) = true := by
  by_cases ia : i=a <;> by_cases jb : j=b <;> by_cases ja : j=a <;> by_cases ib : i=b
  all_goals simp_all
end ProofLantern.Crown.PartialIdentification
