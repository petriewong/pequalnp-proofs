import PEqualNP.Defs.Represents

namespace ProofLantern.Crown.ComponentWitnesses

def row {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)
def zero {n : Nat} : Fin n → Bool := fun _ => false
def present {n : Nat} (i : Fin n) (b : Bool) : Fin n → Bool :=
  fun j => b && (row i j)
def overlay {n : Nat} (a b : Fin n → Bool) : Fin n → Bool := fun j => a j || b j
def below {n : Nat} (a b : Fin n → Bool) : Prop := ∀ j, a j = true → b j = true

variable {n : Nat}

theorem refl (x : Fin n → Bool) : below x x := fun _ h => h
theorem zeroBelow (x : Fin n → Bool) : below zero x := by
  intro j h
  simp [zero] at h

theorem leftBelow (a b : Fin n → Bool) : below a (overlay a b) := by
  intro j h
  simp [overlay,h]

theorem rightBelow (a b : Fin n → Bool) : below b (overlay a b) := by
  intro j h
  simp [overlay,h]

variable (f : (Fin n → Bool) → (Fin n → Bool) → Bool)
variable (mono : ∀ a b c d, below a c → below b d → f a b = true → f c d = true)
variable (crown : ∀ i j, f (row i) (row j) = decide (i ≠ j))
include mono crown

theorem noEmptyColumn (i : Fin n) : f (row i) zero = false := by
  cases h : f (row i) zero with
  | false => rfl
  | true =>
    have p := mono (row i) zero (row i) (row i) (refl _) (zeroBelow _) h
    rw [crown] at p
    simp at p

theorem noEmptyRow (i : Fin n) : f zero (row i) = false := by
  cases h : f zero (row i) with
  | false => rfl
  | true =>
    have p := mono zero (row i) (row i) (row i) (zeroBelow _) (refl _) h
    rw [crown] at p
    simp at p

theorem noEmptyBoth (i : Fin n) : f zero zero = false := by
  cases h : f zero zero with
  | false => rfl
  | true =>
    have p := mono zero zero (row i) (row i) (zeroBelow _) (zeroBelow _) h
    rw [crown] at p
    simp at p

/-- An opposite pair of different indices has an AND cofactor in every monotone extension. -/
theorem crossAnd (i j : Fin n) (ij : i ≠ j) (a b : Bool) :
    f (present i a) (present j b) = (a && b) := by
  cases a <;> cases b
  · exact noEmptyBoth f mono crown i
  · exact noEmptyRow f mono crown j
  · exact noEmptyColumn f mono crown i
  · have A : present i true = row i := by funext u; simp [present]
    have B : present j true = row j := by funext u; simp [present]
    simpa [A,B,ij] using crown i j

/-- Fixing a disjoint negative diagonal makes the same edge pair an OR cofactor. -/
theorem crossOr (i j k : Fin n) (ik : i ≠ k) (kj : k ≠ j) (a b : Bool) :
    f (overlay (row k) (present i a)) (overlay (row k) (present j b)) = (a || b) := by
  have acceptR : f (row k) (row j) = true := by simp [crown,kj]
  have acceptL : f (row i) (row k) = true := by simp [crown,ik]
  cases a <;> cases b
  · have A : overlay (row k) (present i false) = row k := by funext u; simp [overlay,present]
    have B : overlay (row k) (present j false) = row k := by funext u; simp [overlay,present]
    simpa [A,B] using crown k k
  · exact mono _ _ _ _ (leftBelow _ _) (rightBelow _ _) acceptR
  · exact mono _ _ _ _ (rightBelow _ _) (leftBelow _ _) acceptL
  · exact mono _ _ _ _ (rightBelow _ _) (leftBelow _ _) acceptL

/-- If at least two free columns include the first row's index, zero and both
distinct rows produce three different response signatures on those columns. -/
theorem rowRank (i j b : Fin n) (ij : i ≠ j) (ib : i ≠ b) :
    let signature := fun x => (f x (row i), f x (row b))
    signature zero ≠ signature (row i) ∧
    signature zero ≠ signature (row j) ∧
    signature (row i) ≠ signature (row j) := by
  have ji : j ≠ i := Ne.symm ij
  simp [noEmptyRow f mono crown,crown,ji,ib]

end ProofLantern.Crown.ComponentWitnesses
