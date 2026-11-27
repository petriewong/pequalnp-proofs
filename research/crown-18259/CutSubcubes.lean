import Mathlib.Data.Fintype.BigOperators

namespace ProofLantern.Crown.CutCodes

abbrev Partial (m : Nat) := Fin m → Option Bool
abbrev Full (m : Nat) := Fin m → Bool

def fits {m : Nat} (x : Partial m) (v : Full m) : Prop :=
  ∀ i b, x i = some b → v i = b

def opposite {m : Nat} (x y : Partial m) (i : Fin m) : Prop :=
  ∃ a b, x i = some a ∧ y i = some b ∧ a ≠ b

def wordOf {m : Nat} (x y : Partial m) (i : Fin m) : Bool :=
  (x i).getD ((y i).getD false)

theorem has_common_iff {m : Nat} (x y : Partial m) :
    (∃ v : Full m, fits x v ∧ fits y v) ↔ ∀ i, ¬ opposite x y i := by
  constructor
  · rintro ⟨v,l,r⟩ i ⟨a,b,ha,hb,neq⟩
    exact neq ((l i a ha).symm.trans (r i b hb))
  · intro h
    refine ⟨wordOf x y, ?_, ?_⟩
    · intro i a ha
      simp [wordOf,ha]
    · intro i b hb
      cases hi : x i with
      | none => simp [wordOf,hi,hb]
      | some a =>
        have eq : a = b := by
          by_contra n
          exact h i ⟨a,b,hi,hb,n⟩
        simp [wordOf,hi,eq]

/-- Select any common representative for each matched diagonal row/column pair.
An exact pure-cut Crown has distinct representatives automatically. -/
theorem reps_injective {n m : Nat} (x y : Fin n → Partial m)
    (sep : ∀ u v, u ≠ v → ∃ i, opposite (x u) (y v) i)
    (c : Fin n → Full m) (ok : ∀ i, fits (x i) (c i) ∧ fits (y i) (c i)) :
    Function.Injective c := by
  intro u v e
  by_contra d
  obtain ⟨i,a,b,ha,hb,hne⟩ := sep u v d
  have cu := (ok u).1 i a ha
  have cv := (ok v).2 i b hb
  exact hne (cu.symm.trans ((congrFun e i).trans cv))

theorem diag_code_bound {n m : Nat} (x y : Fin n → Partial m)
    (agree : ∀ u i, ¬ opposite (x u) (y u) i)
    (sep : ∀ u v, u ≠ v → ∃ i, opposite (x u) (y v) i) : n ≤ 2^m := by
  classical
  have h u := (has_common_iff (x u) (y u)).2 (agree u)
  let c : Fin n → Full m := fun u => Classical.choose (h u)
  have ok : ∀ u, fits (x u) (c u) ∧ fits (y u) (c u) := fun u => Classical.choose_spec (h u)
  have h := Fintype.card_le_of_injective c (reps_injective x y sep c ok)
  simpa [Fintype.card_fun,Fintype.card_bool,Full] using h

/-- Every row or column subcube excludes the representative of every other vertex.
Thus retaining only cubes containing their specified representative and no other is exact. -/
theorem rep_excluded_from_other {n m : Nat} (x y : Fin n → Partial m)
    (sep : ∀ u v, u ≠ v → ∃ i, opposite (x u) (y v) i)
    (c : Fin n → Full m) (ok : ∀ i, fits (x i) (c i) ∧ fits (y i) (c i))
    (u v : Fin n) (d : u ≠ v) :
    ¬ fits (x u) (c v) ∧ ¬ fits (y u) (c v) := by
  constructor
  · intro ha
    obtain ⟨i,op⟩ := sep u v d
    exact (has_common_iff (x u) (y v)).1 ⟨c v,ha,(ok v).2⟩ i op
  · intro hb
    obtain ⟨i,op⟩ := sep v u (Ne.symm d)
    exact (has_common_iff (x v) (y u)).1 ⟨c v,(ok v).1,hb⟩ i op

end ProofLantern.Crown.CutCodes
