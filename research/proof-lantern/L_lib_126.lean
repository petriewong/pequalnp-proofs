/-
SPDX-License-Identifier: Apache-2.0
Research archive for Proof Lantern L-lib-126; no upstream submission.
The helper block is adapted from open-goat/pequalnp-proofs at
e125f04d0dc6fed67cee48a1d06692912e167c32:
lean/PEqualNP/Search/Helpers/ResLinQ.lean (litQEq_holds) and
lean/PEqualNP/Search/Helpers/SemanticWeakening.lean (the General section).
Changes: narrow imports, omit unrelated helper lemmas, and add the
non-tautological CNF construction and polynomial bound.
-/
import PEqualNP.Defs.SearchQ

import Mathlib.Tactic.Linarith

import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Group.Action.Defs

namespace PEqualNP.Search.Helpers

open PEqualNP.Search

theorem litQEq_holds {V : Type} [Fintype V] [DecidableEq V] (a : V → Bool) (l : V × Bool)
    (h : a l.1 = l.2) : QEq.Holds a (litQEq l) := by
  simp only [QEq.Holds, litQEq, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ l.1 (fun u => if a u = true then (1 : ℤ) else 0)]
  simp [h]

end PEqualNP.Search.Helpers


/-!
# Helpers: what semantic weakening gives to dag-like Res(lin) over the integers

Used by the refutation of `L-alg-004`.

The weakening rule of `IsResLinQDerivation` is semantic. Two consequences:

* a conjunction of literals is one equation with coefficients `1`, `-1`, `0` (`agreeEq`), so
  a line can say "some clause of the formula is falsified", and for an unsatisfiable formula
  that line is implied by anything;
* an equation that falsifies every literal of a clause is cut from the head of a line with
  three lines per literal (`cut`), reusing the line once per literal.

Together (`short_refutation`): a list `E` of equations that covers every 0/1 point, each
falsifying a clause of width at most `k`, gives a refutation with at most
`2 + |E| (3 k + 2)` lines. For the bit pigeonhole formula `E` is "pigeons `i`, `j` both sit
in hole `α`" (`bphp_short`).
-/

namespace PEqualNP.Search.Helpers

open PEqualNP.Search PEqualNP.ProofComplexity

section General

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The equation "the point agrees with `t` on every variable in `S`". -/
def agreeEq (S : V → Prop) [DecidablePred S] (t : V → Bool) : QEq V :=
  (fun v => if S v then (if t v then 1 else -1) else 0,
   ∑ v, if S v then (if t v then 1 else 0) else 0)

theorem agreeEq_holds (S : V → Prop) [DecidablePred S] (t x : V → Bool) :
    QEq.Holds x (agreeEq S t) ↔ ∀ v, S v → x v = t v := by
  unfold QEq.Holds agreeEq
  rw [Finset.sum_eq_sum_iff_of_le]
  · refine ⟨fun h v hv => ?_, fun h v _ => ?_⟩
    · have := h v (Finset.mem_univ v)
      simp only [hv, if_true] at this
      cases hx : x v <;> cases ht : t v <;> simp [hx, ht] at this ⊢
    · by_cases hv : S v
      · have := h v hv
        cases hx : x v <;> cases ht : t v <;> simp_all
      · simp [hv]
  · intro v _
    by_cases hv : S v <;> cases hx : x v <;> cases ht : t v <;> simp [hv, hx, ht]

theorem nat_size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem agreeEq_size (S : V → Prop) [DecidablePred S] (t : V → Bool) :
    (agreeEq S t).size ≤ 3 + 2 * Fintype.card V := by
  unfold QEq.size agreeEq
  have h1 : (∑ v : V, Nat.size (if S v then (if t v then (1 : ℤ) else -1) else 0).natAbs)
      ≤ Fintype.card V := by
    calc _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
            by_cases hv : S v <;> cases ht : t v <;> simp [hv]
      _ = Fintype.card V := by simp
  have h2 : Nat.size (∑ v : V, if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs
      ≤ Fintype.card V := by
    calc _ ≤ (∑ v : V, if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs :=
            nat_size_le_self _
      _ ≤ ∑ v : V, (if S v then (if t v then (1 : ℤ) else 0) else 0).natAbs :=
            Int.natAbs_sum_le _ _
      _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum fun v _ => by
            by_cases hv : S v <;> cases ht : t v <;> simp [hv]
      _ = Fintype.card V := by simp
  dsimp only
  omega

theorem litQEq_size (l : V × Bool) : (litQEq l).size ≤ 3 := by
  unfold QEq.size litQEq
  have h1 : (∑ v : V, Nat.size (if v = l.1 then (1 : ℤ) else 0).natAbs) = 1 := by
    have : ∀ v : V, Nat.size (if v = l.1 then (1 : ℤ) else 0).natAbs = if v = l.1 then 1 else 0 := by
      intro v; by_cases hv : v = l.1 <;> simp [hv]
    simp [this]
  have h2 : Nat.size (if l.2 = true then (1 : ℤ) else 0).natAbs ≤ 1 := by
    cases l.2 <;> simp
  simp only at h1 h2 ⊢
  omega

/-- The combination of a literal equation with the equation of the opposite literal. -/
def clashEq (l : V × Bool) : QEq V :=
  ((1 : ℤ) • (litQEq l).1 + (-1 : ℤ) • (litQEq (l.1, !l.2)).1,
    1 * (litQEq l).2 + (-1) * (litQEq (l.1, !l.2)).2)

theorem clashEq_not_holds (x : V → Bool) (l : V × Bool) : ¬ QEq.Holds x (clashEq l) := by
  unfold QEq.Holds clashEq litQEq
  cases l.2 <;> simp

theorem clashEq_size (l : V × Bool) : (clashEq l).size ≤ 3 := by
  unfold QEq.size clashEq litQEq
  cases l.2 <;> simp

/-- Cutting the literals of a list one by one against an equation that falsifies them. -/
theorem cut_aux (F : Set (PEqualNP.ProofComplexity.Clause V)) (e : QEq V) (R : QLine V) :
    ∀ (lits : List (V × Bool)),
      (∀ lit ∈ lits, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2) →
      ∀ π : List (QLine V), IsResLinQDerivation F π → (e :: R) ∈ π →
        (lits.map litQEq ++ R) ∈ π →
        ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ R ∈ ρ ++ π ∧
          ρ.length = 3 * lits.length ∧
          ∀ L ∈ ρ, L.length ≤ lits.length + 1 + 2 * R.length ∧
            ∀ e' ∈ L, e' ∈ R ∨ e'.size ≤ 3 := by
  intro lits
  induction lits with
  | nil =>
    intro _ π hπ _ hR
    exact ⟨[], by simpa using hπ, by simpa using hR, by simp, by simp⟩
  | cons lit rest ih =>
    intro hf π hπ he hD
    -- line 1: the opposite literal in front of `R`
    have h1 : IsResLinQDerivation F ((litQEq (lit.1, !lit.2) :: R) :: π) := by
      refine IsResLinQDerivation.weaken hπ he ?_
      rintro x ⟨e', he', hx⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact ⟨_, List.mem_cons_self, litQEq_holds x (lit.1, !lit.2)
          (hf lit List.mem_cons_self x hx)⟩
      · exact ⟨e', List.mem_cons_of_mem _ he', hx⟩
    -- line 2: the combination
    have h2 : IsResLinQDerivation F
        ((clashEq lit :: ((rest.map litQEq ++ R) ++ R)) ::
          (litQEq (lit.1, !lit.2) :: R) :: π) :=
      IsResLinQDerivation.res (e := litQEq lit) (e' := litQEq (lit.1, !lit.2)) 1 (-1) h1
        (List.mem_cons_of_mem _ (by simpa using hD)) List.mem_cons_self
    -- line 3: drop the false equation and the copy of `R`
    have h3 : IsResLinQDerivation F
        ((rest.map litQEq ++ R) :: (clashEq lit :: ((rest.map litQEq ++ R) ++ R)) ::
          (litQEq (lit.1, !lit.2) :: R) :: π) := by
      refine IsResLinQDerivation.weaken h2 List.mem_cons_self ?_
      rintro x ⟨e', he', hx⟩
      rcases List.mem_cons.mp he' with rfl | he'
      · exact absurd hx (clashEq_not_holds x lit)
      · rcases List.mem_append.mp he' with he' | he'
        · exact ⟨e', he', hx⟩
        · exact ⟨e', List.mem_append_right _ he', hx⟩
    obtain ⟨ρ, hρ, hRρ, hlen, hb⟩ := ih (fun l hl => hf l (List.mem_cons_of_mem _ hl)) _ h3
      (by simp [he]) List.mem_cons_self
    refine ⟨ρ ++ [rest.map litQEq ++ R, clashEq lit :: ((rest.map litQEq ++ R) ++ R),
      litQEq (lit.1, !lit.2) :: R], by simpa using hρ, by simpa using hRρ, by simp [hlen]; omega,
      ?_⟩
    intro L hL
    rcases List.mem_append.mp hL with hL | hL
    · obtain ⟨hl, hs⟩ := hb L hL
      exact ⟨by simp only [List.length_cons]; omega, hs⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl | rfl
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_append.mp he' with he' | he'
        · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
          exact Or.inr (litQEq_size l')
        · exact Or.inl he'
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (clashEq_size lit)
        · rcases List.mem_append.mp he' with he' | he'
          · rcases List.mem_append.mp he' with he' | he'
            · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
              exact Or.inr (litQEq_size l')
            · exact Or.inl he'
          · exact Or.inl he'
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Or.inr (litQEq_size _)
        · exact Or.inl he'

/-- The cut: an equation that falsifies every literal of a clause of the formula is removed
from the head of a line, with `3 |C| + 2` new lines. -/
theorem cut (F : Set (PEqualNP.ProofComplexity.Clause V)) (e : QEq V) (R : QLine V)
    (C : PEqualNP.ProofComplexity.Clause V) (hC : C ∈ F)
    (hf : ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2)
    (π : List (QLine V)) (hπ : IsResLinQDerivation F π) (he : (e :: R) ∈ π) :
    ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ R ∈ ρ ++ π ∧
      ρ.length = 3 * C.card + 2 ∧
      ∀ L ∈ ρ, L.length ≤ C.card + 1 + 2 * R.length ∧
        ∀ e' ∈ L, e' ∈ R ∨ e'.size ≤ 3 := by
  have h1 : IsResLinQDerivation F (C.toList.map litQEq :: π) :=
    IsResLinQDerivation.ax C hπ hC (fun e' => by
      simp only [List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩)
  have h2 : IsResLinQDerivation F ((C.toList.map litQEq ++ R) :: C.toList.map litQEq :: π) := by
    refine IsResLinQDerivation.weaken h1 List.mem_cons_self ?_
    rintro x ⟨e', he', hx⟩
    exact ⟨e', List.mem_append_left _ he', hx⟩
  obtain ⟨ρ, hρ, hRρ, hlen, hb⟩ := cut_aux F e R C.toList
    (fun l hl => hf l (Finset.mem_toList.mp hl)) _ h2 (by simp [he]) List.mem_cons_self
  rw [Finset.length_toList] at hlen hb
  refine ⟨ρ ++ [C.toList.map litQEq ++ R, C.toList.map litQEq], by simpa using hρ,
    by simpa using hRρ, by simp [hlen], ?_⟩
  intro L hL
  rcases List.mem_append.mp hL with hL | hL
  · exact hb L hL
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · refine ⟨by simp; omega, fun e' he' => ?_⟩
      rcases List.mem_append.mp he' with he' | he'
      · obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
        exact Or.inr (litQEq_size l')
      · exact Or.inl he'
    · refine ⟨by simp; omega, fun e' he' => ?_⟩
      obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
      exact Or.inr (litQEq_size l')

/-- Cutting every equation of a line in turn. -/
theorem cut_all (F : Set (PEqualNP.ProofComplexity.Clause V)) (k : ℕ) :
    ∀ (E : QLine V),
      (∀ e ∈ E, ∃ C ∈ F, C.card ≤ k ∧
        ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2) →
      ∀ π : List (QLine V), IsResLinQDerivation F π → E ∈ π →
        ∃ ρ : List (QLine V), IsResLinQDerivation F (ρ ++ π) ∧ [] ∈ ρ ++ π ∧
          ρ.length ≤ E.length * (3 * k + 2) ∧
          ∀ L ∈ ρ, L.length ≤ k + 1 + 2 * E.length ∧
            ∀ e' ∈ L, e' ∈ E ∨ e'.size ≤ 3 := by
  intro E
  induction E with
  | nil =>
    intro _ π hπ hE
    exact ⟨[], by simpa using hπ, by simpa using hE, by simp, by simp⟩
  | cons e R ih =>
    intro hE π hπ he
    obtain ⟨C, hC, hk, hf⟩ := hE e List.mem_cons_self
    obtain ⟨ρ₁, hρ₁, hR, hlen₁, hb₁⟩ := cut F e R C hC hf π hπ he
    obtain ⟨ρ₂, hρ₂, hnil, hlen₂, hb₂⟩ :=
      ih (fun e' he' => hE e' (List.mem_cons_of_mem _ he')) _ hρ₁ hR
    refine ⟨ρ₂ ++ ρ₁, by simpa using hρ₂, by simpa using hnil, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons, hlen₁]
      have : 3 * C.card + 2 ≤ 3 * k + 2 := by omega
      nlinarith
    · intro L hL
      rcases List.mem_append.mp hL with hL | hL
      · obtain ⟨hl, hs⟩ := hb₂ L hL
        refine ⟨by simp only [List.length_cons]; omega, fun e' he' => ?_⟩
        rcases hs e' he' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · obtain ⟨hl, hs⟩ := hb₁ L hL
        refine ⟨by simp only [List.length_cons]; omega, fun e' he' => ?_⟩
        rcases hs e' he' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

theorem resLinQSize_le (π : List (QLine V)) (W S : ℕ)
    (h : ∀ L ∈ π, L.length ≤ W ∧ ∀ e ∈ L, e.size ≤ S) :
    resLinQSize π ≤ π.length * (1 + W * S) := by
  unfold resLinQSize
  have := List.sum_le_card_nsmul (π.map fun L => 1 + (L.map QEq.size).sum) (1 + W * S) (by
    intro n hn
    obtain ⟨L, hL, rfl⟩ := List.mem_map.mp hn
    obtain ⟨hl, hs⟩ := h L hL
    have h' := List.sum_le_card_nsmul (L.map QEq.size) S (by
      intro n hn
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hn
      exact hs e he)
    simp only [List.length_map, smul_eq_mul] at h'
    have : L.length * S ≤ W * S := Nat.mul_le_mul_right S hl
    omega)
  simpa using this

/-- A line of equations that covers every 0/1 point, each equation falsifying a clause of the
formula of width at most `k`, gives a short dag-like refutation. -/
theorem short_refutation (F : Set (PEqualNP.ProofComplexity.Clause V)) (k S : ℕ)
    (hS : 3 ≤ S) (E : QLine V)
    (hcover : ∀ x : V → Bool, QLine.Holds x E)
    (hE : ∀ e ∈ E, ∃ C ∈ F, C.card ≤ k ∧
      ∀ lit ∈ C, ∀ x : V → Bool, QEq.Holds x e → x lit.1 = !lit.2)
    (hsize : ∀ e ∈ E, e.size ≤ S) :
    ∃ π : List (QLine V), IsResLinQRefutation F π ∧
      resLinQSize π ≤ (2 + E.length * (3 * k + 2)) * (1 + (k + 1 + 2 * E.length) * S) := by
  obtain ⟨e₀, he₀, -⟩ := hcover (fun _ => false)
  obtain ⟨C₀, hC₀, hk₀, -⟩ := hE e₀ he₀
  have h1 : IsResLinQDerivation F [C₀.toList.map litQEq] :=
    IsResLinQDerivation.ax C₀ IsResLinQDerivation.nil hC₀ (fun e' => by
      simp only [List.mem_map, Finset.mem_toList]
      exact ⟨fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩, fun ⟨l, hl, h⟩ => ⟨l, hl, h.symm⟩⟩)
  have h2 : IsResLinQDerivation F [E, C₀.toList.map litQEq] :=
    IsResLinQDerivation.weaken h1 List.mem_cons_self (fun x _ => hcover x)
  obtain ⟨ρ, hρ, hnil, hlen, hb⟩ := cut_all F k E hE _ h2 List.mem_cons_self
  refine ⟨ρ ++ [E, C₀.toList.map litQEq], ⟨hρ, hnil⟩, ?_⟩
  refine (resLinQSize_le _ (k + 1 + 2 * E.length) S ?_).trans ?_
  · intro L hL
    rcases List.mem_append.mp hL with hL | hL
    · obtain ⟨hl, hs⟩ := hb L hL
      refine ⟨hl, fun e' he' => ?_⟩
      rcases hs e' he' with h | h
      · exact hsize e' h
      · exact h.trans hS
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
      rcases hL with rfl | rfl
      · exact ⟨by omega, hsize⟩
      · refine ⟨by simp; omega, fun e' he' => ?_⟩
        obtain ⟨l', _, rfl⟩ := List.mem_map.mp he'
        exact (litQEq_size l').trans hS
  · refine Nat.mul_le_mul_right _ ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end General

end PEqualNP.Search.Helpers

namespace PEqualNP.Outside.L_lib_126
open PEqualNP.ProofComplexity PEqualNP.Search PEqualNP.Search.Helpers

variable {n : ℕ}

def valid (C : Clause (Fin n)) : Prop :=
  ∀ v : Fin n, (v, true) ∈ C → (v, false) ∉ C

instance validDec (C : Clause (Fin n)) : Decidable (valid C) := by
  unfold valid
  infer_instance

def badEq (C : Clause (Fin n)) : QEq (Fin n) :=
  agreeEq (fun v => (v, true) ∈ C ∨ (v, false) ∈ C)
    (fun v => decide ((v, true) ∉ C))

theorem badEq_iff (C : Clause (Fin n)) (hC : valid C) (x : Fin n → Bool) :
    QEq.Holds x (badEq C) ↔ ¬ ClauseSat x C := by
  rw [badEq, agreeEq_holds, ClauseSat]
  constructor
  · intro h
    rintro ⟨⟨v, b⟩, hv, hb⟩
    cases b
    · have hnt : (v, true) ∉ C := fun ht => hC v ht hv
      have hx := h v (Or.inr hv)
      simp [hnt] at hx
      simp_all
    · have hx := h v (Or.inl hv)
      simp [hv] at hx
      simp_all
  · intro h v hv
    by_cases ht : (v, true) ∈ C
    · have hv' : x v ≠ true := fun e => h ⟨(v, true), ht, e⟩
      simpa [ht] using Bool.eq_false_of_not_eq_true hv'
    · have hf := hv.resolve_left ht
      have hv' : x v ≠ false := fun e => h ⟨(v, false), hf, e⟩
      simpa [ht] using Bool.eq_true_of_not_eq_false hv'

theorem valid_of_false {C : Clause (Fin n)} {x : Fin n → Bool} (h : ¬ ClauseSat x C) :
    valid C := by
  intro v ht hf
  apply h
  cases e : x v
  · exact ⟨(v, false), hf, e⟩
  · exact ⟨(v, true), ht, e⟩

theorem bound (n m k l : ℕ) (hl : l ≤ m) :
    (2 + l * (3 * k + 2)) * (1 + (k + 1 + 2 * l) * (3 + 2 * n)) ≤
      112 * (n + m + k + 1) ^ 112 := by
  let T := n + m + k + 1
  change _ ≤ 112 * T ^ 112
  have ht : 1 ≤ T := by dsimp [T]; omega
  have hl' : l ≤ T := by dsimp [T]; omega
  have hk : 3 * k + 2 ≤ 5 * T := by dsimp [T]; omega
  have hkn : k + 1 + 2 * l ≤ 3 * T := by dsimp [T]; omega
  have hn : 3 + 2 * n ≤ 5 * T := by dsimp [T]; omega
  have hs : 1 ≤ T ^ 2 := by nlinarith
  have hA : 2 + l * (3 * k + 2) ≤ 7 * T ^ 2 := by
    have hh := Nat.mul_le_mul hl' hk
    nlinarith
  have hB : 1 + (k + 1 + 2 * l) * (3 + 2 * n) ≤ 16 * T ^ 2 := by
    have hh := Nat.mul_le_mul hkn hn
    nlinarith
  calc
    _ ≤ (7 * T ^ 2) * (16 * T ^ 2) := Nat.mul_le_mul hA hB
    _ = 112 * T ^ 4 := by ring
    _ ≤ 112 * T ^ 112 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right ht (by decide))

theorem full :
    ∃ c : ℕ, ∀ (n k : ℕ) (F : Finset (Clause (Fin n))),
      (∀ C ∈ F, C.card ≤ k) → ¬ Satisfiable (↑F : Set (Clause (Fin n))) →
      ∃ π : List (QLine (Fin n)), IsResLinQRefutation (↑F : Set (Clause (Fin n))) π ∧
        resLinQSize π ≤ c * (n + F.card + k + 1) ^ c := by
  refine ⟨112, ?_⟩
  intro n k F hw hu
  let E := (F.filter valid).toList.map badEq
  have unpack : ∀ e ∈ E, ∃ C ∈ F, valid C ∧ badEq C = e := by
    intro e he
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp he
    have hc := Finset.mem_filter.mp (Finset.mem_toList.mp hC)
    exact ⟨C, hc.1, hc.2, rfl⟩
  have cover : ∀ x : Fin n → Bool, QLine.Holds x E := by
    intro x
    have h : ∃ C ∈ F, ¬ ClauseSat x C := by
      by_contra! h
      exact hu ⟨x, h⟩
    obtain ⟨C, hC, hf⟩ := h
    have hV := valid_of_false hf
    exact ⟨badEq C, List.mem_map.mpr ⟨C, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hC,hV⟩), rfl⟩,
      (badEq_iff C hV x).mpr hf⟩
  have cert : ∀ e ∈ E, ∃ C ∈ (↑F : Set (Clause (Fin n))), C.card ≤ k ∧
      ∀ lit ∈ C, ∀ x : Fin n → Bool, QEq.Holds x e → x lit.1 = !lit.2 := by
    intro e he
    obtain ⟨C, hC, hV, rfl⟩ := unpack e he
    refine ⟨C, hC, hw C hC, ?_⟩
    intro lit hl x hx
    have hn : x lit.1 ≠ lit.2 := fun eq => (badEq_iff C hV x).mp hx ⟨lit, hl, eq⟩
    cases b : lit.2 <;> cases a : x lit.1 <;> simp_all
  have sizes : ∀ e ∈ E, e.size ≤ 3 + 2 * n := by
    intro e he
    obtain ⟨C, _, _, rfl⟩ := unpack e he
    unfold badEq
    simpa using agreeEq_size (V := Fin n) (fun v => (v, true) ∈ C ∨ (v, false) ∈ C)
      (fun v => decide ((v, true) ∉ C))
  obtain ⟨π, hπ, hb⟩ := short_refutation (↑F) k (3 + 2 * n) (by omega) E cover cert sizes
  have hlen : E.length ≤ F.card := by
    simpa [E] using Finset.card_filter_le F valid
  exact ⟨π, hπ, hb.trans (bound n F.card k E.length hlen)⟩

end PEqualNP.Outside.L_lib_126
