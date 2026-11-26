import Init
namespace LocalFano

def edge (p l : Fin 7) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3

instance (p l : Fin 7) : Decidable (edge p l) := by
  unfold edge
  infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem no_four_cycle : ∀ (a b x y : Fin 7), a ≠ b → x ≠ y →
    ¬ (edge a x ∧ edge a y ∧ edge b x ∧ edge b y) := by
  decide

theorem diagonal_edges (a : Fin 7) : edge a a := Or.inl rfl

theorem edge_translate : ∀ (p l t : Fin 7), edge p l ↔ edge (p+t) (l+t) := by decide

theorem neighbors_of_zero : ∀ (l : Fin 7), edge 0 l ↔ l = 0 ∨ l = 4 ∨ l = 6 := by decide

theorem neighbors_of_seven : ∀ (p : Fin 7), edge p 0 ↔ p = 0 ∨ p = 1 ∨ p = 3 := by decide

end LocalFano

namespace LocalFano
/-- A monotone checker only needs an upper negative and a lower positive reference point. -/
theorem monotone_on_boundary {α : Type} (le : α → α → Prop) (want got : α → Bool)
    (mono : ∀ {a b}, le a b → got a = true → got b = true)
    (lower : ∀ a, want a = true → ∃ b, le b a ∧ got b = true)
    (upper : ∀ a, want a = false → ∃ b, le a b ∧ got b = false) :
    ∀ a, got a = want a := by
  intro a
  cases hw : want a with
  | false =>
    obtain ⟨b,hab,hb⟩ := upper a hw
    cases hg : got a with
    | false => rfl
    | true => cases hb.symm.trans (mono hab hg)
  | true =>
    obtain ⟨b,hba,hb⟩ := lower a hw
    exact mono hba hb
end LocalFano

namespace LocalFano

theorem cycle_binary_constant (b : Fin 7 → Bool)
    (h : ∀ i, b i = true → b (i+1) = true) : ∀ i, b i = b 0 := by
  have step01 : b 0 = true → b 1 = true := h 0
  have step12 : b 1 = true → b 2 = true := h 1
  have step23 : b 2 = true → b 3 = true := h 2
  have step34 : b 3 = true → b 4 = true := h 3
  have step45 : b 4 = true → b 5 = true := h 4
  have step56 : b 5 = true → b 6 = true := h 5
  have step60 : b 6 = true → b 0 = true := h 6
  intro i
  have hi := i.isLt
  have hdec : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 ∨ i.val=4 ∨ i.val=5 ∨ i.val=6 := by omega
  rcases hdec with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [show i = 0 from Fin.ext h0]
  · rw [show i = 1 from Fin.ext h1]; cases ha : b 1 <;> cases hz : b 0 <;> simp_all
  · rw [show i = 2 from Fin.ext h2]; cases ha : b 2 <;> cases hz : b 0 <;> simp_all
  · rw [show i = 3 from Fin.ext h3]; cases ha : b 3 <;> cases hz : b 0 <;> simp_all
  · rw [show i = 4 from Fin.ext h4]; cases ha : b 4 <;> cases hz : b 0 <;> simp_all
  · rw [show i = 5 from Fin.ext h5]; cases ha : b 5 <;> cases hz : b 0 <;> simp_all
  · rw [show i = 6 from Fin.ext h6]; cases ha : b 6 <;> cases hz : b 0 <;> simp_all

-- With exactly one endpoint chosen per diagonal edge, a vertex cover is one whole colour.
theorem tight_cover_colours (pt ln : Fin 7 → Bool)
    (one_each : ∀ i, ln i = !(pt i))
    (cover : ∀ a b, edge a b → pt a = true ∨ ln b = true) :
    (∀ i, pt i = true ∧ ln i = false) ∨ (∀ i, pt i = false ∧ ln i = true) := by
  have h : ∀ i, pt i = true → pt (i+1) = true := by
    intro i hi
    rcases cover (i+1) i (Or.inr (Or.inl rfl)) with hp | hl
    · exact hp
    · rw [one_each,hi] at hl
      contradiction
  have c := cycle_binary_constant pt h
  cases h0 : pt 0 with
  | false =>
    right
    intro i
    have hi : pt i = false := (c i).trans h0
    exact ⟨hi,by rw [one_each,hi]; rfl⟩
  | true =>
    left
    intro i
    have hi : pt i = true := (c i).trans h0
    exact ⟨hi,by rw [one_each,hi]; rfl⟩

end LocalFano
