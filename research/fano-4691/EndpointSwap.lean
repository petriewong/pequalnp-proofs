import PEqualNP.Defs.EdgeOwnership

/-! Endpoint-role transport for the double nested-AND obstruction.
This is a structural bridge, not an exclusion at any gate budget. -/
namespace ProofLantern.EndpointSwap

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

structure Profile where
  isAnd : Nat → Prop
  inside : Nat → Nat → Prop
  atOutput : Nat → Prop
  pair : Nat → Bool
  point : Nat → Bool
  line : Nat → Bool
  pointInput : Nat → Fin 2 → Bool
  lineInput : Nat → Fin 2 → Bool

def flag (p : Profile) (self other : Nat → Bool)
    (selfInput : Nat → Fin 2 → Bool) (g : Nat) : Prop :=
  p.atOutput g ∧ p.isAnd g ∧ p.pair g = true ∧
  (∀ b, selfInput g b = false) ∧ other g = false ∧
  ∃ k, p.inside k g ∧ p.isAnd k ∧ p.pair k = true ∧ self k = false ∧ other k = false

def motif (p : Profile) (i j : Nat) : Prop :=
  i ≠ j ∧ ¬ p.inside i j ∧ ¬ p.inside j i ∧
  flag p p.point p.line p.pointInput i ∧ flag p p.line p.point p.lineInput j

def swap (p : Profile) : Profile :=
  { p with point := p.line, line := p.point,
           pointInput := p.lineInput, lineInput := p.pointInput }

/-- Both top gates and their nested witnesses keep their indices, but exchange roles. -/
theorem motif_swap (p : Profile) (i j : Nat) :
    motif (swap p) j i ↔ motif p i j := by
  change (j ≠ i ∧ ¬ p.inside j i ∧ ¬ p.inside i j ∧
      flag p p.line p.point p.lineInput j ∧ flag p p.point p.line p.pointInput i) ↔
    (i ≠ j ∧ ¬ p.inside i j ∧ ¬ p.inside j i ∧
      flag p p.point p.line p.pointInput i ∧ flag p p.line p.point p.lineInput j)
  constructor
  · rintro ⟨hne, hji, hij, hj, hi⟩
    exact ⟨hne.symm, hij, hji, hi, hj⟩
  · rintro ⟨hne, hij, hji, hi, hj⟩
    exact ⟨hne.symm, hji, hij, hj, hi⟩

theorem has_motif_swap (p : Profile) :
    (∃ i j, motif (swap p) i j) ↔ ∃ i j, motif p i j := by
  constructor
  · rintro ⟨i, j, h⟩
    exact ⟨j, i, (motif_swap p j i).mp h⟩
  · rintro ⟨i, j, h⟩
    exact ⟨j, i, (motif_swap p i j).mpr h⟩

/-- Only primary wires can be changed; gate wires (even forward references) stay fixed. -/
def renameWire (n : Nat) (f : Fin n → Fin n) (w : Nat) : Nat :=
  if h : w < n then (f ⟨w, h⟩).val else w

def renameGate (n : Nat) (f : Fin n → Fin n) (g : Gate) : Gate :=
  { g with inputs := g.inputs.map (renameWire n f) }

def renameInputs (n : Nat) (f : Fin n → Fin n) (C : Circuit) : Circuit :=
  { C with gates := C.gates.map (renameGate n f) }

private theorem filter_rename (n cap : Nat) (f : Fin n → Fin n) (ws : List Nat) :
    (ws.map (renameWire n f)).filter (fun w => decide (n ≤ w ∧ w < cap)) =
      ws.filter (fun w => decide (n ≤ w ∧ w < cap)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : w < n
    · have hf : ¬ n ≤ (f ⟨w,h⟩).val := Nat.not_le_of_lt (f ⟨w,h⟩).isLt
      simpa [renameWire, h, Nat.not_le_of_lt h, hf] using ih
    · rw [List.map_cons, show renameWire n f w = w by simp [renameWire, h],
        List.filter_cons, List.filter_cons, ih]

theorem coneStep_rename (n : Nat) (f : Fin n → Fin n) (cs : List (List Nat)) (g : Gate) :
    coneStep n cs (renameGate n f g) = coneStep n cs g := by
  simp only [coneStep, renameGate, filter_rename]

private theorem fold_rename (n : Nat) (f : Fin n → Fin n)
    (gs : List Gate) (cs : List (List Nat)) :
    (gs.map (renameGate n f)).foldl (coneStep n) cs = gs.foldl (coneStep n) cs := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih => simp only [List.map_cons, List.foldl_cons, coneStep_rename, ih]

theorem cones_rename (n : Nat) (f : Fin n → Fin n) (C : Circuit) :
    cones n (renameInputs n f C) = cones n C :=
  fold_rename n f C.gates []

theorem inCone_rename (n : Nat) (f : Fin n → Fin n) (C : Circuit) (i j : Nat) :
    InCone n (renameInputs n f C) i j ↔ InCone n C i j := by
  rw [InCone, InCone, cones_rename]

end ProofLantern.EndpointSwap
