/-
SPDX-License-Identifier: Apache-2.0
Research archive: a 54-line Res(2) refutation of PHP(4,3), not a solution to the
50-line target L-pcx-189. The search starts from the public L-pcx-191 proof
in open-goat/pequalnp-proofs and rewires its inference DAG.
-/
import PEqualNP.Defs.ProofComplexityResK

namespace PEqualNP.Outside.ContributionPHP43
open PEqualNP.ProofComplexity
abbrev V := Fin 4 × Fin 3
abbrev F : Set (KLine V) := (fun C => kLineOfClause C) '' PHP 4 3

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem unitc (C : Clause V) : ∀ T ∈ kLineOfClause C, T.card ≤ 2 := by
  intro T hT
  simp only [kLineOfClause, Finset.mem_image] at hT
  obtain ⟨l, _, rfl⟩ := hT
  simp

def c17 : Clause V := ({((0, 2), false), ((2, 2), false)} : Clause V)
def k17 : KLine V := kLineOfClause c17
def p17 : List (KLine V) := k17 :: []
theorem d17 : IsResKDerivation 2 F p17 :=
  IsResKDerivation.ax IsResKDerivation.nil ⟨c17, Set.mem_union_right _ ⟨0, 2, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def c7 : Clause V := ({((1, 0), false), ((2, 0), false)} : Clause V)
def k7 : KLine V := kLineOfClause c7
def p7 : List (KLine V) := k7 :: p17
theorem d7 : IsResKDerivation 2 F p7 :=
  IsResKDerivation.ax d17 ⟨c7, Set.mem_union_right _ ⟨1, 2, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def c9 : Clause V := ({((2, 0), false), ((3, 0), false)} : Clause V)
def k9 : KLine V := kLineOfClause c9
def p9 : List (KLine V) := k9 :: p7
theorem d9 : IsResKDerivation 2 F p9 :=
  IsResKDerivation.ax d7 ⟨c9, Set.mem_union_right _ ⟨2, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k22 : KLine V := {({((1, 0), false), ((3, 0), false)} : KTerm V), ({((2, 0), false)} : KTerm V)}
def p22 : List (KLine V) := k22 :: p9
theorem d22 : IsResKDerivation 2 F p22 :=
  IsResKDerivation.andIntro (C := k7) (D := k9) (R := k22) d9 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 0), false)} : KTerm V), ({((3, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

def c2 : Clause V := ({((2, 0), true), ((2, 1), true), ((2, 2), true)} : Clause V)
def k2 : KLine V := kLineOfClause c2
def p2 : List (KLine V) := k2 :: p22
theorem d2 : IsResKDerivation 2 F p2 :=
  IsResKDerivation.ax d22 ⟨c2, Set.mem_union_left _ ⟨2, by decide +kernel⟩, rfl⟩ (unitc _)

def k823 : KLine V := {({((1, 0), false), ((3, 0), false)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((2, 2), true)} : KTerm V)}
def p823 : List (KLine V) := k823 :: p2
theorem d823 : IsResKDerivation 2 F p823 :=
  IsResKDerivation.cut (C := k22) (D := k2) (R := k823) d2 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((2, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c3 : Clause V := ({((3, 0), true), ((3, 1), true), ((3, 2), true)} : Clause V)
def k3 : KLine V := kLineOfClause c3
def p3 : List (KLine V) := k3 :: p823
theorem d3 : IsResKDerivation 2 F p3 :=
  IsResKDerivation.ax d823 ⟨c3, Set.mem_union_left _ ⟨3, by decide +kernel⟩, rfl⟩ (unitc _)

def c1 : Clause V := ({((1, 0), true), ((1, 1), true), ((1, 2), true)} : Clause V)
def k1 : KLine V := kLineOfClause c1
def p1 : List (KLine V) := k1 :: p3
theorem d1 : IsResKDerivation 2 F p1 :=
  IsResKDerivation.ax d3 ⟨c1, Set.mem_union_left _ ⟨1, by decide +kernel⟩, rfl⟩ (unitc _)

def c14 : Clause V := ({((1, 1), false), ((3, 1), false)} : Clause V)
def k14 : KLine V := kLineOfClause c14
def p14 : List (KLine V) := k14 :: p1
theorem d14 : IsResKDerivation 2 F p14 :=
  IsResKDerivation.ax d1 ⟨c14, Set.mem_union_right _ ⟨1, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k25 : KLine V := {({((1, 0), true)} : KTerm V), ({((1, 2), true)} : KTerm V), ({((3, 1), false)} : KTerm V)}
def p25 : List (KLine V) := k25 :: p14
theorem d25 : IsResKDerivation 2 F p25 :=
  IsResKDerivation.cut (C := k1) (D := k14) (R := k25) d14 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k27 : KLine V := {({((1, 0), true)} : KTerm V), ({((1, 2), true)} : KTerm V), ({((3, 0), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p27 : List (KLine V) := k27 :: p25
theorem d27 : IsResKDerivation 2 F p27 :=
  IsResKDerivation.cut (C := k3) (D := k25) (R := k27) d25 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({((3, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k41 : KLine V := {({((1, 2), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((2, 2), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p41 : List (KLine V) := k41 :: p27
theorem d41 : IsResKDerivation 2 F p41 :=
  IsResKDerivation.cut (C := k823) (D := k27) (R := k41) d27 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))) (List.Mem.head _) ⟨({((1, 0), false), ((3, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c13 : Clause V := ({((1, 1), false), ((2, 1), false)} : Clause V)
def k13 : KLine V := kLineOfClause c13
def p13 : List (KLine V) := k13 :: p41
theorem d13 : IsResKDerivation 2 F p13 :=
  IsResKDerivation.ax d41 ⟨c13, Set.mem_union_right _ ⟨1, 2, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def c15 : Clause V := ({((2, 1), false), ((3, 1), false)} : Clause V)
def k15 : KLine V := kLineOfClause c15
def p15 : List (KLine V) := k15 :: p13
theorem d15 : IsResKDerivation 2 F p15 :=
  IsResKDerivation.ax d13 ⟨c15, Set.mem_union_right _ ⟨2, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k23 : KLine V := {({((1, 1), false), ((3, 1), false)} : KTerm V), ({((2, 1), false)} : KTerm V)}
def p23 : List (KLine V) := k23 :: p15
theorem d23 : IsResKDerivation 2 F p23 :=
  IsResKDerivation.andIntro (C := k13) (D := k15) (R := k23) d15 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 1), false)} : KTerm V), ({((3, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

def k382 : KLine V := {({((1, 0), true), ((3, 0), true)} : KTerm V), ({((1, 1), true)} : KTerm V), ({((1, 2), true)} : KTerm V), ({((3, 1), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p382 : List (KLine V) := k382 :: p23
theorem d382 : IsResKDerivation 2 F p382 :=
  IsResKDerivation.andIntro (C := k1) (D := k3) (R := k382) d23 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))) ⟨({((1, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

def c8 : Clause V := ({((1, 0), false), ((3, 0), false)} : Clause V)
def k8 : KLine V := kLineOfClause c8
def p8 : List (KLine V) := k8 :: p382
theorem d8 : IsResKDerivation 2 F p8 :=
  IsResKDerivation.ax d382 ⟨c8, Set.mem_union_right _ ⟨1, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k35 : KLine V := {({((1, 1), true)} : KTerm V), ({((1, 2), true)} : KTerm V), ({((3, 1), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p35 : List (KLine V) := k35 :: p8
theorem d35 : IsResKDerivation 2 F p35 :=
  IsResKDerivation.cut (C := k382) (D := k8) (R := k35) d8 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 0), true), ((3, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k40 : KLine V := {({((1, 2), true)} : KTerm V), ({((2, 1), false)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p40 : List (KLine V) := k40 :: p35
theorem d40 : IsResKDerivation 2 F p40 :=
  IsResKDerivation.cut (C := k23) (D := k35) (R := k40) d35 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) (List.Mem.head _) ⟨({((1, 1), false), ((3, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k42 : KLine V := {({((1, 2), true)} : KTerm V), ({((2, 2), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p42 : List (KLine V) := k42 :: p40
theorem d42 : IsResKDerivation 2 F p42 :=
  IsResKDerivation.cut (C := k41) (D := k40) (R := k42) d40 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))) (List.Mem.head _) ⟨({((2, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c16 : Clause V := ({((0, 2), false), ((1, 2), false)} : Clause V)
def k16 : KLine V := kLineOfClause c16
def p16 : List (KLine V) := k16 :: p42
theorem d16 : IsResKDerivation 2 F p16 :=
  IsResKDerivation.ax d42 ⟨c16, Set.mem_union_right _ ⟨0, 1, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k49 : KLine V := {({((0, 2), false)} : KTerm V), ({((2, 2), true)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p49 : List (KLine V) := k49 :: p16
theorem d49 : IsResKDerivation 2 F p49 :=
  IsResKDerivation.cut (C := k42) (D := k16) (R := k49) d16 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k50 : KLine V := {({((0, 2), false)} : KTerm V), ({((3, 2), true)} : KTerm V)}
def p50 : List (KLine V) := k50 :: p49
theorem d50 : IsResKDerivation 2 F p50 :=
  IsResKDerivation.cut (C := k17) (D := k49) (R := k50) d49 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))) (List.Mem.head _) ⟨({((2, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c18 : Clause V := ({((0, 2), false), ((3, 2), false)} : Clause V)
def k18 : KLine V := kLineOfClause c18
def p18 : List (KLine V) := k18 :: p50
theorem d18 : IsResKDerivation 2 F p18 :=
  IsResKDerivation.ax d50 ⟨c18, Set.mem_union_right _ ⟨0, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k51 : KLine V := {({((0, 2), false)} : KTerm V)}
def p51 : List (KLine V) := k51 :: p18
theorem d51 : IsResKDerivation 2 F p51 :=
  IsResKDerivation.cut (C := k50) (D := k18) (R := k51) d18 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((3, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c0 : Clause V := ({((0, 0), true), ((0, 1), true), ((0, 2), true)} : Clause V)
def k0 : KLine V := kLineOfClause c0
def p0 : List (KLine V) := k0 :: p51
theorem d0 : IsResKDerivation 2 F p0 :=
  IsResKDerivation.ax d51 ⟨c0, Set.mem_union_left _ ⟨0, by decide +kernel⟩, rfl⟩ (unitc _)

def c21 : Clause V := ({((2, 2), false), ((3, 2), false)} : Clause V)
def k21 : KLine V := kLineOfClause c21
def p21 : List (KLine V) := k21 :: p0
theorem d21 : IsResKDerivation 2 F p21 :=
  IsResKDerivation.ax d0 ⟨c21, Set.mem_union_right _ ⟨2, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def c19 : Clause V := ({((1, 2), false), ((2, 2), false)} : Clause V)
def k19 : KLine V := kLineOfClause c19
def p19 : List (KLine V) := k19 :: p21
theorem d19 : IsResKDerivation 2 F p19 :=
  IsResKDerivation.ax d21 ⟨c19, Set.mem_union_right _ ⟨1, 2, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k24 : KLine V := {({((1, 2), false), ((3, 2), false)} : KTerm V), ({((2, 2), false)} : KTerm V)}
def p24 : List (KLine V) := k24 :: p19
theorem d24 : IsResKDerivation 2 F p24 :=
  IsResKDerivation.andIntro (C := k21) (D := k19) (R := k24) d19 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((3, 2), false)} : KTerm V), ({((1, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel⟩ (by decide +kernel)

def k36 : KLine V := {({((1, 1), true)} : KTerm V), ({((2, 2), false)} : KTerm V), ({((3, 1), true)} : KTerm V)}
def p36 : List (KLine V) := k36 :: p24
theorem d36 : IsResKDerivation 2 F p36 :=
  IsResKDerivation.cut (C := k24) (D := k35) (R := k36) d24 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))) ⟨({((1, 2), false), ((3, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c20 : Clause V := ({((1, 2), false), ((3, 2), false)} : Clause V)
def k20 : KLine V := kLineOfClause c20
def p20 : List (KLine V) := k20 :: p36
theorem d20 : IsResKDerivation 2 F p20 :=
  IsResKDerivation.ax d36 ⟨c20, Set.mem_union_right _ ⟨1, 3, 2, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k482 : KLine V := {({((1, 0), true)} : KTerm V), ({((1, 1), true)} : KTerm V), ({((3, 2), false)} : KTerm V)}
def p482 : List (KLine V) := k482 :: p20
theorem d482 : IsResKDerivation 2 F p482 :=
  IsResKDerivation.cut (C := k1) (D := k20) (R := k482) d20 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))) (List.Mem.head _) ⟨({((1, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k29 : KLine V := {({((1, 0), true)} : KTerm V), ({((1, 1), true)} : KTerm V), ({((3, 0), true)} : KTerm V), ({((3, 1), true)} : KTerm V)}
def p29 : List (KLine V) := k29 :: p482
theorem d29 : IsResKDerivation 2 F p29 :=
  IsResKDerivation.cut (C := k482) (D := k3) (R := k29) d482 (List.Mem.head _) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))) ⟨({((3, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k37 : KLine V := {({((1, 1), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((2, 2), true)} : KTerm V), ({((3, 1), true)} : KTerm V)}
def p37 : List (KLine V) := k37 :: p29
theorem d37 : IsResKDerivation 2 F p37 :=
  IsResKDerivation.cut (C := k823) (D := k29) (R := k37) d29 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) (List.Mem.head _) ⟨({((1, 0), false), ((3, 0), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k38 : KLine V := {({((1, 1), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((3, 1), true)} : KTerm V)}
def p38 : List (KLine V) := k38 :: p37
theorem d38 : IsResKDerivation 2 F p38 :=
  IsResKDerivation.cut (C := k36) (D := k37) (R := k38) d37 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))) (List.Mem.head _) ⟨({((2, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c10 : Clause V := ({((0, 1), false), ((1, 1), false)} : Clause V)
def k10 : KLine V := kLineOfClause c10
def p10 : List (KLine V) := k10 :: p38
theorem d10 : IsResKDerivation 2 F p10 :=
  IsResKDerivation.ax d38 ⟨c10, Set.mem_union_right _ ⟨0, 1, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k46 : KLine V := {({((0, 1), false)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((3, 1), true)} : KTerm V)}
def p46 : List (KLine V) := k46 :: p10
theorem d46 : IsResKDerivation 2 F p46 :=
  IsResKDerivation.cut (C := k38) (D := k10) (R := k46) d10 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c12 : Clause V := ({((0, 1), false), ((3, 1), false)} : Clause V)
def k12 : KLine V := kLineOfClause c12
def p12 : List (KLine V) := k12 :: p46
theorem d12 : IsResKDerivation 2 F p12 :=
  IsResKDerivation.ax d46 ⟨c12, Set.mem_union_right _ ⟨0, 3, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k3176 : KLine V := {({((0, 1), false)} : KTerm V), ({((2, 1), true)} : KTerm V)}
def p3176 : List (KLine V) := k3176 :: p12
theorem d3176 : IsResKDerivation 2 F p3176 :=
  IsResKDerivation.cut (C := k46) (D := k12) (R := k3176) d12 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((3, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c11 : Clause V := ({((0, 1), false), ((2, 1), false)} : Clause V)
def k11 : KLine V := kLineOfClause c11
def p11 : List (KLine V) := k11 :: p3176
theorem d11 : IsResKDerivation 2 F p11 :=
  IsResKDerivation.ax d3176 ⟨c11, Set.mem_union_right _ ⟨0, 2, 1, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k48 : KLine V := {({((0, 1), false)} : KTerm V)}
def p48 : List (KLine V) := k48 :: p11
theorem d48 : IsResKDerivation 2 F p48 :=
  IsResKDerivation.cut (C := k3176) (D := k11) (R := k48) d11 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((2, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k343 : KLine V := {({((0, 0), true)} : KTerm V), ({((0, 2), true)} : KTerm V)}
def p343 : List (KLine V) := k343 :: p48
theorem d343 : IsResKDerivation 2 F p343 :=
  IsResKDerivation.cut (C := k0) (D := k48) (R := k343) d48 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))) (List.Mem.head _) ⟨({((0, 1), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k30 : KLine V := {({((1, 0), true)} : KTerm V), ({((2, 1), false)} : KTerm V), ({((3, 0), true)} : KTerm V)}
def p30 : List (KLine V) := k30 :: p343
theorem d30 : IsResKDerivation 2 F p30 :=
  IsResKDerivation.cut (C := k23) (D := k29) (R := k30) d343 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))) ⟨({((1, 1), false), ((3, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k28 : KLine V := {({((1, 0), true)} : KTerm V), ({((2, 2), false)} : KTerm V), ({((3, 0), true)} : KTerm V)}
def p28 : List (KLine V) := k28 :: p30
theorem d28 : IsResKDerivation 2 F p28 :=
  IsResKDerivation.cut (C := k24) (D := k27) (R := k28) d30 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))))))) ⟨({((1, 2), false), ((3, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k31 : KLine V := {({((1, 0), true)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((2, 1), true)} : KTerm V), ({((3, 0), true)} : KTerm V)}
def p31 : List (KLine V) := k31 :: p28
theorem d31 : IsResKDerivation 2 F p31 :=
  IsResKDerivation.cut (C := k2) (D := k28) (R := k31) d28 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({((2, 2), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k32 : KLine V := {({((1, 0), true)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V)}
def p32 : List (KLine V) := k32 :: p31
theorem d32 : IsResKDerivation 2 F p32 :=
  IsResKDerivation.cut (C := k30) (D := k31) (R := k32) d31 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _) ⟨({((2, 1), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c4 : Clause V := ({((0, 0), false), ((1, 0), false)} : Clause V)
def k4 : KLine V := kLineOfClause c4
def p4 : List (KLine V) := k4 :: p32
theorem d4 : IsResKDerivation 2 F p4 :=
  IsResKDerivation.ax d32 ⟨c4, Set.mem_union_right _ ⟨0, 1, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k43 : KLine V := {({((0, 0), false)} : KTerm V), ({((2, 0), true)} : KTerm V), ({((3, 0), true)} : KTerm V)}
def p43 : List (KLine V) := k43 :: p4
theorem d43 : IsResKDerivation 2 F p43 :=
  IsResKDerivation.cut (C := k32) (D := k4) (R := k43) d4 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((1, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c6 : Clause V := ({((0, 0), false), ((3, 0), false)} : Clause V)
def k6 : KLine V := kLineOfClause c6
def p6 : List (KLine V) := k6 :: p43
theorem d6 : IsResKDerivation 2 F p6 :=
  IsResKDerivation.ax d43 ⟨c6, Set.mem_union_right _ ⟨0, 3, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k1925 : KLine V := {({((0, 0), false)} : KTerm V), ({((2, 0), true)} : KTerm V)}
def p1925 : List (KLine V) := k1925 :: p6
theorem d1925 : IsResKDerivation 2 F p1925 :=
  IsResKDerivation.cut (C := k43) (D := k6) (R := k1925) d6 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((3, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def c5 : Clause V := ({((0, 0), false), ((2, 0), false)} : Clause V)
def k5 : KLine V := kLineOfClause c5
def p5 : List (KLine V) := k5 :: p1925
theorem d5 : IsResKDerivation 2 F p5 :=
  IsResKDerivation.ax d1925 ⟨c5, Set.mem_union_right _ ⟨0, 2, 0, by decide, by decide +kernel⟩, rfl⟩ (unitc _)

def k45 : KLine V := {({((0, 0), false)} : KTerm V)}
def p45 : List (KLine V) := k45 :: p5
theorem d45 : IsResKDerivation 2 F p45 :=
  IsResKDerivation.cut (C := k1925) (D := k5) (R := k45) d5 (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _) ⟨({((2, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k53 : KLine V := {({((0, 2), true)} : KTerm V)}
def p53 : List (KLine V) := k53 :: p45
theorem d53 : IsResKDerivation 2 F p53 :=
  IsResKDerivation.cut (C := k343) (D := k45) (R := k53) d45 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))) (List.Mem.head _) ⟨({((0, 0), true)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def k54 : KLine V := ∅
def p54 : List (KLine V) := k54 :: p53
theorem d54 : IsResKDerivation 2 F p54 :=
  IsResKDerivation.cut (C := k51) (D := k53) (R := k54) d53 (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))))))))))))))) (List.Mem.head _) ⟨({((0, 2), false)} : KTerm V), by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem checked : ∃ π : List (KLine V),
    IsResKRefutation 2 (PHP 4 3) π ∧ π.length ≤ 54 :=
  ⟨p54, ⟨d54, List.Mem.head _⟩, by decide +kernel⟩

end PEqualNP.Outside.ContributionPHP43
