import PEqualNP.Defs.MetaComplexity
import Std.Tactic.BVDecide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace G11ProjectControl

def g11 : Circuit := ⟨[⟨.or, [9,10]⟩,⟨.and, [0,11]⟩,⟨.or, [4,8]⟩,⟨.and, [1,13]⟩,⟨.or, [6,7]⟩,⟨.and, [3,15]⟩,⟨.or, [2,8]⟩,⟨.or, [17,9]⟩,⟨.and, [5,18]⟩,⟨.or, [6,9]⟩,⟨.and, [7,20]⟩,⟨.or, [4,9]⟩,⟨.and, [8,22]⟩,⟨.or, [2,4]⟩,⟨.or, [24,6]⟩,⟨.and, [10,25]⟩,⟨.or, [12,14]⟩,⟨.or, [27,16]⟩,⟨.or, [28,19]⟩,⟨.or, [29,21]⟩,⟨.or, [30,23]⟩,⟨.or, [31,26]⟩],32⟩

def inputs (x : BitVec 11) : List Bool := [x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7],x[8],x[9],x[10]]

def g11BVEval (x : BitVec 11) : Bool :=
  let w0 := x[0]
  let w1 := x[1]
  let w2 := x[2]
  let w3 := x[3]
  let w4 := x[4]
  let w5 := x[5]
  let w6 := x[6]
  let w7 := x[7]
  let w8 := x[8]
  let w9 := x[9]
  let w10 := x[10]
  let w11 := w9 || w10
  let w12 := w0 && w11
  let w13 := w4 || w8
  let w14 := w1 && w13
  let w15 := w6 || w7
  let w16 := w3 && w15
  let w17 := w2 || w8
  let w18 := w17 || w9
  let w19 := w5 && w18
  let w20 := w6 || w9
  let w21 := w7 && w20
  let w22 := w4 || w9
  let w23 := w8 && w22
  let w24 := w2 || w4
  let w25 := w24 || w6
  let w26 := w10 && w25
  let w27 := w12 || w14
  let w28 := w27 || w16
  let w29 := w28 || w19
  let w30 := w29 || w21
  let w31 := w30 || w23
  let w32 := w31 || w26
  w32

def g11BVSpec (x : BitVec 11) : Bool :=
  (x[0] && x[9]) ||
  (x[0] && x[10]) ||
  (x[1] && x[4]) ||
  (x[1] && x[8]) ||
  (x[2] && x[5]) ||
  (x[2] && x[10]) ||
  (x[3] && x[6]) ||
  (x[3] && x[7]) ||
  (x[4] && x[8]) ||
  (x[4] && x[10]) ||
  (x[5] && x[8]) ||
  (x[5] && x[9]) ||
  (x[6] && x[7]) ||
  (x[6] && x[10]) ||
  (x[7] && x[9]) ||
  (x[8] && x[9])


example : g11.size = 22 := by decide

example (x : BitVec 11) : g11BVEval x = g11BVSpec x := by
  unfold g11BVEval g11BVSpec
  bv_decide

-- Evaluate the actual upstream Circuit, not only the stand-alone control.
theorem project_matches_expression (x : BitVec 11) :
    g11.eval (inputs x) = g11BVEval x := by
  simp [g11, inputs, Circuit.eval, Circuit.wires, GateOp.eval, g11BVEval,
    List.getD_eq_getElem?_getD]

end G11ProjectControl
