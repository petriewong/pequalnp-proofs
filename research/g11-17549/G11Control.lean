import Std.Tactic.BVDecide

def g11Edges : List (Nat × Nat) := [
  (0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
  (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

def g11Circuit : List (Nat × Nat × Bool) := [(9,10,true), (0,11,false), (4,8,true), (1,13,false), (6,7,true), (3,15,false), (2,8,true), (17,9,true), (5,18,false), (6,9,true), (7,20,false), (4,9,true), (8,22,false), (2,4,true), (24,6,true), (10,25,false), (12,14,true), (27,16,true), (28,19,true), (29,21,true), (30,23,true), (31,26,true)]

def g11Step (w : Array Bool) (g : Nat × Nat × Bool) : Array Bool :=
  let a := w[g.1]?.getD false
  let b := w[g.2.1]?.getD false
  w.push (if g.2.2 then a || b else a && b)

def g11Eval (mask : Nat) : Bool :=
  let init := (List.range 11).map (fun j => mask.testBit j)
  (g11Circuit.foldl g11Step init.toArray)[32]?.getD false

def g11Spec (mask : Nat) : Bool :=
  g11Edges.any (fun (u,v) => mask.testBit u && mask.testBit v)

example : g11Circuit.length = 22 := by decide

example : (g11Circuit.zipIdx).all (fun (g,i) => g.1 < 11 + i && g.2.1 < 11 + i) = true := by decide

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

example (x : BitVec 11) : g11BVEval x = g11BVSpec x := by
  unfold g11BVEval g11BVSpec
  bv_decide
