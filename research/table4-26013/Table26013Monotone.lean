import PEqualNP.Defs.CircuitLowerBounds
import Std.Tactic.BVDecide

open PEqualNP.CircuitLowerBounds
namespace Table26013Monotone

def circ : Circuit :=
  ⟨[⟨.or, [1,4]⟩, ⟨.or, [2,5]⟩, ⟨.or, [8,9]⟩, ⟨.or, [9,7]⟩,
    ⟨.and, [8,11]⟩, ⟨.or, [0,12]⟩, ⟨.or, [6,3]⟩, ⟨.and, [10,14]⟩,
    ⟨.or, [13,15]⟩],16⟩

def hot (i j : BitVec 2) : List Bool :=
  [i==0, i==1, i==2, i==3, j==0, j==1, j==2, j==3]

def table (i j : BitVec 2) : Bool :=
  (i==0) || ((i==1) && (j != 0)) ||
  ((i==2) && ((j==0) || (j==2))) ||
  ((i==3) && ((j==0) || (j==1)))

def expr (i j : BitVec 2) : Bool :=
  let a := (i == 1) || (j == 0)
  let b := (i == 2) || (j == 1)
  (i == 0 || (a && (b || (j == 3)))) ||
    ((a || b) && ((j == 2) || (i == 3)))

theorem eval_eq (i j : BitVec 2) : circ.eval (hot i j) = expr i j := by
  simp [circ, hot, Circuit.eval, Circuit.wires, GateOp.eval, expr, List.getD_eq_getElem?_getD]

theorem exact_on_promise (i j : BitVec 2) : circ.eval (hot i j) = table i j := by
  rw [eval_eq]
  unfold expr table
  bv_decide

example : circ.size = 9 := by decide
example : circ.gates.all (fun g => (match g.op with | .and | .or => true | _ => false)
    && (g.inputs.length == 2)) = true := by decide
example : (circ.gates.zipIdx).all (fun (g,i) => g.inputs.all (· < 8+i)) = true := by decide

end Table26013Monotone
