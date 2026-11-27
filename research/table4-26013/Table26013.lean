import PEqualNP.Defs.CircuitLowerBounds
import Std.Tactic.BVDecide

open PEqualNP.CircuitLowerBounds
namespace Table26013

def circ : Circuit :=
  ⟨[⟨.or, [5,7]⟩, ⟨.or, [6,7]⟩, ⟨.and, [1,4]⟩, ⟨.and, [2,8]⟩,
    ⟨.and, [3,9]⟩, ⟨.or, [10,11]⟩, ⟨.or, [13,12]⟩, ⟨.not, [14]⟩],15⟩

def hot (i j : BitVec 2) : List Bool :=
  [i==0, i==1, i==2, i==3, j==0, j==1, j==2, j==3]

def table (i j : BitVec 2) : Bool :=
  (i==0) || ((i==1) && (j != 0)) ||
  ((i==2) && ((j==0) || (j==2))) ||
  ((i==3) && ((j==0) || (j==1)))

def expr (i j : BitVec 2) : Bool :=
  !(((i==1) && (j==0)) || ((i==2) && ((j==1) || (j==3))) ||
    ((i==3) && ((j==2) || (j==3))))

theorem shape : circ.size = 8 := by decide

theorem eval_eq (i j : BitVec 2) : circ.eval (hot i j) = expr i j := by
  simp [circ, hot, Circuit.eval, Circuit.wires, GateOp.eval, expr,
    List.getD_eq_getElem?_getD, Bool.or_assoc]

theorem exact_on_promise (i j : BitVec 2) : circ.eval (hot i j) = table i j := by
  rw [eval_eq]
  unfold expr table
  bv_decide

example : circ.gates.countP (fun g => match g.op with | .not => true | _ => false) = 1 :=
  by decide

example : circ.gates.all (fun g => g.inputs.length ≤ 2) = true := by decide

example : (circ.gates.zipIdx).all (fun (g,i) => g.inputs.all (· < 8+i)) = true := by decide

end Table26013
