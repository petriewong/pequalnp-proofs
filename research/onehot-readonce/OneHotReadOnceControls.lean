import PEqualNP.Defs.CircuitLowerBounds
import Std.Tactic.BVDecide

open PEqualNP.CircuitLowerBounds
namespace OneHotReadOnceControls

def hot (i j : BitVec 2) : List Bool :=
  [i == 0, i == 1, i == 2, i == 3, j == 0, j == 1, j == 2, j == 3]

def overlap : Circuit :=
  ⟨[⟨.or, [4,6]⟩, ⟨.and, [0,8]⟩, ⟨.and, [1,5]⟩, ⟨.and, [2,4]⟩,
    ⟨.or, [9,10]⟩, ⟨.or, [12,11]⟩], 13⟩

def matching : Circuit :=
  ⟨[⟨.and, [0,4]⟩, ⟨.and, [1,5]⟩, ⟨.and, [2,6]⟩,
    ⟨.or, [8,9]⟩, ⟨.or, [11,10]⟩], 12⟩

def overlapTable (i j : BitVec 2) : Bool :=
  ((i == 0) && (j == 0)) || ((i == 0) && (j == 2)) ||
  ((i == 1) && (j == 1)) || ((i == 2) && (j == 0))

def matchingTable (i j : BitVec 2) : Bool := (i == j) && (i != 3)

theorem overlap_correct (i j : BitVec 2) :
    overlap.eval (hot i j) = overlapTable i j := by
  simp [overlap, hot, Circuit.eval, Circuit.wires, GateOp.eval,
    overlapTable, List.getD_eq_getElem?_getD] <;> bv_decide

theorem matching_correct (i j : BitVec 2) :
    matching.eval (hot i j) = matchingTable i j := by
  simp [matching, hot, Circuit.eval, Circuit.wires, GateOp.eval,
    matchingTable, List.getD_eq_getElem?_getD] <;> bv_decide

example : overlap.size = 6 := by decide
example : matching.size = 5 := by decide
example : [overlap, matching].all (fun q =>
    q.gates.all (fun g => (match g.op with | .and | .or => true | _ => false)
      && (g.inputs.length == 2)) &&
    (q.gates.zipIdx).all (fun (g,i) => g.inputs.all (· < 8+i))) = true := by decide

end OneHotReadOnceControls
