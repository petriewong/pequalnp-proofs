import Std.Tactic.BVDecide
namespace ProofLantern.Crown.OneHelperRows
def lift (x : BitVec 7) : BitVec 22 :=
  (if x.getLsbD 0 then 8065#22 else 0#22) |||
  (if x.getLsbD 1 then 254082#22 else 0#22) |||
  (if x.getLsbD 2 then 3940612#22 else 0#22) |||
  (if x.getLsbD 3 then 279048#22 else 0#22) |||
  (if x.getLsbD 4 then 558096#22 else 0#22) |||
  (if x.getLsbD 5 then 1116192#22 else 0#22) |||
  (if x.getLsbD 6 then 2232384#22 else 0#22)
theorem noModel (s t u v : BitVec 7) :
    (lift s &&& (lift t ||| (lift u &&& lift v))) ≠ 4194176#22 := by
  unfold lift
  bv_decide (config := { timeout := 90 })
end ProofLantern.Crown.OneHelperRows
