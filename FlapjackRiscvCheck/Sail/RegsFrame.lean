import FlapjackRiscvCheck.Sail.Regs

/-!
# Read-after-write for Sail integer registers

Proved by a 32 × 32 case split (about 100 s), so it has its own module.
-/

namespace FlapjackRiscvCheck

open LeanRV64D

set_option maxHeartbeats 4000000 in
theorem sailGpr_sailSetGpr (t : SailState) (n m : BitVec 5) (v : BitVec 64) :
    sailGpr (sailSetGpr t n v) m = if m = n ∧ n ≠ 0 then some v else sailGpr t m := by
  have hn := n.isLt
  have hm := m.isLt
  generalize hk : n.toNat = k at hn
  generalize hj : m.toNat = j at hm
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  obtain rfl : m = BitVec.ofNat 5 j := by rw [← hj]; simp
  interval_cases k <;> interval_cases j <;>
    simp [sailGpr, sailSetGpr, Std.ExtDHashMap.get?_insert]

end FlapjackRiscvCheck
