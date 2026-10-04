import FlapjackRiscvCheck.Sail.Regs

/-!
# Writing a GPR leaves the other Sail registers alone
-/

namespace FlapjackRiscvCheck

open LeanRV64D

/-- The Sail registers `x1` .. `x31`. -/
def Register.isGpr : Register → Bool
  | .x1 | .x2 | .x3 | .x4 | .x5 | .x6 | .x7 | .x8 | .x9 | .x10 | .x11 | .x12 | .x13 | .x14
  | .x15 | .x16 | .x17 | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26
  | .x27 | .x28 | .x29 | .x30 | .x31 => true
  | _ => false

theorem sailSetGpr_get?_of_not_gpr (t : SailState) (n : BitVec 5) (v : BitVec 64)
    {r : Register} (hr : Register.isGpr r = false) :
    (sailSetGpr t n v).regs.get? r = t.regs.get? r := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailSetGpr, Std.ExtDHashMap.get?_insert] <;>
    (intro h; subst h; simp [Register.isGpr] at hr)

theorem sailSetGpr_mem (t : SailState) (n : BitVec 5) (v : BitVec 64) :
    (sailSetGpr t n v).mem = t.mem := by
  unfold sailSetGpr; split <;> rfl

end FlapjackRiscvCheck
