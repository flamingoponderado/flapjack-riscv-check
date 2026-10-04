import FlapjackRiscvCheck.Sail.RegsFrame
import FlapjackRiscvCheck.L3.Regs

/-!
# Relating L3 and Sail states

`RegRel s t`: the integer registers and the PC agree. The L3 side is read
through `GPR`, which returns `0` for `x0` whatever `c_gpr` stores there.

Memory and the side invariants (`L3Inv`, `SailInv`) are still to come; see
`docs/PLAN.md`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D Flapjack.RiscV.L3

structure RegRel (s : L3State) (t : SailState) : Prop where
  gpr : ∀ n, sailGpr t n = some (GPR n s)
  pc : t.regs.get? Register.PC = some (PC s)

theorem sailSetGpr_get?_PC (t : SailState) (n : BitVec 5) (v : BitVec 64) :
    (sailSetGpr t n v).regs.get? Register.PC = t.regs.get? Register.PC := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailSetGpr, Std.ExtDHashMap.get?_insert]

theorem sailSetGpr_get?_nextPC (t : SailState) (n : BitVec 5) (v : BitVec 64) :
    (sailSetGpr t n v).regs.get? Register.nextPC = t.regs.get? Register.nextPC := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailSetGpr, Std.ExtDHashMap.get?_insert]

/-- Writing the same value to the same register on both sides preserves `RegRel`. -/
theorem RegRel.write {s : L3State} {t : SailState} (h : RegRel s t) (n : BitVec 5)
    (v : BitVec 64) : RegRel («write'GPR» (v, n) s) (sailSetGpr t n v) where
  gpr m := by
    rw [sailGpr_sailSetGpr, l3_GPR_write'GPR]
    split
    · rfl
    · exact h.gpr m
  pc := by rw [sailSetGpr_get?_PC, l3_PC_write'GPR]; exact h.pc

end FlapjackRiscvCheck
