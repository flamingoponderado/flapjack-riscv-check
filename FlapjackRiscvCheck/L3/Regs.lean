import Flapjack.RiscV.L3.Defs
import Flapjack.RiscV.L3.Defs.ReadInst

/-!
# L3 general-purpose registers

Read-after-write for the L3 `GPR` / `write'GPR` accessors.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3

theorem l3_GPR_write'GPR (s : riscv_state) (n m : BitVec 5) (v : BitVec 64) :
    GPR m («write'GPR» (v, n) s) = if m = n ∧ n ≠ 0 then v else GPR m s := by
  simp only [GPR, gpr, «write'GPR», «write'gpr»]
  by_cases hn : n = 0 <;> by_cases hm0 : m = 0 <;> by_cases hmn : m = n <;>
    subst_vars <;> simp_all [holUpdate] <;> exact fun h => absurd h.symm hmn

theorem l3_PC_write'GPR (s : riscv_state) (n : BitVec 5) (v : BitVec 64) :
    PC («write'GPR» (v, n) s) = PC s := by
  simp only [«write'GPR», «write'gpr», PC]
  split <;> rfl

end FlapjackRiscvCheck
