import FlapjackRiscvCheck.L3.Regs
import Flapjack.RiscV.L3.Defs.UpperJump

/-!
# L3 control transfer

`l3NextPC s` is the PC that `NextRISCV` commits after `Run`: the `BranchTo`
target if one was recorded, otherwise `PC + Skip`.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3

def l3NextPC (s : riscv_state) : Option (BitVec 64) :=
  match NextFetch s with
  | none => some (PC s + Skip s)
  | some (.BranchTo a) => some a
  | some _ => none

@[simp] theorem l3_GPR_branchTo (a : BitVec 64) (s : riscv_state) (n : BitVec 5) :
    GPR n (branchTo a s) = GPR n s := by
  simp [branchTo, «write'NextFetch», GPR, gpr]

@[simp] theorem l3_PC_branchTo (a : BitVec 64) (s : riscv_state) :
    PC (branchTo a s) = PC s := rfl

@[simp] theorem l3_NextFetch_branchTo (a : BitVec 64) (s : riscv_state) :
    NextFetch (branchTo a s) = some (.BranchTo a) := by
  simp [branchTo, «write'NextFetch», NextFetch, holUpdate]

@[simp] theorem l3_NextFetch_write'GPR (s : riscv_state) (n : BitVec 5) (v : BitVec 64) :
    NextFetch («write'GPR» (v, n) s) = NextFetch s := by
  simp only [«write'GPR», «write'gpr», NextFetch]
  split <;> rfl

@[simp] theorem l3_Skip_write'GPR (s : riscv_state) (n : BitVec 5) (v : BitVec 64) :
    Skip («write'GPR» (v, n) s) = Skip s := by
  simp only [«write'GPR», «write'gpr», Skip]
  split <;> rfl

theorem l3NextPC_branchTo (a : BitVec 64) (s : riscv_state) :
    l3NextPC (branchTo a s) = some a := by
  simp [l3NextPC]

theorem l3NextPC_write'GPR (s : riscv_state) (n : BitVec 5) (v : BitVec 64) :
    l3NextPC («write'GPR» (v, n) s) = l3NextPC s := by
  simp [l3NextPC, l3_PC_write'GPR]

@[simp] theorem l3_MEM8_branchTo (a : BitVec 64) (s : riscv_state) :
    (branchTo a s).MEM8 = s.MEM8 := rfl

@[simp] theorem l3_MEM8_write'GPR (s : riscv_state) (n : BitVec 5) (v : BitVec 64) :
    («write'GPR» (v, n) s).MEM8 = s.MEM8 := by
  simp only [«write'GPR», «write'gpr»]
  split <;> rfl

end FlapjackRiscvCheck
