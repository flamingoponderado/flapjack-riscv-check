import FlapjackRiscvCheck.Relation
import FlapjackRiscvCheck.Sail.RegsOther
import FlapjackRiscvCheck.L3.Control
import LeanRV64D.InstsEnd

/-!
# The execute-level contract

Every per-instruction lemma has the shape

  `ExecPre s t → ∃ t', runSail (execute_X ...) t = some (RETIRE_SUCCESS, t') ∧ ExecPost s' t t'`

where `s'` is L3's `Run` result. `ExecPre` is what holds between Sail's
`set_next_pc (PC + 4)` and `execute` in `try_step`, matched with L3 after
`Fetch` of a 4-byte instruction. `ExecPost` relates the results: registers,
the next PC (Sail `nextPC` against L3 `l3NextPC`), and a frame condition on
the Sail registers the instruction may not touch.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

structure ExecPre (s : L3State) (t : SailState) : Prop where
  rel : RegRel s t
  nextFetch : NextFetch s = none
  skip : Skip s = 4
  nextPC : t.regs.get? Register.nextPC = some (PC s + 4)
  rv64 : (MCSR s).mcpuid.ArchBase = 2
  bareVM : (s.c_MCSR s.procID).mstatus.VM = 0#5
  pcEven : (PC s).getLsbD 0 = false
  misaC : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_C m = 1
  machine : t.regs.get? Register.cur_privilege = some .Machine
  noLandingPads : ∃ c, t.regs.get? Register.mseccfg = some c ∧ _get_Seccfg_MLPE c = 0

/-- Sail registers other than `x1..x31` and `nextPC` are unchanged. -/
def SailRegFrame (t t' : SailState) : Prop :=
  ∀ r, Register.isGpr r = false → r ≠ Register.nextPC → t'.regs.get? r = t.regs.get? r

structure ExecPost (s' : L3State) (t t' : SailState) : Prop where
  rel : RegRel s' t'
  nextPC : t'.regs.get? Register.nextPC = l3NextPC s'
  frame : SailRegFrame t t'
  mem : t'.mem = t.mem

theorem ExecPre.l3NextPC {s t} (h : ExecPre s t) : l3NextPC s = some (PC s + 4) := by
  simp [FlapjackRiscvCheck.l3NextPC, h.nextFetch, h.skip]

/-- An instruction that only writes `v` to `rd` on both sides meets the contract. -/
theorem ExecPost.of_write {s t} (h : ExecPre s t) (rd : BitVec 5) (v : BitVec 64) :
    ExecPost («write'GPR» (v, rd) s) t (sailSetGpr t rd v) where
  rel := h.rel.write rd v
  nextPC := by
    rw [sailSetGpr_get?_of_not_gpr _ _ _ rfl, l3NextPC_write'GPR, h.l3NextPC, h.nextPC]
  frame _ hr _ := sailSetGpr_get?_of_not_gpr _ _ _ hr
  mem := sailSetGpr_mem _ _ _

end FlapjackRiscvCheck
