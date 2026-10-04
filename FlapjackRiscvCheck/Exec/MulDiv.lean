import FlapjackRiscvCheck.Exec.ALU
import Flapjack.RiscV.L3.Defs.Multiply
import Flapjack.RiscV.L3.Defs.Divide
import FlapjackRiscvCheck.BridgeM

/-!
# M extension: MUL, MULHU, DIV

L3 `dfn'MUL` / `dfn'MULHU` / `dfn'DIV` against Sail `execute_MUL` /
`execute_DIV`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

/-- Sail `execute_MUL` writes `v` to `rd` and retires; L3 writes the same `v`. -/
def MulSim (op : mul_op) (l3op : BitVec 5 × BitVec 5 × BitVec 5 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd rs1 rs2 : BitVec 5) : Prop :=
  ∃ v, runSail (execute_MUL (.Regidx rs2) (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, rs1, rs2) s = «write'GPR» (v, rd) s

macro "mul_reads" h:ident : tactic =>
  `(tactic| (
    simp only [execute_MUL, bind_assoc, pure_bind]
    delta Functions.xlen
    rw [runSail_bind_of_eq (runSail_rX_bits (($h).gpr _)),
      runSail_bind_of_eq (runSail_rX_bits (($h).gpr _))]
    simp only [runSail_bind, runSail_pure]))

theorem mul_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    MulSim ⟨.Low, .Signed, .Signed⟩ «dfn'MUL» s t rd rs1 rs2 := by
  refine ⟨GPR rs1 s * GPR rs2 s, ?_, rfl⟩
  mul_reads h
  rw [sail_mul_low, runSail_wX_bits]

theorem mulhu_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 rs2 : BitVec 5) :
    MulSim ⟨.High, .Unsigned, .Unsigned⟩ «dfn'MULHU» s t rd rs1 rs2 := by
  refine ⟨BitVec.ofNat 64 ((GPR rs1 s).toNat * (GPR rs2 s).toNat / 2 ^ 64), ?_, ?_⟩
  · mul_reads h
    rw [sail_mulhu, runSail_wX_bits]
  · simp only [«dfn'MULHU», l3_in32BitMode_of_rv64 hA, Bool.false_eq_true, if_false, l3_mulhu]

def DivSim (unsigned : Bool) (l3op : BitVec 5 × BitVec 5 × BitVec 5 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd rs1 rs2 : BitVec 5) : Prop :=
  ∃ v, runSail (execute_DIV (.Regidx rs2) (.Regidx rs1) (.Regidx rd) unsigned) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, rs1, rs2) s = «write'GPR» (v, rd) s

theorem div_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    DivSim false «dfn'DIV» s t rd rs1 rs2 := by
  refine ⟨if GPR rs2 s = 0 then -1 else (GPR rs1 s).sdiv (GPR rs2 s), ?_, ?_⟩
  · simp only [execute_DIV, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_rX_bits (h.gpr _)),
      runSail_bind_of_eq (runSail_rX_bits (h.gpr _))]
    simp only [runSail_bind, runSail_wX_bits, runSail_pure, Functions.not, Bool.not_false,
      Bool.true_and, Bool.false_eq_true, if_true, if_false, beq_iff_eq, decide_eq_true_eq,
      to_bits_truncate, get_slice_int_zero, Functions.xlen]
    rw [← div_value]
    norm_num
    rfl
  · simp only [«dfn'DIV»]
    by_cases hx : GPR rs2 s = 0#64 <;> simp [hx]

end FlapjackRiscvCheck
