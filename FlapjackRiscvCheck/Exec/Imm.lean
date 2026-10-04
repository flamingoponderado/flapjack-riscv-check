import FlapjackRiscvCheck.Exec.ALU
import Flapjack.RiscV.L3.Defs.ImmediateALU
import Flapjack.RiscV.L3.Defs.ImmediateShift
import Flapjack.RiscV.L3.Defs.UpperJump

/-!
# Immediate and upper-immediate ALU instructions

L3 `dfn'<OP>` against Sail `execute_ITYPE`, `execute_SHIFTIOP` and
`execute_UTYPE`. As in `Exec/ALU.lean`, each lemma names the value `v` written
to `rd` on both sides.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

/-! ## Bridges -/

theorem sail_sign_extend_eq {n : Nat} (x : BitVec n) :
    sign_extend (m := 64) x = BitVec.signExtend 64 x := rfl

theorem sail_shamt_imm (x : BitVec 6) :
    (Sail.BitVec.extractLsb x ((Functions.log2_xlen : Int) - 1).toNat 0).toNat = x.toNat := by
  simp [Sail.BitVec.extractLsb, Functions.log2_xlen]
  omega

theorem l3_upper_imm (imm : BitVec 20) :
    BitVec.signExtend 64 (BitVec.setWidth 32 (imm ++ BitVec.ofNat 12 0)) =
      sign_extend (m := 64) (imm +++ 0x000#12) := by
  simp [sail_sign_extend_eq]

/-! ## `execute_ITYPE` -/

/-- Sail `execute_ITYPE op` writes `v` to `rd` and retires; L3 writes the same `v`. -/
def ITypeSim (op : iop) (l3op : BitVec 5 × BitVec 5 × BitVec 12 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd rs1 : BitVec 5) (imm : BitVec 12) : Prop :=
  ∃ v, runSail (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, rs1, imm) s = «write'GPR» (v, rd) s

macro "itype_reads" h:ident : tactic =>
  `(tactic| (
    simp only [execute_ITYPE, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_rX_bits (($h).gpr _)),
      runSail_bind_of_eq (runSail_wX_bits _ _ _)]))

theorem addi_sim {s t} (h : RegRel s t) (rd rs1 : BitVec 5) (imm : BitVec 12) :
    ITypeSim .ADDI «dfn'ADDI» s t rd rs1 imm :=
  ⟨GPR rs1 s + BitVec.signExtend 64 imm, by itype_reads h; rfl, rfl⟩

theorem andi_sim {s t} (h : RegRel s t) (rd rs1 : BitVec 5) (imm : BitVec 12) :
    ITypeSim .ANDI «dfn'ANDI» s t rd rs1 imm :=
  ⟨GPR rs1 s &&& BitVec.signExtend 64 imm, by itype_reads h; rfl, rfl⟩

theorem ori_sim {s t} (h : RegRel s t) (rd rs1 : BitVec 5) (imm : BitVec 12) :
    ITypeSim .ORI «dfn'ORI» s t rd rs1 imm :=
  ⟨GPR rs1 s ||| BitVec.signExtend 64 imm, by itype_reads h; rfl, rfl⟩

theorem xori_sim {s t} (h : RegRel s t) (rd rs1 : BitVec 5) (imm : BitVec 12) :
    ITypeSim .XORI «dfn'XORI» s t rd rs1 imm :=
  ⟨GPR rs1 s ^^^ BitVec.signExtend 64 imm, by itype_reads h; rfl, rfl⟩

theorem ITypeSim.rel {op l3op s t rd rs1 imm} (h : RegRel s t)
    (hs : ITypeSim op l3op s t rd rs1 imm) :
    ∃ t', runSail (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, t') ∧ RegRel (l3op (rd, rs1, imm) s) t' := by
  obtain ⟨v, hrun, hl3⟩ := hs
  exact ⟨_, hrun, hl3 ▸ h.write rd v⟩

/-! ## `execute_SHIFTIOP` -/

def ShiftISim (op : sop) (l3op : BitVec 5 × BitVec 5 × BitVec 6 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd rs1 : BitVec 5) (shamt : BitVec 6) : Prop :=
  ∃ v, runSail (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, rs1, shamt) s = «write'GPR» (v, rd) s

macro "shifti_reads" h:ident : tactic =>
  `(tactic| (
    simp only [execute_SHIFTIOP, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_rX_bits (($h).gpr _)),
      runSail_bind_of_eq (runSail_wX_bits _ _ _)]))

theorem slli_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    ShiftISim .SLLI «dfn'SLLI» s t rd rs1 shamt := by
  refine ⟨GPR rs1 s <<< shamt.toNat, ?_, ?_⟩
  · shifti_reads h
    simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq', sail_shamt_imm]
    rfl
  · simp [«dfn'SLLI», l3_in32BitMode_of_rv64 hA]

theorem srli_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    ShiftISim .SRLI «dfn'SRLI» s t rd rs1 shamt := by
  refine ⟨GPR rs1 s >>> shamt.toNat, ?_, ?_⟩
  · shifti_reads h
    simp only [Sail.shift_bits_right, BitVec.ushiftRight_eq', sail_shamt_imm]
    rfl
  · simp [«dfn'SRLI», l3_in32BitMode_of_rv64 hA]

theorem srai_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 : BitVec 5) (shamt : BitVec 6) :
    ShiftISim .SRAI «dfn'SRAI» s t rd rs1 shamt := by
  refine ⟨(GPR rs1 s).sshiftRight shamt.toNat, ?_, ?_⟩
  · shifti_reads h
    simp only [shift_bits_right_arith, Sail.BitVec.toNatInt, sail_shamt_imm]
    rfl
  · simp [«dfn'SRAI», l3_in32BitMode_of_rv64 hA]

theorem ShiftISim.rel {op l3op s t rd rs1 shamt} (h : RegRel s t)
    (hs : ShiftISim op l3op s t rd rs1 shamt) :
    ∃ t', runSail (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, t') ∧ RegRel (l3op (rd, rs1, shamt) s) t' := by
  obtain ⟨v, hrun, hl3⟩ := hs
  exact ⟨_, hrun, hl3 ▸ h.write rd v⟩

/-! ## `execute_UTYPE` -/

def UTypeSim (op : uop) (l3op : BitVec 5 × BitVec 20 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd : BitVec 5) (imm : BitVec 20) : Prop :=
  ∃ v, runSail (execute_UTYPE imm (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, imm) s = «write'GPR» (v, rd) s

theorem lui_sim {s t} (rd : BitVec 5) (imm : BitVec 20) :
    UTypeSim .LUI «dfn'LUI» s t rd imm := by
  refine ⟨sign_extend (m := 64) (imm +++ 0x000#12), ?_, ?_⟩
  · simp only [execute_UTYPE, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_wX_bits _ _ _)]
    rfl
  · simp only [«dfn'LUI», l3_upper_imm]

theorem auipc_sim {s t} (h : RegRel s t) (rd : BitVec 5) (imm : BitVec 20) :
    UTypeSim .AUIPC «dfn'AUIPC» s t rd imm := by
  refine ⟨PC s + sign_extend (m := 64) (imm +++ 0x000#12), ?_, ?_⟩
  · simp only [execute_UTYPE, get_arch_pc, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_readReg h.pc),
      runSail_bind_of_eq (runSail_wX_bits _ _ _)]
    rfl
  · simp only [«dfn'AUIPC», l3_upper_imm]

theorem UTypeSim.rel {op l3op s t rd imm} (h : RegRel s t)
    (hs : UTypeSim op l3op s t rd imm) :
    ∃ t', runSail (execute_UTYPE imm (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, t') ∧ RegRel (l3op (rd, imm) s) t' := by
  obtain ⟨v, hrun, hl3⟩ := hs
  exact ⟨_, hrun, hl3 ▸ h.write rd v⟩

end FlapjackRiscvCheck
