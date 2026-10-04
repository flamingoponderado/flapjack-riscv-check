import FlapjackRiscvCheck.Relation
import FlapjackRiscvCheck.L3.Arch
import FlapjackRiscvCheck.Bridge
import Flapjack.RiscV.L3.Defs.RegisterALU
import Flapjack.RiscV.L3.Defs.RegisterShift
import Flapjack.RiscV.L3.Defs.SetLess
import LeanRV64D.InstsEnd

/-!
# Register-register ALU instructions

L3 `dfn'<OP>` against Sail `execute_RTYPE`. Each lemma says that Sail retires
successfully, writing a value `v` to `rd`, and that the L3 instruction is
exactly `write'GPR (v, rd)`. `RegRel` preservation then follows from
`RegRel.write`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

/-- Sail `execute_RTYPE op` writes `v` to `rd` and retires, and L3's `l3op`
writes the same `v` to `rd`. -/
def RTypeSim (op : rop) (l3op : BitVec 5 × BitVec 5 × BitVec 5 → riscv_state → riscv_state)
    (s : L3State) (t : SailState) (rd rs1 rs2 : BitVec 5) : Prop :=
  ∃ v, runSail (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, sailSetGpr t rd v) ∧
    l3op (rd, rs1, rs2) s = «write'GPR» (v, rd) s

theorem RTypeSim.rel {op l3op s t rd rs1 rs2} (h : RegRel s t)
    (hs : RTypeSim op l3op s t rd rs1 rs2) :
    ∃ t', runSail (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) op) t =
      some (RETIRE_SUCCESS, t') ∧ RegRel (l3op (rd, rs1, rs2) s) t' := by
  obtain ⟨v, hrun, hl3⟩ := hs
  exact ⟨_, hrun, hl3 ▸ h.write rd v⟩

/-- Read both source registers through `RegRel`, then do the destination write,
leaving `runSail (pure RETIRE_SUCCESS) (sailSetGpr t rd <sail value>) = ...`. -/
macro "rtype_reads" h:ident : tactic =>
  `(tactic| (
    simp only [execute_RTYPE, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_rX_bits (($h).gpr _)),
      runSail_bind_of_eq (runSail_rX_bits (($h).gpr _)),
      runSail_bind_of_eq (runSail_wX_bits _ _ _)]))

macro "rtype_sail" h:ident : tactic => `(tactic| (rtype_reads $h; rfl))

theorem add_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    RTypeSim .ADD «dfn'ADD» s t rd rs1 rs2 :=
  ⟨GPR rs1 s + GPR rs2 s, by rtype_sail h, rfl⟩

theorem sub_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    RTypeSim .SUB «dfn'SUB» s t rd rs1 rs2 :=
  ⟨GPR rs1 s - GPR rs2 s, by rtype_sail h, rfl⟩

theorem and_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    RTypeSim .AND «dfn'AND» s t rd rs1 rs2 :=
  ⟨GPR rs1 s &&& GPR rs2 s, by rtype_sail h, rfl⟩

theorem or_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    RTypeSim .OR «dfn'OR» s t rd rs1 rs2 :=
  ⟨GPR rs1 s ||| GPR rs2 s, by rtype_sail h, rfl⟩

theorem xor_sim {s t} (h : RegRel s t) (rd rs1 rs2 : BitVec 5) :
    RTypeSim .XOR «dfn'XOR» s t rd rs1 rs2 :=
  ⟨GPR rs1 s ^^^ GPR rs2 s, by rtype_sail h, rfl⟩

theorem sltu_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 rs2 : BitVec 5) :
    RTypeSim .SLTU «dfn'SLTU» s t rd rs1 rs2 := by
  refine ⟨if GPR rs1 s < GPR rs2 s then 1 else 0, by rtype_reads h; rw [sail_sltu]; rfl, ?_⟩
  simp only [«dfn'SLTU», l3_in32BitMode_of_rv64 hA, Bool.false_eq_true, if_false,
    l3_holV2w_single, BitVec.ult_iff_lt]

theorem sll_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 rs2 : BitVec 5) :
    RTypeSim .SLL «dfn'SLL» s t rd rs1 rs2 := by
  refine ⟨GPR rs1 s <<< ((GPR rs2 s).toNat % 64), by rtype_reads h; rw [sail_shift_bits_left]; rfl, ?_⟩
  simp only [«dfn'SLL», l3_in32BitMode_of_rv64 hA, Bool.false_eq_true, if_false,
    l3_shamt6]

theorem srl_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 rs2 : BitVec 5) :
    RTypeSim .SRL «dfn'SRL» s t rd rs1 rs2 := by
  refine ⟨GPR rs1 s >>> ((GPR rs2 s).toNat % 64), by rtype_reads h; rw [sail_shift_bits_right]; rfl, ?_⟩
  simp only [«dfn'SRL», l3_in32BitMode_of_rv64 hA, Bool.false_eq_true, if_false,
    l3_shamt6]

theorem sra_sim {s t} (h : RegRel s t) (hA : (MCSR s).mcpuid.ArchBase = 2)
    (rd rs1 rs2 : BitVec 5) :
    RTypeSim .SRA «dfn'SRA» s t rd rs1 rs2 := by
  refine ⟨(GPR rs1 s).sshiftRight ((GPR rs2 s).toNat % 64), by rtype_reads h; rw [sail_shift_bits_right_arith]; rfl, ?_⟩
  simp only [«dfn'SRA», l3_in32BitMode_of_rv64 hA, Bool.false_eq_true, if_false,
    l3_shamt6]

end FlapjackRiscvCheck
