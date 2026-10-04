import FlapjackRiscvCheck.Exec.Contract
import FlapjackRiscvCheck.Sail.Jump
import FlapjackRiscvCheck.L3.Arch
import FlapjackRiscvCheck.Exec.Imm
import Flapjack.RiscV.L3.Defs.ConditionalBranch

/-!
# Conditional branches

L3 `dfn'B<cond> (rs1, rs2, offs)` against Sail
`execute_BTYPE (offs ++ 0) rs2 rs1 op`. Sail's 13-bit immediate has its low
bit fixed to zero by the encoding, while L3 stores the 12 upper bits and
shifts.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

theorem sext_append_zero {n : Nat} (hn : 0 < n) (x : BitVec n) :
    BitVec.signExtend 64 (x ++ 0#1) = BitVec.signExtend 64 x <<< 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [BitVec.getElem_signExtend, BitVec.getElem_append, hn]
  · have hi0 : i ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft,
      BitVec.msb_append, hi, hi0, hn0, decide_true, decide_false, Bool.true_and, Bool.not_false,
      BitVec.getLsbD_zero, Bool.false_and]
    by_cases h : i < n + 1
    · have h' : i - 1 < n := by omega
      simp [h, h', hi0, show i - 1 < 64 by omega]
    · have h' : ¬ i - 1 < n := by omega
      simp [h, h', hi0, hn0, show i - 1 < 64 by omega]

theorem sailGpr_insert_nextPC (t : SailState) (v : BitVec 64) (n : BitVec 5) :
    sailGpr { t with regs := t.regs.insert Register.nextPC v } n = sailGpr t n := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailGpr, Std.ExtDHashMap.get?_insert]

theorem ExecPre.post_jump {s t} (h : ExecPre s t) (a : BitVec 64) :
    ExecPost s (branchTo a s) t { t with regs := t.regs.insert Register.nextPC a } where
  rel := ⟨fun n => by rw [sailGpr_insert_nextPC, l3_GPR_branchTo]; exact h.rel.gpr n,
    by simp [Std.ExtDHashMap.get?_insert]; exact h.rel.pc⟩
  nextPC := by simp [Std.ExtDHashMap.get?_insert, l3NextPC_branchTo]
  frame r _ hr := by simp [Std.ExtDHashMap.get?_insert, Ne.symm hr]
  mem _ hm := hm.of_eq rfl rfl

theorem ExecPre.post_id {s t} (h : ExecPre s t) : ExecPost s s t t where
  rel := h.rel
  nextPC := by rw [h.nextPC, h.l3NextPC]
  frame _ _ _ := rfl
  mem _ hm := hm

theorem lsb_add_even (pc x : BitVec 64) (hpc : pc.getLsbD 0 = false) :
    (pc + x <<< 1).getLsbD 0 = false := by
  have h0 : pc[0] = false := by rwa [← BitVec.getLsbD_eq_getElem]
  rw [BitVec.getLsbD_add (by decide)]
  simp [hpc, h0, BitVec.carry, Nat.mod_one]

/-- Common shape of a branch: Sail retires, jumping iff `cond`. -/
theorem btype_sim {s t} {op : bop} {rs1 rs2 : BitVec 5}
    {l3op : BitVec 5 × BitVec 5 × BitVec 12 → riscv_state → riscv_state}
    (h : ExecPre s t) (offs : BitVec 12) (cond : Bool)
    (hsail : runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) op) t =
        runSail (if cond then (do jump_to ((← readReg Register.PC) +
          sign_extend (m := 64) (offs ++ 0#1))) else pure RETIRE_SUCCESS) t)
    (hl3 : l3op (rs1, rs2, offs) s =
      if cond then branchTo (PC s + (BitVec.signExtend 64 offs <<< 1)) s else s) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) op) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s (l3op (rs1, rs2, offs) s) t t' := by
  obtain ⟨m, hm, hC⟩ := h.misaC
  rw [hsail, hl3]
  cases cond
  · exact ⟨t, rfl, h.post_id⟩
  · simp only [if_true]
    rw [runSail_bind_of_eq (runSail_readReg h.rel.pc), sail_sign_extend_eq,
      sext_append_zero (by decide), runSail_jump_to hm hC _ (lsb_add_even _ _ h.pcEven)]
    exact ⟨_, rfl, h.post_jump _⟩

/-! ## Comparison bridges -/

theorem sail_slt (a b : BitVec 64) : zopz0zI_s a b = a.slt b := by
  simp [zopz0zI_s, BitVec.slt]

theorem sail_sge (a b : BitVec 64) : zopz0zKzJ_s a b = b.sle a := by
  simp [zopz0zKzJ_s, BitVec.sle]

theorem sail_ult (a b : BitVec 64) : zopz0zI_u a b = a.ult b := by
  simp [zopz0zI_u, BitVec.ult, Sail.BitVec.toNatInt]

theorem sail_uge (a b : BitVec 64) : zopz0zKzJ_u a b = !a.ult b := by
  simp only [zopz0zKzJ_u, BitVec.ult, Sail.BitVec.toNatInt]
  exact Bool.eq_iff_iff.mpr (by simp)

/-- Read both operands of `execute_BTYPE` through `RegRel`. -/
macro "btype_reads" h:term : tactic =>
  `(tactic| (
    simp only [execute_BTYPE, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_rX_bits (($h).rel.gpr _)),
      runSail_bind_of_eq (runSail_rX_bits (($h).rel.gpr _))]))

macro "btype_l3" h:term : tactic =>
  `(tactic| simp only [«dfn'BEQ», «dfn'BNE», «dfn'BLT», «dfn'BGE», «dfn'BLTU», «dfn'BGEU»,
    l3_in32BitMode_of_rv64 ($h).rv64, Bool.false_eq_true, if_false])

theorem beq_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BEQ) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BEQ» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs (GPR rs1 s == GPR rs2 s) (by btype_reads h) (by btype_l3 h)

theorem bne_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BNE) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BNE» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs (!(GPR rs1 s == GPR rs2 s)) (by btype_reads h; rfl) (by btype_l3 h)

theorem blt_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BLT) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BLT» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs ((GPR rs1 s).slt (GPR rs2 s))
    (by btype_reads h; rw [sail_slt]) (by btype_l3 h)

theorem bge_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BGE) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BGE» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs ((GPR rs2 s).sle (GPR rs1 s))
    (by btype_reads h; rw [sail_sge]) (by btype_l3 h)

theorem bltu_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BLTU) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BLTU» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs ((GPR rs1 s).ult (GPR rs2 s))
    (by btype_reads h; rw [sail_ult]) (by btype_l3 h)

theorem bgeu_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    ∃ t', runSail (execute_BTYPE (offs ++ 0#1) (.Regidx rs2) (.Regidx rs1) .BGEU) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'BGEU» (rs1, rs2, offs) s) t t' :=
  btype_sim h offs (!(GPR rs1 s).ult (GPR rs2 s))
    (by btype_reads h; rw [sail_uge]) (by btype_l3 h)

end FlapjackRiscvCheck
