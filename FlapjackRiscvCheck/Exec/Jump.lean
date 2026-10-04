import FlapjackRiscvCheck.Exec.Branch

/-!
# JAL and JALR

L3 `dfn'JAL (rd, imm)` against Sail `execute_JAL (imm ++ 0) rd`, and L3
`dfn'JALR (rd, rs1, imm)` against Sail `execute_JALR imm rs1 rd`.

Sail's JALR first runs `update_elp_state` (Zicfilp landing pads). With
`mseccfg.MLPE = 0` in machine mode this does nothing, which matches L3, where
landing pads do not exist.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

theorem ExecPre.post_jump_link {s t} (h : ExecPre s t) (a v : BitVec 64) (rd : BitVec 5) :
    ExecPost s (branchTo a («write'GPR» (v, rd) s)) t
      (sailSetGpr { t with regs := t.regs.insert Register.nextPC a } rd v) := by
  have hj := h.post_jump a
  refine ⟨⟨fun n => ?_, ?_⟩, ?_, ?_, ?_, (L3Frame.ofWrite s rd v).trans (L3Frame.ofBranchTo _ a)⟩
  · rw [sailGpr_sailSetGpr, l3_GPR_branchTo, l3_GPR_write'GPR]
    split
    · rfl
    · rw [← l3_GPR_branchTo a s]; exact hj.rel.gpr n
  · rw [sailSetGpr_get?_of_not_gpr _ _ _ rfl, l3_PC_branchTo, l3_PC_write'GPR]
    exact hj.rel.pc
  · rw [sailSetGpr_get?_of_not_gpr _ _ _ rfl, l3NextPC_branchTo]
    simp [Std.ExtDHashMap.get?_insert]
  · intro r hr hn
    rw [sailSetGpr_get?_of_not_gpr _ _ _ hr]
    exact hj.frame r hr hn
  · intro D hm
    exact hm.of_eq (by simp) (by rw [sailSetGpr_mem])

theorem runSail_get_next_pc {s t} (h : ExecPre s t) :
    runSail (get_next_pc ()) t = some (PC s + 4, t) :=
  runSail_readReg h.nextPC

theorem jal_sim {s t} (h : ExecPre s t) (rd : BitVec 5) (imm : BitVec 20) :
    ∃ t', runSail (execute_JAL (imm ++ 0#1) (.Regidx rd)) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'JAL» (rd, imm) s) t t' := by
  obtain ⟨m, hm, hC⟩ := h.misaC
  have heven := lsb_add_even (PC s) (BitVec.signExtend 64 imm) h.pcEven
  refine ⟨sailSetGpr { t with regs := t.regs.insert Register.nextPC (PC s +
      BitVec.signExtend 64 imm <<< 1) } rd (PC s + 4), ?_, ?_⟩
  rotate_left
  · have := h.post_jump_link (PC s + BitVec.signExtend 64 imm <<< 1) (PC s + 4) rd
    simp only [«dfn'JAL», heven, Bool.false_eq_true, if_false, h.skip]
    exact this
  · simp only [execute_JAL, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_get_next_pc h),
      runSail_bind_of_eq (runSail_readReg h.rel.pc), sail_sign_extend_eq,
      sext_append_zero (by decide),
      runSail_bind_of_eq (runSail_jump_to hm hC _ heven)]
    simp only [RETIRE_SUCCESS]
    rw [runSail_bind_of_eq (runSail_wX_bits _ _ _)]
    rfl

theorem runSail_update_elp_state {s t} (h : ExecPre s t) (rs1 : regidx) :
    runSail (update_elp_state rs1) t = some ((), t) := by
  obtain ⟨c, hc, hL⟩ := h.noLandingPads
  have hz : runSail (currentlyEnabled .Ext_Zicfilp) t = some (false, t) := by
    rw [currentlyEnabled]
    rw [runSail_bind_of_eq (show runSail (currentlyEnabled .Ext_Zicsr) t = some (true, t) by
      rw [currentlyEnabled]; simp [hartSupports])]
    simp only [hartSupports, Bool.true_and]
    rw [runSail_bind_of_eq (runSail_readReg h.machine)]
    simp [get_xLPE, runSail, EStateM.run, EStateM.bind, EStateM.pure, Sail.ConcurrencyInterfaceV1.PreSail.readReg, get,
      getThe, MonadStateOf.get, EStateM.get, hc, hL, bind, pure, bool_bit_backwards]
  unfold update_elp_state
  rw [runSail_bind_of_eq hz]
  rfl

theorem sail_update_lsb (x : BitVec 64) :
    Sail.BitVec.update x 0 0#1 = x &&& BitVec.signExtend 64 (BitVec.ofNat 2 2) := by
  have h1 : ~~~(BitVec.zeroExtend 64 (BitVec.allOnes 1) <<< 0) =
      BitVec.signExtend 64 (BitVec.ofNat 2 2) := by decide
  simp only [Sail.BitVec.update, Sail.BitVec.updateSubrange', h1, BitVec.and_comm]
  simp

theorem jalr_sim {s t} (h : ExecPre s t) (rd rs1 : BitVec 5) (imm : BitVec 12) :
    ∃ t', runSail (execute_JALR imm (.Regidx rs1) (.Regidx rd)) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'JALR» (rd, rs1, imm) s) t t' := by
  obtain ⟨m, hm, hC⟩ := h.misaC
  let a := (GPR rs1 s + BitVec.signExtend 64 imm) &&& BitVec.signExtend 64 (BitVec.ofNat 2 2)
  have heven : a.getLsbD 0 = false := by simp [a]
  refine ⟨sailSetGpr { t with regs := t.regs.insert Register.nextPC a } rd (PC s + 4), ?_, ?_⟩
  · simp only [execute_JALR, bind_assoc, pure_bind]
    rw [runSail_bind_of_eq (runSail_update_elp_state h _),
      runSail_bind_of_eq (runSail_get_next_pc h),
      runSail_bind_of_eq (runSail_rX_bits (h.rel.gpr _)), sail_sign_extend_eq, sail_update_lsb,
      runSail_bind_of_eq (runSail_jump_to hm hC _ heven)]
    simp only [RETIRE_SUCCESS]
    rw [runSail_bind_of_eq (runSail_wX_bits _ _ _)]
    rfl
  · have := h.post_jump_link a (PC s + 4) rd
    simp only [«dfn'JALR», h.skip]
    simp only [a] at heven this
    simp only [heven, Bool.false_eq_true, if_false]
    exact this

end FlapjackRiscvCheck
