import FlapjackRiscvCheck.Exec.Load
import FlapjackRiscvCheck.Sail.Mem.Write
import FlapjackRiscvCheck.L3.Store

/-!
# Stores: SD, SW, SH, SB

Sail `execute_STORE imm rs2 rs1 w` against L3 `dfn'S<w> (rs1, rs2, imm)`. Both
replace the bytes at `A, …, A + w - 1` (with `A = x[rs1] + imm`) with the low
`w` bytes of `x[rs2]`. `MemRel` is preserved on every domain.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

theorem sail_store_run {s t} (h : ExecPre s t) {rs1 rs2 : BitVec 5} {imm : BitVec 12} {w : Nat}
    (hacc : SailAccessOK t (l3EA s rs1 imm) w true) :
    ∃ data : BitVec (8 * w), (∀ j < w, data.extractLsb' (8 * j) 8 = (GPR rs2 s).extractLsb' (8 * j) 8) ∧
      runSail (execute_STORE imm (.Regidx rs2) (.Regidx rs1) w) t =
        some (RETIRE_SUCCESS, sailStore t (l3EA s rs1 imm) data) := by
  have hw8 : decide (w ≤ Functions.xlen_bytes) = true := by
    rcases hacc.width with rfl | rfl | rfl | rfl <;> rfl
  refine ⟨BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb (GPR rs2 s) (((w : Int) * 8) - 1).toNat 0),
    ?hb, ?hrun⟩
  case hrun =>
    unfold execute_STORE
    rw [hw8, runSail_bind_of_eq (runSail_assert_true _ t),
      runSail_bind_of_eq (runSail_rX_bits (h.rel.gpr rs2)), sail_sign_extend_eq]
    simp only [pure_bind]
    rw [runSail_bind_of_eq (runSail_vmem_write (h.rel.gpr rs1) _ hacc _)]
    rfl
  case hb =>
    intro j hj
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hw := hacc.pos
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, Sail.BitVec.extractLsb,
      BitVec.getLsbD_extractLsb, hi, decide_true, Bool.true_and]
    have h1 : 8 * j + i < 8 * w := by omega
    have h2 : 8 * j + i ≤ ((w : Int) * 8 - 1).toNat - 0 := by omega
    simp [h1, h2]
    intro _
    omega

theorem store_post {s t} (h : ExecPre s t) {rs1 rs2 : BitVec 5} {imm : BitVec 12} {w : Nat}
    (hacc : SailAccessOK t (l3EA s rs1 imm) w true) (data : BitVec (8 * w))
    (hdata : ∀ j < w, data.extractLsb' (8 * j) 8 = (GPR rs2 s).extractLsb' (8 * j) 8) :
    ExecPost s (l3Store s rs1 rs2 imm w) t (sailStore t (l3EA s rs1 imm) data) where
  rel := ⟨fun n => h.rel.gpr n, h.rel.pc⟩
  nextPC := by rw [show l3NextPC (l3Store s rs1 rs2 imm w) = l3NextPC s from rfl, h.l3NextPC]; exact h.nextPC
  frame _ _ _ := rfl
  mem D hm := by
    refine ⟨fun a ha => ?_⟩
    simp only [sailStore, writeBytes_get?, l3Store, l3StoreMem]
    split
    · rename_i hr
      rw [hdata _ (by omega)]
    · exact hm.agree a ha
  l3frame := ⟨rfl, rfl, rfl, rfl, rfl⟩
  npc := ⟨_, (show l3NextPC (l3Store s rs1 rs2 imm w) = l3NextPC s from rfl).trans h.l3NextPC⟩

theorem sd_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (hacc : SailAccessOK t (l3EA s rs1 imm) 8 true) :
    ∃ t', runSail (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 8) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'SD» (rs1, rs2, imm) s) t t' := by
  obtain ⟨data, hd, hr⟩ := sail_store_run (rs2 := rs2) h hacc
  rw [l3_sd s rs1 rs2 imm h.rv64 h.bareVM hacc.aligned]
  exact ⟨_, hr, store_post h hacc data hd⟩

theorem sw_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (hacc : SailAccessOK t (l3EA s rs1 imm) 4 true) :
    ∃ t', runSail (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 4) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'SW» (rs1, rs2, imm) s) t t' := by
  obtain ⟨data, hd, hr⟩ := sail_store_run (rs2 := rs2) h hacc
  rw [l3_sw s rs1 rs2 imm h.bareVM hacc.aligned]
  exact ⟨_, hr, store_post h hacc data hd⟩

theorem sh_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (hacc : SailAccessOK t (l3EA s rs1 imm) 2 true) :
    ∃ t', runSail (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 2) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'SH» (rs1, rs2, imm) s) t t' := by
  obtain ⟨data, hd, hr⟩ := sail_store_run (rs2 := rs2) h hacc
  rw [l3_sh s rs1 rs2 imm h.bareVM hacc.aligned]
  exact ⟨_, hr, store_post h hacc data hd⟩

theorem sb_sim {s t} (h : ExecPre s t) (rs1 rs2 : BitVec 5) (imm : BitVec 12)
    (hacc : SailAccessOK t (l3EA s rs1 imm) 1 true) :
    ∃ t', runSail (execute_STORE imm (.Regidx rs2) (.Regidx rs1) 1) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'SB» (rs1, rs2, imm) s) t t' := by
  obtain ⟨data, hd, hr⟩ := sail_store_run (rs2 := rs2) h hacc
  rw [l3_sb s rs1 rs2 imm h.bareVM]
  exact ⟨_, hr, store_post h hacc data hd⟩

end FlapjackRiscvCheck
