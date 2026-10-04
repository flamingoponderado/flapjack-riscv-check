import FlapjackRiscvCheck.Exec.Contract
import FlapjackRiscvCheck.Exec.Imm
import FlapjackRiscvCheck.Sail.Mem.Read
import FlapjackRiscvCheck.L3.Load

/-!
# Loads: LD, LWU, LHU, LBU

A load whose bytes lie in `D` and which Sail performs as a plain
RAM access (`SailAccessOK`) reads the same value on both sides.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

theorem toNat_add_small {A : BitVec 64} {w i : Nat} (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8)
    (hal : A.toNat % w = 0) (hi : i < w) : (A + BitVec.ofNat 64 i).toNat = A.toNat + i := by
  have := A.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rcases hw with rfl | rfl | rfl | rfl <;> omega

theorem sail_load {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    {rs1 rd : BitVec 5} {imm : BitVec 12} {w : Nat} (u : Bool)
    (hacc : SailAccessOK t (GPR rs1 s + BitVec.signExtend 64 imm) w false)
    (hD : ∀ i < w, D (GPR rs1 s + BitVec.signExtend 64 imm + BitVec.ofNat 64 i)) :
    ∃ v : BitVec (8 * w),
      v.toNat = leNat (fun i => s.MEM8 (GPR rs1 s + BitVec.signExtend 64 imm + BitVec.ofNat 64 i)) w ∧
      runSail (execute_LOAD imm (.Regidx rs1) (.Regidx rd) u w) t =
        some (RETIRE_SUCCESS, sailSetGpr t rd (extend_value u v)) := by
  let A := GPR rs1 s + BitVec.signExtend 64 imm
  obtain ⟨v, hv, hr⟩ := runSail_readBytes w A.toNat (fun i => s.MEM8 (A + BitVec.ofNat 64 i)) t
    (fun i hi => by
      rw [← toNat_add_small hacc.width hacc.aligned hi]
      exact hm.agree _ (hD i hi))
  refine ⟨v, hv, ?_⟩
  have hw8 : decide (w ≤ Functions.xlen_bytes) = true := by
    rcases hacc.width with rfl | rfl | rfl | rfl <;> rfl
  unfold execute_LOAD
  rw [hw8, runSail_bind_of_eq (runSail_assert_true _ t), sail_sign_extend_eq,
    runSail_bind_of_eq (runSail_vmem_read (h.rel.gpr rs1) _ hacc (runSail_read_ram hr))]
  simp only []
  rw [runSail_bind_of_eq (runSail_wX_bits _ _ _)]
  rfl

theorem extend_value_toNat_unsigned {n : Nat} (v : BitVec n) (hn : n ≤ 64) :
    (extend_value true v).toNat = v.toNat := by
  simp [extend_value, zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
  exact Nat.lt_of_lt_of_le v.isLt (Nat.pow_le_pow_right (by decide) hn)

theorem extend_value_toNat_64 (v : BitVec (8 * 8)) : (extend_value false v).toNat = v.toNat := by
  simp [extend_value, sign_extend, Sail.BitVec.signExtend]

/-- Assemble a load simulation from the Sail and L3 characterisations. -/
theorem load_post {s t} (h : ExecPre s t) {rd : BitVec 5} {l3s : L3State} {v : BitVec 64}
    {sv : BitVec 64} (hl3 : l3s = «write'GPR» (v, rd) s) (heq : sv.toNat = v.toNat) :
    ExecPost s l3s t (sailSetGpr t rd sv) := by
  rw [BitVec.eq_of_toNat_eq heq, hl3]
  exact ExecPost.of_write h rd v

theorem ld_sim {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    (rd rs1 : BitVec 5) (imm : BitVec 12) (hacc : SailAccessOK t (l3EA s rs1 imm) 8 false)
    (hD : ∀ i < 8, D (l3EA s rs1 imm + BitVec.ofNat 64 i)) :
    ∃ t', runSail (execute_LOAD imm (.Regidx rs1) (.Regidx rd) false 8) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'LD» (rd, rs1, imm) s) t t' := by
  obtain ⟨sv, hsv, hr⟩ := sail_load (rd := rd) h hm false hacc hD
  obtain ⟨v, hl3, hv⟩ := l3_ld s rd rs1 imm h.rv64 h.bareVM hacc.aligned
  exact ⟨_, hr, load_post h hl3 (by rw [extend_value_toNat_64, hsv, hv])⟩

theorem lwu_sim {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    (rd rs1 : BitVec 5) (imm : BitVec 12) (hacc : SailAccessOK t (l3EA s rs1 imm) 4 false)
    (hD : ∀ i < 4, D (l3EA s rs1 imm + BitVec.ofNat 64 i)) :
    ∃ t', runSail (execute_LOAD imm (.Regidx rs1) (.Regidx rd) true 4) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'LWU» (rd, rs1, imm) s) t t' := by
  obtain ⟨sv, hsv, hr⟩ := sail_load (rd := rd) h hm true hacc hD
  obtain ⟨v, hl3, hv⟩ := l3_lwu s rd rs1 imm h.rv64 h.bareVM hacc.aligned
  exact ⟨_, hr, load_post h hl3 (by rw [extend_value_toNat_unsigned _ (by decide), hsv, hv])⟩

theorem lhu_sim {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    (rd rs1 : BitVec 5) (imm : BitVec 12) (hacc : SailAccessOK t (l3EA s rs1 imm) 2 false)
    (hD : ∀ i < 2, D (l3EA s rs1 imm + BitVec.ofNat 64 i)) :
    ∃ t', runSail (execute_LOAD imm (.Regidx rs1) (.Regidx rd) true 2) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'LHU» (rd, rs1, imm) s) t t' := by
  obtain ⟨sv, hsv, hr⟩ := sail_load (rd := rd) h hm true hacc hD
  obtain ⟨v, hl3, hv⟩ := l3_lhu s rd rs1 imm h.bareVM hacc.aligned
  exact ⟨_, hr, load_post h hl3 (by rw [extend_value_toNat_unsigned _ (by decide), hsv, hv])⟩

theorem lbu_sim {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    (rd rs1 : BitVec 5) (imm : BitVec 12) (hacc : SailAccessOK t (l3EA s rs1 imm) 1 false)
    (hD : ∀ i < 1, D (l3EA s rs1 imm + BitVec.ofNat 64 i)) :
    ∃ t', runSail (execute_LOAD imm (.Regidx rs1) (.Regidx rd) true 1) t =
      some (RETIRE_SUCCESS, t') ∧ ExecPost s («dfn'LBU» (rd, rs1, imm) s) t t' := by
  obtain ⟨sv, hsv, hr⟩ := sail_load (rd := rd) h hm true hacc hD
  obtain ⟨v, hl3, hv⟩ := l3_lbu s rd rs1 imm h.bareVM
  exact ⟨_, hr, load_post h hl3 (by rw [extend_value_toNat_unsigned _ (by decide), hsv, hv])⟩

end FlapjackRiscvCheck
