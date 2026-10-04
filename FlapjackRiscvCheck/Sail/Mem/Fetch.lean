import FlapjackRiscvCheck.Sail.Mem.Read
import LeanRV64D.Fetch
import FlapjackRiscvCheck.Sail.Jump

/-!
# Instruction fetch

Under `SailFetchOK t pc` (machine mode, PMP off, `pc` 4-aligned in an executable
PMA region outside MMIO), Sail's `fetch` of a 32-bit instruction reads the four
bytes at `pc` and returns `F_Base`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

structure PmaExecOK (t : SailState) (a : BitVec 64) (w : Nat) : Prop where
  region : ∃ rs r, t.regs.get? Register.pma_regions = some rs ∧
    matching_pma_region rs (.Physaddr a) w = some r ∧ r.attributes.executable = true

theorem runSail_pmaCheck_fetch {t : SailState} {a : BitVec 64} {w : Nat}
    (h : PmaExecOK t a w) (halign : is_aligned_paddr (.Physaddr a) w = true) :
    runSail (pmaCheck (.Physaddr a) w (.InstructionFetch ()) .PBMT_PMA false) t =
      some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, t) := by
  obtain ⟨rs, r, hrs, hr, hp⟩ := h.region
  unfold pmaCheck
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hrs)]
  simp only [hr, override_PMA, pure_bind, ExceptT_run_lift_bind, hp, Bool.not_true,
    Bool.false_eq_true, if_false, Functions.not, bind_assoc]
  rw [runSail_bind_of_eq (runSail_mag_pma_check_aligned _ (.InstructionFetch ()) halign t _ rfl)]
  rfl

/-- `checked_mem_read` for any access whose PMA/PMP check passes without splitting. -/
theorem runSail_checked_mem_read_gen {t : SailState} {a : BitVec 64} {w : Nat}
    {acc : MemoryAccessType mem_payload}
    (hw : 0 < w) (hpmp : PmpOff t) (hmmio : MmioFree t a w)
    (hc : runSail (check_pma_with_pmp_priority acc .PBMT_PMA .Machine (.Physaddr a) w false) t =
      some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, t))
    {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t)) :
    runSail (checked_mem_read acc .PBMT_PMA .Machine (.Physaddr a) w false false false
      false) t = some (.Ok (v, ()), t) := by
  unfold checked_mem_read
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq hc]
  simp only [pure_bind, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_split_misaligned_cannot (.Physaddr a) w 0 t)]
  rw [runSail_bind_of_eq (show runSail (read_kind_of_flags false false false) t =
    some (.Read_plain, t) from rfl)]
  simp only [misaligned_order, sys_misaligned_order_decreasing, untilFuelM, untilFuelM.go,
    Bool.false_eq_true, if_false, Int.toNat_one, bind_assoc, pure_bind, ExceptT_run_lift_bind,
    bits_of_physaddr, Int.toNat_natCast, Int.toNat_zero, Nat.cast_zero, zero_mul, sail_addInt_zero]
  rw [runSail_bind_of_eq (runSail_assert_true _ t), runSail_bind_of_eq (runSail_pmpCheck_off hpmp _ _ _)]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_within_mmio_readable hmmio)]
  simp only [Bool.false_eq_true, if_false, bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq hram]
  simp only [pure_bind, ExceptT.run_pure, runSail_pure]
  simp only [Int.cast_ofNat_Int, Nat.cast_one, Int.sub_self, Int.toNat_zero, beq_self_eq_true,
    if_true, Int.mul_one, Int.zero_add, Int.one_mul]
  simp
  rw [sail_read_assemble w hw v]

structure SailFetchOK (t : SailState) (pc : BitVec 64) : Prop where
  mem : SailMemInv t
  pmp : PmpOff t
  pma : PmaExecOK t pc 4
  mmio : MmioFree t pc 4
  aligned : pc.toNat % 4 = 0

theorem runSail_fetch_bytes {t : SailState} {pc : BitVec 64} (h : SailFetchOK t pc)
    {v : BitVec (8 * 4)}
    (hram : runSail (read_ram .Read_plain (.Physaddr pc) 4 false) t = some ((v, ()), t)) :
    runSail (fetch_bytes pc pc 4) t = some (.FetchBytes_Success v, t) := by
  have halign : is_aligned_paddr (.Physaddr pc) 4 = true := by
    have := h.aligned
    simp only [is_aligned_paddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, beq_iff_eq]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  have hc : runSail (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr pc) 4 false) t = some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, t) := by
    unfold check_pma_with_pmp_priority
    rw [runSail_bind_of_eq (runSail_pmaCheck_fetch h.pma halign)]
    rfl
  unfold fetch_bytes
  rw [SailME.run, runSail_SailME_run]
  simp only [ext_fetch_check_pc, bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_translateAddr h.mem pc _ rfl)]
  simp only [pure_bind, ExceptT_run_lift_bind]
  unfold mem_read
  simp only [bind_assoc]
  rw [runSail_readReg_mstatus_priv h.mem]
  unfold mem_read_priv mem_read_priv_meta
  simp only [bind_assoc, pure_bind]
  rw [runSail_bind_of_eq (runSail_checked_mem_read_gen (by decide) h.pmp h.mmio hc hram)]
  rfl

theorem runSail_currentlyEnabled_Ziccif (t : SailState) :
    runSail (currentlyEnabled .Ext_Ziccif) t = some (true, t) := by
  rw [currentlyEnabled]; simp [hartSupports]

theorem runSail_fetch {t : SailState} {pc : BitVec 64} (h : SailFetchOK t pc)
    (hpc : t.regs.get? Register.PC = some pc) {m : BitVec 64}
    (hm : t.regs.get? Register.misa = some m) (hC : _get_Misa_C m = 1)
    {v : BitVec (8 * 4)}
    (hram : runSail (read_ram .Read_plain (.Physaddr pc) 4 false) t = some ((v, ()), t))
    (hrvc : isRVC (Sail.BitVec.extractLsb v 15 0) = false) :
    runSail (fetch ()) t = some (.F_Base v, t) := by
  have ha := h.aligned
  have hb0 : (Sail.BitVec.access pc 0 != 0#1) = false := by
    have : pc.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, this]
  have hb1 : (Sail.BitVec.access pc 1 != 0#1) = false := by
    have : pc.getLsbD 1 = false := by
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
    simp [Sail.BitVec.access, ← BitVec.getLsbD_eq_getElem, this]
  have hal : is_aligned_vaddr (.Virtaddr pc) 4 = true := by
    simp only [is_aligned_vaddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, beq_iff_eq]
    rw [Int.tmod_eq_emod_of_nonneg (by omega)]
    omega
  unfold fetch
  rw [SailME.run, runSail_SailME_run]
  simp only [get_config_rvfi, Bool.false_eq_true, if_false, ext_fetch_check_pc, bind_assoc,
    ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hpc), runSail_bind_of_eq (runSail_readReg hpc),
    runSail_bind_of_eq (runSail_readReg hpc), runSail_bind_of_eq (runSail_readReg hpc),
    runSail_bind_of_eq (runSail_currentlyEnabled_Zca hm hC)]
  simp only [hb0, hb1, Bool.false_or, Bool.false_and, Bool.false_eq_true, if_false,
    ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hpc),
    runSail_bind_of_eq (runSail_currentlyEnabled_Ziccif t)]
  simp only [hal, Bool.and_true, if_true, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hpc), runSail_bind_of_eq (runSail_readReg hpc),
    runSail_bind_of_eq (runSail_fetch_bytes h hram)]
  simp [hrvc]

end FlapjackRiscvCheck
