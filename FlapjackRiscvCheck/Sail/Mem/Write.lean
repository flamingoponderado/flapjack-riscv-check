import FlapjackRiscvCheck.Sail.Mem.Read

/-!
# Data stores through `vmem_write`

Under `SailAccessOK t a w true`, an aligned machine-mode store of `w` bytes
at `a` is a plain `writeBytes` into Sail's memory map.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

/-- Sail's state after storing `data` at `a`. -/
def sailStore (t : SailState) (a : BitVec 64) {w : Nat} (data : BitVec (8 * w)) : SailState :=
  { t with mem := insertAll t.mem (writeList a.toNat data) }

theorem runSail_write_ram {t : SailState} {a : BitVec 64} {w : Nat} (data : BitVec (8 * w)) :
    runSail (write_ram .Write_plain (.Physaddr a) w data ()) t = some (true, sailStore t a data) := by
  unfold write_ram
  simp only [pure_bind, bind_assoc]
  unfold LeanRV64D.ConcurrencyInterfaceV1.sail_mem_write Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_write
  simp only [bind_assoc]
  rw [runSail_bind_of_eq (runSail_writeBytes _ _ t)]
  rfl

theorem sail_extract_full {w : Nat} (hw : 0 < w) (data : BitVec (8 * w)) :
    BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb data (8 * ((0 : Nat) + 1 : Int) * (w : Int) - 1).toNat
      (8 * ((0 : Nat) : Int) * (w : Int)).toNat) = data := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (8 * ((0 : Nat) + 1 : Int) * (w : Int) - 1).toNat = 8 * w - 1 := by omega
  have h3 : (8 * ((0 : Nat) : Int) * (w : Int)).toNat = 0 := by simp
  simp only [Sail.BitVec.extractLsb, h2, h3, BitVec.toNat_setWidth, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero]
  have h4 : 8 * w - 1 - 0 + 1 = 8 * w := by omega
  rw [h4, Nat.mod_eq_of_lt data.isLt, Nat.mod_eq_of_lt data.isLt]

theorem runSail_checked_mem_write {t : SailState} {a : BitVec 64} {w : Nat}
    (hw : 0 < w) (hpma : PmaOK t a w true) (hpmp : PmpOff t) (hmmio : MmioFree t a w)
    (halign : is_aligned_paddr (.Physaddr a) w = true) (data : BitVec (8 * w)) :
    runSail (checked_mem_write (.Physaddr a) w data (.Store .Data) .PBMT_PMA .Machine () false false
      false) t = some (.Ok true, sailStore t a data) := by
  unfold checked_mem_write
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  have hc := runSail_check_pma_with_pmp_priority (write := true) hpma halign
  simp only [dataAccess] at hc
  rw [runSail_bind_of_eq hc]
  simp only [pure_bind, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_split_misaligned_cannot (.Physaddr a) w 0 t)]
  rw [runSail_bind_of_eq (show runSail (write_kind_of_flags false false false) t =
    some (.Write_plain, t) from rfl)]
  simp only [misaligned_order, sys_misaligned_order_decreasing, untilFuelM, untilFuelM.go,
    Bool.false_eq_true, if_false, Int.toNat_one, bind_assoc, pure_bind, ExceptT_run_lift_bind,
    bits_of_physaddr, Int.toNat_natCast, Int.toNat_zero, Nat.cast_zero, zero_mul, sail_addInt_zero]
  rw [runSail_bind_of_eq (runSail_assert_true _ t), runSail_bind_of_eq (runSail_pmpCheck_off hpmp _ _ _)]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_within_mmio_writable hmmio)]
  simp only [Bool.false_eq_true, if_false, bind_assoc, ExceptT_run_lift_bind]
  rw [sail_extract_full hw data, runSail_bind_of_eq (runSail_write_ram data)]
  simp

theorem runSail_mem_write_value {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w true) (data : BitVec (8 * w)) :
    runSail (mem_write_value (.Physaddr a) w data (.Store .Data) .PBMT_PMA false false false) t =
      some (.Ok true, sailStore t a data) := by
  unfold mem_write_value mem_write_value_meta
  rw [runSail_readReg_mstatus_priv h.mem]
  unfold mem_write_value_priv_meta
  rw [runSail_bind_of_eq (runSail_checked_mem_write h.pos h.pma h.pmp h.mmio h.paligned data)]
  rfl

theorem sail_extract_full' {w : Nat} (hw : 0 < w) (data : BitVec (8 * w)) :
    BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb data (8 * (w : Int) - 1).toNat 0) = data := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (8 * (w : Int) - 1).toNat = 8 * w - 1 := by omega
  simp only [Sail.BitVec.extractLsb, h2, BitVec.toNat_setWidth, BitVec.extractLsb_toNat,
    Nat.shiftRight_zero]
  have h4 : 8 * w - 1 - 0 + 1 = 8 * w := by omega
  rw [h4, Nat.mod_eq_of_lt data.isLt, Nat.mod_eq_of_lt data.isLt]

/-- `mem_write_value` as `vmem_write_addr` calls it, with the (always equal) split-width
conditional left symbolic. -/
theorem runSail_mem_write_value_ite {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w true) (data : BitVec (8 * w)) (c : Bool) :
    runSail (mem_write_value (.Physaddr a) (if c = true then (w : Int) else (w : Int)).toNat
      (BitVec.setWidth (8 * (if c = true then (w : Int) else (w : Int)).toNat)
        (Sail.BitVec.extractLsb data ((8 * if c = true then (w : Int) else (w : Int)) - 1).toNat 0))
      (.Store .Data) .PBMT_PMA false false false) t = some (.Ok true, sailStore t a data) := by
  have e := runSail_mem_write_value h
    (BitVec.setWidth (8 * w) (Sail.BitVec.extractLsb data (8 * (w : Int) - 1).toNat 0))
  have hd := sail_extract_full' h.pos data
  cases c <;> exact e.trans (by rw [hd])

theorem runSail_mem_write_ea {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w true) :
    runSail (mem_write_ea (.Physaddr a) w (.Store .Data) .PBMT_PMA false false false) t =
      some (.Ok (), t) := by
  unfold mem_write_ea
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_readReg_mstatus_priv h.mem]
  have hc := runSail_check_pma_with_pmp_priority (write := true) h.pma h.paligned
  simp only [dataAccess] at hc
  rw [runSail_bind_of_eq hc]
  simp only [pure_bind, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_split_misaligned_cannot (.Physaddr a) w 0 t)]
  rw [runSail_bind_of_eq (show runSail (write_kind_of_flags false false false) t =
    some (.Write_plain, t) from rfl)]
  simp only [misaligned_order, sys_misaligned_order_decreasing, untilFuelM, untilFuelM.go,
    Bool.false_eq_true, if_false, Int.toNat_one, bind_assoc, pure_bind, ExceptT_run_lift_bind,
    bits_of_physaddr, Int.toNat_natCast, Int.toNat_zero, Nat.cast_zero, zero_mul, sail_addInt_zero]
  rw [runSail_bind_of_eq (runSail_assert_true _ t), runSail_bind_of_eq (runSail_pmpCheck_off h.pmp _ _ _)]
  simp

theorem runSail_vmem_write_addr {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w true) (data : BitVec (8 * w)) :
    runSail (vmem_write_addr (.Virtaddr a) w data (.Store .Data) false false false) t =
      some (.Ok true, sailStore t a data) := by
  unfold vmem_write_addr
  rw [SailME.run, runSail_SailME_run]
  simp only [h.valigned, Functions.not, Bool.not_true, Bool.false_eq_true, if_false, pure_bind,
    bind_assoc, ExceptT_run_lift_bind, bits_of_virtaddr]
  rw [runSail_bind_of_eq (runSail_split_on_page_boundary h.width h.aligned t),
    runSail_readReg_mstatus_priv h.mem, runSail_bind_of_eq (runSail_translationMode_machine t)]
  have hb : (SATPMode.Bare != SATPMode.Bare) = false := rfl
  simp only [hb, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false, ite_self,
    pure_bind, bind_assoc, ExceptT_run_lift_bind, Int.toNat_natCast]
  rw [runSail_bind_of_eq (runSail_translateAddr h.mem a _ rfl)]
  simp only [ExceptT_run_lift_bind, bind_assoc]
  rw [show (false == is_store_conditional (MemoryAccessType.Store mem_payload.Data)) = true from rfl,
    runSail_bind_of_eq (runSail_assert_true _ t), runSail_bind_of_eq (runSail_mem_write_ea h)]
  simp only [pure_bind, ExceptT_run_lift_bind]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_mem_write_value_ite h data _)]
  rfl

theorem runSail_vmem_write {t : SailState} {n : BitVec 5} {x : BitVec 64}
    (hx : sailGpr t n = some x) (offset : BitVec 64) {w : Nat}
    (h : SailAccessOK t (x + offset) w true) (data : BitVec (8 * w)) :
    runSail (vmem_write (.Regidx n) offset w data (.Store .Data) false false false) t =
      some (.Ok true, sailStore t (x + offset) data) := by
  unfold vmem_write
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_get_transformed_data_addr h.mem hx offset _ w)]
  simp only [pure_bind, ExceptT_run_lift]
  rw [runSail_map_ok (runSail_vmem_write_addr h data)]

end FlapjackRiscvCheck
