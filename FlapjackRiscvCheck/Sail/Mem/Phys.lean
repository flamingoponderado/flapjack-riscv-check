import FlapjackRiscvCheck.Sail.Mem.Pma

/-!
# Aligned physical RAM accesses

`checked_mem_read` / `checked_mem_write` for an aligned access that the PMA
permits, PMP lets through, and that misses every MMIO window, reduce to a
single `read_ram` / `write_ram`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

/-- The access misses CLINT, the signature region and HTIF. -/
structure MmioFree (t : SailState) (a : BitVec 64) (w : Nat) : Prop where
  clint : ¬ (0x2000000 ≤ a.toNat ∧ a.toNat + w ≤ 0x2000000 + 0xC0000)
  sig : ¬ (0xC000000 ≤ a.toNat ∧ a.toNat + w ≤ 0xC000000 + 0x20)
  htif : ∃ hb, t.regs.get? Register.htif_tohost_base = some hb ∧ ∀ base, hb = some base →
    (zopz0zI_u a (Sail.BitVec.addInt base (htif_tohost_size : Int)) &&
      zopz0zK_u (Sail.BitVec.addInt a (w : Int)) base)
      = false

theorem runSail_within_htif_writable {t : SailState} {a : BitVec 64} {w : Nat}
    (h : MmioFree t a w) :
    runSail (within_htif_writable (.Physaddr a) w) t = some (false, t) := by
  obtain ⟨hb, hhb, hfree⟩ := h.htif
  unfold within_htif_writable
  rw [runSail_bind_of_eq (runSail_readReg hhb)]
  cases hb with
  | none => rfl
  | some base => simp only [hfree base rfl]; rfl

theorem plat_clint_base_toNat : plat_clint_base.toNat = 0x2000000 := by decide
theorem plat_clint_size_toNat : plat_clint_size.toNat = 0xC0000 := by decide
theorem plat_sig_base_toNat : plat_sig_base.toNat = 0xC000000 := by decide
theorem plat_sig_size_toNat : plat_sig_size.toNat = 0x20 := by decide

theorem runSail_within_clint {t : SailState} {a : BitVec 64} {w : Nat} (h : MmioFree t a w) :
    runSail (within_clint (.Physaddr a) w) t = some (false, t) := by
  have := h.clint
  unfold within_clint
  simp only [plat_have_clint, Sail.BitVec.toNatInt, plat_clint_base_toNat, plat_clint_size_toNat,
    Functions.not, Bool.not_true, Bool.false_eq_true, if_false]
  have key : ((Int.ofNat 33554432 ≤b Int.ofNat a.toNat) &&
      (Int.ofNat a.toNat + (w : Int) ≤b Int.ofNat 33554432 + Int.ofNat 786432)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.ofNat_eq_natCast]
    omega
  rw [key]; rfl

theorem runSail_within_sig {t : SailState} {a : BitVec 64} {w : Nat} (h : MmioFree t a w) :
    runSail (within_sig (.Physaddr a) w) t = some (false, t) := by
  have := h.sig
  unfold within_sig
  simp only [plat_have_sig, Sail.BitVec.toNatInt, plat_sig_base_toNat, plat_sig_size_toNat,
    Functions.not, Bool.not_true, Bool.false_eq_true, if_false]
  have key : ((Int.ofNat 201326592 ≤b Int.ofNat a.toNat) &&
      (Int.ofNat a.toNat + (w : Int) ≤b Int.ofNat 201326592 + Int.ofNat 32)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Int.ofNat_eq_natCast]
    omega
  rw [key]; rfl

theorem runSail_within_mmio_readable {t : SailState} {a : BitVec 64} {w : Nat}
    (h : MmioFree t a w) :
    runSail (within_mmio_readable (.Physaddr a) w) t = some (false, t) := by
  unfold within_mmio_readable within_htif_readable
  simp only [get_config_rvfi, Bool.false_eq_true, if_false]
  rw [runSail_bind_of_eq (runSail_within_clint h), runSail_bind_of_eq (runSail_within_sig h),
    runSail_bind_of_eq (runSail_within_htif_writable h)]
  rfl

theorem runSail_within_mmio_writable {t : SailState} {a : BitVec 64} {w : Nat}
    (h : MmioFree t a w) :
    runSail (within_mmio_writable (.Physaddr a) w) t = some (false, t) := by
  unfold within_mmio_writable
  simp only [get_config_rvfi, Bool.false_eq_true, if_false]
  rw [runSail_bind_of_eq (runSail_within_clint h), runSail_bind_of_eq (runSail_within_sig h),
    runSail_bind_of_eq (runSail_within_htif_writable h)]
  rfl

theorem runSail_check_pma_with_pmp_priority {t : SailState} {a : BitVec 64} {w : Nat}
    {write : Bool} (hpma : PmaOK t a w write) (halign : is_aligned_paddr (.Physaddr a) w = true) :
    runSail (check_pma_with_pmp_priority (dataAccess write) .PBMT_PMA .Machine (.Physaddr a) w false)
      t = some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, t) := by
  unfold check_pma_with_pmp_priority
  rw [runSail_bind_of_eq (runSail_pmaCheck hpma halign)]
  rfl

theorem runSail_split_misaligned_cannot (a : physaddr) (w e : Nat) (t : SailState) :
    runSail (split_misaligned a w e .CannotSplit) t = some ((1, w), t) := by
  unfold split_misaligned
  simp
  rfl

@[simp] theorem sail_addInt_zero {n : Nat} (x : BitVec n) : Sail.BitVec.addInt x 0 = x := by
  simp [Sail.BitVec.addInt]

/-- A single-piece read writes the whole result word. -/
theorem sail_read_assemble (w : Nat) (hw : 0 < w) (v : BitVec (8 * w)) :
    BitVec.setWidth (8 * w)
      (BitVec.setWidth (8 * (w : Int)).toNat
        (Sail.BitVec.updateSubrange (BitVec.setWidth (8 * w) (zeros (n := 8 * w)))
          (8 * (w : Int) - 1).toNat (0 * (w : Int)).toNat
          (BitVec.setWidth ((8 * (w : Int) - 1).toNat - (0 * (w : Int)).toNat + 1) v))) = v := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (8 * (w : Int) - 1).toNat = 8 * w - 1 := by omega
  have h3 : (8 * (w : Int)).toNat = 8 * w := by omega
  have h4 : 8 * w - 1 + 1 = 8 * w := by omega
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros, BitVec.toNat_setWidth, h2,
    h3, h4, Nat.mod_eq_of_lt v.isLt]

theorem runSail_checked_mem_read {t : SailState} {a : BitVec 64} {w : Nat}
    (hw : 0 < w) (hpma : PmaOK t a w false) (hpmp : PmpOff t) (hmmio : MmioFree t a w)
    (halign : is_aligned_paddr (.Physaddr a) w = true) {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t)) :
    runSail (checked_mem_read (.Load .Data) .PBMT_PMA .Machine (.Physaddr a) w false false false
      false) t = some (.Ok (v, ()), t) := by
  unfold checked_mem_read
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  have hc := runSail_check_pma_with_pmp_priority (write := false) hpma halign
  simp only [dataAccess] at hc
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

end FlapjackRiscvCheck
