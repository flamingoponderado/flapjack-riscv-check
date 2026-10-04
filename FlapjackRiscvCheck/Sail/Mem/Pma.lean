import FlapjackRiscvCheck.Sail.Mem.Pmp
import LeanRV64D.Mem

/-!
# PMA checks for aligned RAM accesses

`PmaOK t a w acc`: the access of `w` bytes at physical address `a` falls in a
PMA region that permits the data access `acc` (readable for loads, writable
for stores). For an aligned access, `pmaCheck` then succeeds without
splitting.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

/-- Whether a PMA permits a plain data load (`false`) or store (`true`). -/
def pmaPermits (attrs : PMA) : Bool → Bool
  | false => attrs.readable
  | true => attrs.writable

/-- The plain data access of the given direction. -/
def dataAccess : Bool → MemoryAccessType mem_payload
  | false => .Load .Data
  | true => .Store .Data

structure PmaOK (t : SailState) (a : BitVec 64) (w : Nat) (write : Bool) : Prop where
  region : ∃ rs r, t.regs.get? Register.pma_regions = some rs ∧
    matching_pma_region rs (.Physaddr a) w = some r ∧ pmaPermits r.attributes write = true

theorem runSail_mag_pma_check_aligned (attrs : PMA) (acc : MemoryAccessType mem_payload)
    {a : BitVec 64} {w : Nat} (halign : is_aligned_paddr (.Physaddr a) w = true)
    (t : SailState) (b : Bool) (hb : runSail (is_mag_applicable_access acc w) t = some (b, t)) :
    runSail (mag_pma_check attrs acc (.Physaddr a) w) t = some (.Ok (.CannotSplit, 0), t) := by
  unfold mag_pma_check
  rw [runSail_bind_of_eq hb]
  simp only [halign, Bool.true_or, if_true]
  rfl

theorem runSail_is_mag_applicable_data (write : Bool) (w : Nat) (t : SailState) :
    runSail (is_mag_applicable_access (dataAccess write) w) t = some (decide (w ≤ 8), t) := by
  cases write <;> rfl

theorem runSail_pmaCheck {t : SailState} {a : BitVec 64} {w : Nat} {write : Bool}
    (h : PmaOK t a w write) (halign : is_aligned_paddr (.Physaddr a) w = true) :
    runSail (pmaCheck (.Physaddr a) w (dataAccess write) .PBMT_PMA false) t =
      some (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }, t) := by
  obtain ⟨rs, r, hrs, hr, hp⟩ := h.region
  unfold pmaCheck
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hrs)]
  simp only [hr, override_PMA]
  cases write <;> simp only [dataAccess, pmaPermits] at hp ⊢ <;>
    simp only [pure_bind, ExceptT_run_lift_bind, Functions.not, Bool.not_false] <;>
    simp only [bind_assoc, ExceptT_run_lift_bind] <;>
    rw [runSail_bind_of_eq (runSail_assert_true _ t)] <;>
    simp only [pure_bind, hp, Bool.not_true, Bool.false_eq_true, if_false, ExceptT_run_lift_bind] <;>
    first
    | rw [runSail_bind_of_eq (runSail_mag_pma_check_aligned _ (.Load .Data) halign t _ rfl)]; rfl
    | rw [runSail_bind_of_eq (runSail_mag_pma_check_aligned _ (.Store .Data) halign t _ rfl)]; rfl

end FlapjackRiscvCheck
