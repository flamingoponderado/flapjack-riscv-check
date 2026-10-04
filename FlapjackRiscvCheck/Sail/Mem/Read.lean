import FlapjackRiscvCheck.Sail.Mem.Phys
import FlapjackRiscvCheck.Sail.Mem.Addr
import FlapjackRiscvCheck.Sail.Mem.Page
import FlapjackRiscvCheck.Sail.Mem.Bytes

/-!
# Data loads through `vmem_read`

`SailLoadOK t a w`: the conditions under which an aligned `w`-byte machine-mode
load at `a` is a plain RAM read in Sail.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

structure SailAccessOK (t : SailState) (a : BitVec 64) (w : Nat) (write : Bool) : Prop where
  mem : SailMemInv t
  pmp : PmpOff t
  pma : PmaOK t a w write
  mmio : MmioFree t a w
  width : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8
  aligned : a.toNat % w = 0

theorem SailAccessOK.pos {t a w b} (h : SailAccessOK t a w b) : 0 < w := by
  rcases h.width with rfl | rfl | rfl | rfl <;> decide

theorem SailAccessOK.paligned {t a w b} (h : SailAccessOK t a w b) :
    is_aligned_paddr (.Physaddr a) w = true := by
  have := h.aligned
  simp only [is_aligned_paddr, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, beq_iff_eq]
  rw [Int.tmod_eq_emod_of_nonneg (by omega)]
  omega

theorem SailAccessOK.valigned {t a w b} (h : SailAccessOK t a w b) :
    is_aligned_vaddr (.Virtaddr a) w = true := h.paligned

theorem runSail_mem_read {t : SailState} {a : BitVec 64} {w : Nat} (h : SailAccessOK t a w false)
    {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t)) :
    runSail (mem_read (.Load .Data) .PBMT_PMA (.Physaddr a) w false false false) t =
      some (.Ok v, t) := by
  unfold mem_read
  rw [runSail_readReg_mstatus_priv h.mem]
  unfold mem_read_priv mem_read_priv_meta
  simp only [bind_assoc, pure_bind]
  rw [runSail_bind_of_eq (runSail_checked_mem_read h.pos h.pma h.pmp h.mmio h.paligned hram)]
  rfl

theorem runSail_translateAddr {t : SailState} (h : SailMemInv t) (a : BitVec 64)
    (acc : MemoryAccessType mem_payload)
    (hss : runSail (is_shadow_stack_access acc) t = some (false, t)) :
    runSail (translateAddr (.Virtaddr a) acc) t = some (.Ok (.Physaddr a, .PBMT_PMA, ()), t) := by
  unfold translateAddr
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_readReg_mstatus_priv h acc, runSail_bind_of_eq (runSail_translationMode_machine t),
    runSail_bind_of_eq hss]
  simp [bits_of_virtaddr, zero_extend, Sail.BitVec.zeroExtend]
  rfl

theorem runSail_translate_and_read_value {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w false) {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t)) :
    runSail (translate_and_read_value (.Virtaddr a) w (.Load .Data) false false false) t =
      some (.Ok (.Physaddr a, v), t) := by
  unfold translate_and_read_value
  rw [runSail_bind_of_eq (runSail_translateAddr h.mem a _ rfl)]
  simp only []
  rw [runSail_bind_of_eq (runSail_mem_read h hram)]
  rfl

theorem sail_updateSubrange_zeros_full (w : Nat) (hw : 0 < w) (v : BitVec (8 * w)) :
    Sail.BitVec.updateSubrange (zeros (n := 8 * w)) (8 * (w : Int) - 1).toNat 0
      (BitVec.setWidth ((8 * (w : Int) - 1).toNat + 1) v) = v := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (8 * (w : Int) - 1).toNat = 8 * w - 1 := by omega
  have h4 : 8 * w - 1 + 1 = 8 * w := by omega
  simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros, BitVec.toNat_setWidth, h2,
    h4, Nat.mod_eq_of_lt v.isLt]

theorem runSail_vmem_read_addr {t : SailState} {a : BitVec 64} {w : Nat}
    (h : SailAccessOK t a w false) {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t)) :
    runSail (vmem_read_addr (.Virtaddr a) w (.Load .Data) false false false) t =
      some (.Ok v, t) := by
  unfold vmem_read_addr
  rw [SailME.run, runSail_SailME_run]
  simp only [h.valigned, Functions.not, Bool.not_true, Bool.false_eq_true, if_false, pure_bind,
    bind_assoc, ExceptT_run_lift_bind, bits_of_virtaddr]
  rw [runSail_bind_of_eq (runSail_split_on_page_boundary h.width h.aligned t),
    runSail_readReg_mstatus_priv h.mem, runSail_bind_of_eq (runSail_translationMode_machine t)]
  have hb : (SATPMode.Bare != SATPMode.Bare) = false := rfl
  simp only [hb, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false, ite_self,
    pure_bind, bind_assoc, ExceptT_run_lift_bind, Int.toNat_natCast]
  generalize (SATPMode.Bare != SATPMode.Bare && 0>b0) = c
  cases c <;>
  · erw [runSail_bind_of_eq (runSail_translate_and_read_value h hram)]
    simp
    exact sail_updateSubrange_zeros_full w h.pos v

theorem runSail_vmem_read {t : SailState} {n : BitVec 5} {x : BitVec 64}
    (hx : sailGpr t n = some x) (offset : BitVec 64) {w : Nat}
    (h : SailAccessOK t (x + offset) w false) {v : BitVec (8 * w)}
    (hram : runSail (read_ram .Read_plain (.Physaddr (x + offset)) w false) t = some ((v, ()), t)) :
    runSail (vmem_read (.Regidx n) offset w (.Load .Data) false false false) t =
      some (.Ok v, t) := by
  unfold vmem_read
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_get_transformed_data_addr h.mem hx offset _ w)]
  simp only [pure_bind, ExceptT_run_lift]
  rw [runSail_map_ok (runSail_vmem_read_addr h hram)]

theorem runSail_read_ram {t : SailState} {a : BitVec 64} {w : Nat} {v : BitVec (8 * w)}
    (h : runSail (PreSail.readBytes w a.toNat : SailM (BitVec (8 * w) × Option Bool)) t =
      some ((v, none), t)) :
    runSail (read_ram .Read_plain (.Physaddr a) w false) t = some ((v, ()), t) := by
  unfold read_ram
  simp only [Bool.false_eq_true, if_false, pure_bind, bind_assoc]
  unfold LeanRV64D.ConcurrencyInterfaceV1.sail_mem_read Sail.ConcurrencyInterfaceV1.PreSail.sail_mem_read
  simp only [bind_assoc]
  rw [runSail_bind_of_eq h]
  rfl

end FlapjackRiscvCheck
