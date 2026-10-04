import FlapjackRiscvCheck.Sail.Mem.Inv
import LeanRV64D.SplitAccessUtils

/-!
# Aligned accesses stay within a page

`split_on_page_boundary a w` returns `(w, 0)` for a `w`-aligned access with
`w ≤ 8`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

theorem testBit_add_small (n k i : Nat) (hi : 12 ≤ i) (hk : n % 4096 + k < 4096) :
    (n + k).testBit i = n.testBit i := by
  have e : ∀ m, m.testBit i = (m / 2 ^ 12).testBit (i - 12) := by
    intro m; rw [Nat.testBit_div_two_pow]; congr 1; omega
  rw [e, e n]
  congr 1
  omega

theorem page_mask_eq (a : BitVec 64) (k : Nat) (hk : a.toNat % 4096 + k < 4096) :
    (a &&& ~~~(4095#64)) = ((a + BitVec.ofNat 64 k) &&& ~~~(4095#64)) := by
  have hlt : a.toNat + k < 2 ^ 64 := by have := a.isLt; omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  by_cases h12 : i < 12
  · have : (4095#64).getLsbD i = true := by
      rw [BitVec.getLsbD_ofNat]; simp [hi]; interval_cases i <;> decide
    simp [this]
  · have h4 : (4095#64).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      simp only [Bool.and_eq_false_iff]
      right
      apply Nat.testBit_lt_two_pow
      calc 4095 < 2 ^ 12 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [h4]
    simp only [Bool.not_false, Bool.and_true]
    rw [BitVec.getLsbD, BitVec.getLsbD, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hlt,
      testBit_add_small _ _ _ (by omega) hk]

theorem runSail_split_on_page_boundary {a : BitVec 64} {w : Nat}
    (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) (ha : a.toNat % w = 0) (t : SailState) :
    runSail (split_on_page_boundary a w) t = some (((w : Int), (0 : Int)), t) := by
  have hk : a.toNat % 4096 + (w - 1) < 4096 := by rcases hw with rfl | rfl | rfl | rfl <;> omega
  unfold split_on_page_boundary
  have hmask : Sail.BitVec.updateSubrange (ones (n := 64))
      (((Functions.pagesize_bits : Int) - 1).toNat) 0 zeros = ~~~(4095#64) := by decide
  have hw1 : Sail.BitVec.subInt (Sail.BitVec.addInt a (w : Int)) 1 = a + BitVec.ofNat 64 (w - 1) := by
    simp only [Sail.BitVec.subInt, Sail.BitVec.addInt]
    rcases hw with rfl | rfl | rfl | rfl <;> simp <;> bv_omega
  simp only [hw1]
  erw [hmask]
  rw [← page_mask_eq a (w - 1) hk]
  simp only [beq_self_eq_true, if_true]
  rfl

end FlapjackRiscvCheck
