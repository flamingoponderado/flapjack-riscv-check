import LeanRV64D.Arithmetic
import Flapjack.RiscV.L3.Support
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Bit-level bridges for the M extension

Sail computes products and quotients over `Int` and truncates with
`to_bits_truncate`; L3 uses `BitVec` arithmetic on widened words.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

theorem extractLsb'_zero_ofInt {l m : Nat} (h : l ≤ m) (n : Int) :
    (BitVec.ofInt m n).extractLsb' 0 l = BitVec.ofInt l n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt, Nat.shiftRight_zero]
  have h1 : (0:Int) ≤ n % (2 ^ m : Nat) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
  have h2 : (0:Int) ≤ n % (2 ^ l : Nat) :=
    Int.emod_nonneg _ (by exact_mod_cast (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _)))
  apply Int.natCast_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2]
  apply Int.emod_emod_of_dvd
  exact_mod_cast Nat.pow_dvd_pow 2 h

theorem get_slice_int_zero (l : Nat) (n : Int) : Sail.get_slice_int l n 0 = BitVec.ofInt l n :=
  extractLsb'_zero_ofInt (by omega) n

theorem ofInt_toInt_mul (a b : BitVec 64) : BitVec.ofInt 64 (a.toInt * b.toInt) = a * b := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofInt, BitVec.toInt_mul]

theorem sail_mul_low (a b : BitVec 64) :
    (mult_to_bits_half (l := 64) .Signed .Signed a b .Low : BitVec 64) = a * b := by
  rw [← ofInt_toInt_mul]
  simp only [mult_to_bits_half, to_bits_truncate, get_slice_int_zero, Sail.BitVec.extractLsb]
  exact extractLsb'_zero_ofInt (by decide) _

theorem mul_lt_128 (a b : BitVec 64) : a.toNat * b.toNat < 2 ^ 128 :=
  calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' a.isLt b.isLt
    _ = 2 ^ 128 := by norm_num

theorem sail_mulhu (a b : BitVec 64) :
    (mult_to_bits_half (l := 64) .Unsigned .Unsigned a b .High : BitVec 64) =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  have hlt := mul_lt_128 a b
  simp only [mult_to_bits_half, to_bits_truncate, get_slice_int_zero, Sail.BitVec.extractLsb,
    Sail.BitVec.toNatInt, xlen]
  apply BitVec.eq_of_toNat_eq
  rw [show (Int.ofNat a.toNat * Int.ofNat b.toNat) = ((a.toNat * b.toNat : Nat) : Int) by simp]
  have hlt' : a.toNat * b.toNat < 340282366920938463463374607431768211456 := by
    simpa using hlt
  simp [Nat.shiftRight_eq_div_pow]
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hlt')]
  rfl

theorem l3_mulhu (a b : BitVec 64) :
    holWordExtract 64 127 64 (BitVec.setWidth 128 a * BitVec.setWidth 128 b) =
      BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  have hlt := mul_lt_128 a b
  have hlt' : a.toNat * b.toNat < 340282366920938463463374607431768211456 := by
    simpa using hlt
  simp [holWordExtract, BitVec.toNat_mul, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hlt']

theorem tdiv_le_two_pow (a b : BitVec 64) : a.toInt.tdiv b.toInt ≤ 2 ^ 63 := by
  have h1 := Int.natAbs_tdiv_le_natAbs a.toInt b.toInt
  have h2 := BitVec.le_toInt a
  have h3 := BitVec.toInt_lt (x := a)
  simp at h2 h3
  omega

theorem div_value (a b : BitVec 64) :
    BitVec.ofInt 64
      (if (if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt) ≥ 2 ^ 63 then -2 ^ 63
       else if b.toInt = 0 then -1 else a.toInt.tdiv b.toInt) =
      if b = 0 then -1 else a.sdiv b := by
  by_cases hb : b = 0
  · subst hb
    simp
  · have hb' : b.toInt ≠ 0 := by
      intro h; apply hb; apply BitVec.eq_of_toInt_eq; simpa using h
    simp only [hb, hb', if_false]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
    split
    · have hq : a.toInt.tdiv b.toInt = 2 ^ 63 := le_antisymm (tdiv_le_two_pow a b) ‹_›
      rw [hq]; decide
    · rfl

end FlapjackRiscvCheck
