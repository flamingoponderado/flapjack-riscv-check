import Flapjack.RiscV.L3.Support
import LeanRV64D.Prelude
import LeanRV64D.Xlen

/-!
# Bit-level bridges between L3 and Sail helper functions
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

/-! ## L3 side -/

theorem l3_shamt6 (x : BitVec 64) :
    (BitVec.setWidth 64 (holWordExtract 6 5 0 x)).toNat = x.toNat % 64 := by
  simp [holWordExtract]
  omega

theorem l3_holV2w_single (b : Bool) :
    holV2w 64 [b] = if b then 1 else 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [holV2w, Flapjack.getLsbD_holFcpWord]
  cases b <;> rcases Nat.eq_zero_or_pos i with rfl | hpos <;>
    simp_all [Nat.pos_iff_ne_zero]

/-! ## Sail side -/

theorem sail_shamt6 (x : BitVec 64) :
    (Sail.BitVec.extractLsb x ((Functions.log2_xlen : Int) - 1).toNat 0).toNat = x.toNat % 64 := by
  simp [Sail.BitVec.extractLsb, Functions.log2_xlen]

theorem sail_shift_bits_left (x y : BitVec 64) :
    Sail.shift_bits_left x (Sail.BitVec.extractLsb y ((Functions.log2_xlen : Int) - 1).toNat 0) =
      x <<< (y.toNat % 64) := by
  simp only [Sail.shift_bits_left, BitVec.shiftLeft_eq', sail_shamt6]

theorem sail_shift_bits_right (x y : BitVec 64) :
    Sail.shift_bits_right x (Sail.BitVec.extractLsb y ((Functions.log2_xlen : Int) - 1).toNat 0) =
      x >>> (y.toNat % 64) := by
  simp only [Sail.shift_bits_right, BitVec.ushiftRight_eq', sail_shamt6]

theorem sail_shift_bits_right_arith (x y : BitVec 64) :
    shift_bits_right_arith x (Sail.BitVec.extractLsb y ((Functions.log2_xlen : Int) - 1).toNat 0) =
      x.sshiftRight (y.toNat % 64) := by
  simp only [shift_bits_right_arith, Sail.BitVec.toNatInt, sail_shamt6]
  rfl

theorem sail_sltu (x y : BitVec 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) = if x < y then 1 else 0 := by
  simp only [zopz0zI_u, Sail.BitVec.toNatInt, Int.ofNat_eq_natCast, Int.ofNat_lt, bool_to_bit,
    bool_bit_forwards, zero_extend, Sail.BitVec.zeroExtend]
  by_cases h : x < y <;> have h' := h <;> rw [BitVec.lt_def] at h' <;> simp [h, h']

end FlapjackRiscvCheck
