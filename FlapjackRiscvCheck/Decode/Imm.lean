/-!
# Reassembling split immediates

S-, B- and J-type encodings scatter an immediate's bits; Sail's decoder
concatenates the pieces again. These lemmas say the concatenation is the
original immediate. (Kept free of Sail imports, whose `BitVec` width
coercions would otherwise change the statements.)
-/

namespace FlapjackRiscvCheck

theorem toNat_or_shift' {a b k : Nat} (hb : b < 2 ^ k) : a <<< k ||| b = a * 2 ^ k + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

macro "reassemble" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]
  simp (disch := omega) only [toNat_or_shift']
  omega))

theorem imm_S (imm : BitVec 12) : imm.extractLsb 11 5 ++ imm.extractLsb 4 0 = imm := by
  have := imm.isLt; reassemble

theorem imm_B (offs : BitVec 12) :
    offs.extractLsb 11 11 ++ offs.extractLsb 10 10 ++ offs.extractLsb 9 4 ++ offs.extractLsb 3 0 = offs := by
  have := offs.isLt; reassemble

theorem imm_J (imm : BitVec 20) :
    imm.extractLsb 19 19 ++ imm.extractLsb 18 11 ++ imm.extractLsb 10 10 ++ imm.extractLsb 9 0 = imm := by
  have := imm.isLt; reassemble

end FlapjackRiscvCheck
