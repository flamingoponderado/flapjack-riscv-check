import Flapjack.RiscV.L3.Defs.Encode
import FlapjackRiscvCheck.Bridge
import Mathlib.Tactic.NormNum

/-!
# Encoded instruction words as numbers

`(Encode i).toNat` as an explicit sum of the instruction's fields, for the 37
tier-1 instructions. The decode proofs evaluate Sail's decoder guards against
these formulas with `omega`.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3

theorem toNat_or_shift {a b k : Nat} (hb : b < 2 ^ k) : a <<< k ||| b = a * 2 ^ k + b := by
  rw [← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq]

theorem holV2w_bit_toNat {n : Nat} (x : BitVec n) (k : Nat) :
    (holV2w 1 [x.getLsbD k]).toNat = x.toNat / 2 ^ k % 2 := by
  have ht : x.getLsbD k = decide (x.toNat / 2 ^ k % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  rw [ht]
  by_cases h : x.toNat / 2 ^ k % 2 = 1
  · rw [h]; decide
  · simp only [h, decide_false]
    have : x.toNat / 2 ^ k % 2 = 0 := by omega
    rw [this]; decide

/-- Compute `(Encode i).toNat` as a field formula. -/
macro "enc_toNat" : tactic => `(tactic| (
  simp only [Encode, Rtype, Itype, Stype, SBtype, UJtype, Utype, opc, BitVec.toNat_setWidth,
    BitVec.toNat_append, holWordExtract, BitVec.toNat_ofNat, holV2w_bit_toNat]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul]
  simp (disch := omega) only [toNat_or_shift]
  norm_num [Nat.shiftRight_eq_div_pow]
  simp (disch := omega) only [Nat.mod_eq_of_lt]
  (try simp only [BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow] at *)
  omega))

theorem enc_add (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.ADD (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_sub (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.SUB (rd, rs1, rs2)))).toNat = 0x20 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_and (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.AND (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 7 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_or (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.OR (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 6 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_xor (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.XOR (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 4 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_sltu (rd rs1 rs2 : BitVec 5) :
    (Encode (.ArithR (.SLTU (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 3 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_sll (rd rs1 rs2 : BitVec 5) :
    (Encode (.Shift (.SLL (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 1 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_srl (rd rs1 rs2 : BitVec 5) :
    (Encode (.Shift (.SRL (rd, rs1, rs2)))).toNat = 0 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_sra (rd rs1 rs2 : BitVec 5) :
    (Encode (.Shift (.SRA (rd, rs1, rs2)))).toNat = 0x20 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_mul (rd rs1 rs2 : BitVec 5) :
    (Encode (.MulDiv (.MUL (rd, rs1, rs2)))).toNat = 1 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_mulhu (rd rs1 rs2 : BitVec 5) :
    (Encode (.MulDiv (.MULHU (rd, rs1, rs2)))).toNat = 1 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 3 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_div (rd rs1 rs2 : BitVec 5) :
    (Encode (.MulDiv (.DIV (rd, rs1, rs2)))).toNat = 1 * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 4 * 2^12 + rd.toNat * 2^7 + 0x33 := by
  have := rd.isLt; have := rs1.isLt; have := rs2.isLt
  enc_toNat

theorem enc_addi (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.ArithI (.ADDI (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_andi (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.ArithI (.ANDI (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 7 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_ori (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.ArithI (.ORI (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 6 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_xori (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.ArithI (.XORI (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 4 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_ld (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Load (.LD (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 3 * 2^12 + rd.toNat * 2^7 + 0x03 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_lwu (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Load (.LWU (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 6 * 2^12 + rd.toNat * 2^7 + 0x03 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_lhu (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Load (.LHU (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + rd.toNat * 2^7 + 0x03 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_lbu (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Load (.LBU (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 4 * 2^12 + rd.toNat * 2^7 + 0x03 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_jalr (rd rs1 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Branch (.JALR (rd, rs1, imm)))).toNat = imm.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + rd.toNat * 2^7 + 0x67 := by
  have := rd.isLt; have := rs1.isLt; have := imm.isLt
  enc_toNat

theorem enc_slli (rd rs1 : BitVec 5) (sh : BitVec 6) :
    (Encode (.Shift (.SLLI (rd, rs1, sh)))).toNat = 0 * 2^26 + sh.toNat * 2^20 + rs1.toNat * 2^15 + 1 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := sh.isLt
  enc_toNat

theorem enc_srli (rd rs1 : BitVec 5) (sh : BitVec 6) :
    (Encode (.Shift (.SRLI (rd, rs1, sh)))).toNat = 0 * 2^26 + sh.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := sh.isLt
  enc_toNat

theorem enc_srai (rd rs1 : BitVec 5) (sh : BitVec 6) :
    (Encode (.Shift (.SRAI (rd, rs1, sh)))).toNat = 0x10 * 2^26 + sh.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + rd.toNat * 2^7 + 0x13 := by
  have := rd.isLt; have := rs1.isLt; have := sh.isLt
  enc_toNat

theorem enc_sb (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Store (.SB (rs1, rs2, imm)))).toNat = (imm.extractLsb 11 5).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + (imm.extractLsb 4 0).toNat * 2^7 + 0x23 := by
  have := rs1.isLt; have := rs2.isLt; have := imm.isLt
  enc_toNat

theorem enc_sh (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Store (.SH (rs1, rs2, imm)))).toNat = (imm.extractLsb 11 5).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 1 * 2^12 + (imm.extractLsb 4 0).toNat * 2^7 + 0x23 := by
  have := rs1.isLt; have := rs2.isLt; have := imm.isLt
  enc_toNat

theorem enc_sw (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Store (.SW (rs1, rs2, imm)))).toNat = (imm.extractLsb 11 5).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 2 * 2^12 + (imm.extractLsb 4 0).toNat * 2^7 + 0x23 := by
  have := rs1.isLt; have := rs2.isLt; have := imm.isLt
  enc_toNat

theorem enc_sd (rs1 rs2 : BitVec 5) (imm : BitVec 12) :
    (Encode (.Store (.SD (rs1, rs2, imm)))).toNat = (imm.extractLsb 11 5).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 3 * 2^12 + (imm.extractLsb 4 0).toNat * 2^7 + 0x23 := by
  have := rs1.isLt; have := rs2.isLt; have := imm.isLt
  enc_toNat

theorem enc_lui (rd : BitVec 5) (imm : BitVec 20) :
    (Encode (.ArithI (.LUI (rd, imm)))).toNat = imm.toNat * 2^12 + rd.toNat * 2^7 + 0x37 := by
  have := rd.isLt; have := imm.isLt
  enc_toNat

theorem enc_auipc (rd : BitVec 5) (imm : BitVec 20) :
    (Encode (.ArithI (.AUIPC (rd, imm)))).toNat = imm.toNat * 2^12 + rd.toNat * 2^7 + 0x17 := by
  have := rd.isLt; have := imm.isLt
  enc_toNat

theorem enc_beq (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BEQ (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 0 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_bne (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BNE (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 1 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_blt (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BLT (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 4 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_bge (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BGE (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 5 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_bltu (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BLTU (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 6 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_bgeu (rs1 rs2 : BitVec 5) (offs : BitVec 12) :
    (Encode (.Branch (.BGEU (rs1, rs2, offs)))).toNat = (offs.extractLsb 11 11).toNat * 2^31 + (offs.extractLsb 9 4).toNat * 2^25 + rs2.toNat * 2^20 + rs1.toNat * 2^15 + 7 * 2^12 + (offs.extractLsb 3 0).toNat * 2^8 + (offs.extractLsb 10 10).toNat * 2^7 + 0x63 := by
  have := rs1.isLt; have := rs2.isLt; have := offs.isLt
  enc_toNat

theorem enc_jal (rd : BitVec 5) (imm : BitVec 20) :
    (Encode (.Branch (.JAL (rd, imm)))).toNat = (imm.extractLsb 19 19).toNat * 2^31 + (imm.extractLsb 9 0).toNat * 2^21 + (imm.extractLsb 10 10).toNat * 2^20 + (imm.extractLsb 18 11).toNat * 2^12 + rd.toNat * 2^7 + 0x6F := by
  have := rd.isLt; have := imm.isLt
  enc_toNat

end FlapjackRiscvCheck
