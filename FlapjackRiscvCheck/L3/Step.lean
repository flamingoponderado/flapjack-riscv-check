import FlapjackRiscvCheck.L3.Control
import Flapjack.RiscV.L3.Step.Next
import Flapjack.RiscV.L3.Step.FetchTheorems

/-!
# One L3 step on an encoded 32-bit instruction

`Fetch` of a word whose four bytes sit at `PC` (bare VM), and `NextRISCV` as
`Run` followed by committing the next PC.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step

set_option maxRecDepth 100000

/-- The `k`-th little-endian byte of a word. -/
abbrev wordByte (w : BitVec 32) (k : Nat) : BitVec 8 := w.extractLsb' (8 * k) 8

theorem l3_word_reassemble (w : BitVec 32) :
    BitVec.setWidth 32 (wordByte w 3 ++ BitVec.setWidth 24 (wordByte w 2 ++
      BitVec.setWidth 16 (wordByte w 1 ++ wordByte w 0))) = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem l3_fetch_word (s : riscv_state) (w : BitVec 32)
    (vm : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (low0 : w.getLsbD 0 = true) (low1 : w.getLsbD 1 = true)
    (hb : ∀ k < 4, s.MEM8 (PC s + BitVec.ofNat 64 k) = wordByte w k) :
    Fetch s = (.Word w, { s with c_Skip := holUpdate s.procID 4 s.c_Skip }) := by
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide)
  have b2 := hb 2 (by decide); have b3 := hb 3 (by decide)
  simp only [PC] at b0 b1 b2 b3
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at b0
  have lo0 : (wordByte w 0).getLsbD 0 = true := by simpa [BitVec.getLsbD_extractLsb'] using low0
  have lo1 : (wordByte w 0).getLsbD 1 = true := by simpa [BitVec.getLsbD_extractLsb'] using low1
  rw [fetch_bare s vm]
  simp only [rawReadInst, boolify8, b0, b1, b2, b3, lo0, lo1, «write'Skip», Bool.and_self,
    if_true, l3_word_reassemble]
  rfl

theorem l3_write'NextFetch_none (s : riscv_state) (h : NextFetch s = none) :
    «write'NextFetch» none s = s := by
  cases s
  simp only [«write'NextFetch», NextFetch] at h ⊢
  congr
  funext c
  simp only [holUpdate]
  split <;> simp_all

/-- `NextRISCV` after a successful fetch, decode and exception-free `Run`. -/
theorem l3_next (s s1 s2 : riscv_state) (w : BitVec 32) (i : instruction) (npc : BitVec 64)
    (hfetch : Fetch s = (.Word w, s1)) (hdec : DecodeAny (.Word w) = i) (hrun : Run i s1 = s2)
    (hexc : s2.exception = .NoException) (hnpc : l3NextPC s2 = some npc) :
    NextRISCV s = some («write'PC» npc («write'NextFetch» none s2)) := by
  rw [NextRISCV_equation, hfetch]
  simp only [hdec, hrun, hexc, bne_self_eq_false, Bool.false_eq_true, if_false]
  unfold l3NextPC at hnpc
  split at hnpc
  · rename_i hn
    simp only [Option.some.injEq] at hnpc
    subst hnpc
    simp only [hn, l3_write'NextFetch_none s2 hn, update_pc]
  · rename_i a hn
    simp only [Option.some.injEq] at hnpc
    subst hnpc
    simp only [hn, update_pc]
  · simp at hnpc

end FlapjackRiscvCheck
