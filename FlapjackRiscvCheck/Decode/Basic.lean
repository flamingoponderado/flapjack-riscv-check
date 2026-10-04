import FlapjackRiscvCheck.Sail.DecodePrefix
import FlapjackRiscvCheck.Sail.Jump
import FlapjackRiscvCheck.Exec.Contract
import Mathlib.Tactic.IntervalCases

/-!
# Toolkit for decoding encoded words in Sail

A decode proof fixes a word `w` together with `hw : w.toNat = <field formula>`
(from the encoding), steps through `decodePrefix` one block at a time
(`unfold decodeBlock<k>; guard_simp hw`), and discharges every guard
`Sail.BitVec.extractLsb w hi lo == c` by `omega` on `w.toNat`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions

theorem extractLsb_toNat' (w : BitVec 32) (hi lo : Nat) :
    (Sail.BitVec.extractLsb w hi lo).toNat = w.toNat / 2 ^ lo % 2 ^ (hi - lo + 1) := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]

theorem beq_false_of_toNat {n : Nat} {x c : BitVec n} (h : x.toNat ≠ c.toNat) : (x == c) = false := by
  simpa [beq_iff_eq, ← BitVec.toNat_inj] using h

theorem beq_true_of_toNat {n : Nat} {x c : BitVec n} (h : x.toNat = c.toNat) : (x == c) = true := by
  simpa [beq_iff_eq, ← BitVec.toNat_inj] using h

theorem extractLsb_full {n : Nat} (x : BitVec (n + 1)) : BitVec.extractLsb n 0 x = x := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat, Nat.mod_eq_of_lt x.isLt]

/-- Decide a guard about `w` by `omega` from `hw : w.toNat = …`. -/
macro "guard_omega" hw:ident : tactic =>
  `(tactic| (simp only [extractLsb_toNat', $hw:ident, BitVec.toNat_ofNat]; omega))

/-- Simplify the current decoder block: rewrite the known fields of `w` (`facts`), evaluate
the field decoders on them, decide the remaining guards by `omega`, drop dead branches. -/
syntax "guard_simp" ident "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| guard_simp $hw [$facts,*]) =>
    `(tactic| ((try dsimp only); simp (config := { decide := true }) (disch := guard_omega $hw) only [$facts,*,
      Functions.base_E_enabled, Functions.not, beq_self_eq_true, Bool.or_true, Bool.true_or,
      Bool.not_false, ite_true, ite_false, Bool.ite_eq_true_distrib,
      beq_false_of_toNat, beq_true_of_toNat,
      encdec_reg_backwards_matches, encdec_uop_backwards_matches, encdec_ntl_backwards_matches,
      encdec_mul_op_backwards_matches, encdec_iop_backwards_matches,
      encdec_cbop_zicbop_backwards_matches, encdec_bop_backwards_matches,
      encdec_amoop_backwards_matches, width_enc_backwards_matches,
      width_enc_wide_backwards_matches, bool_bit_backwards_matches,
      Bool.and_false, Bool.false_and, Bool.and_true, Bool.true_and, Bool.false_eq_true, if_false,
      if_true, pure_bind, bind_assoc]))

/-- Finish a matched block: register and field decoders, then the continuation. -/
macro "decode_finish" : tactic =>
  `(tactic| simp (config := { decide := true }) [encdec_reg_backwards_matches, encdec_reg_backwards,
    encdec_uop_backwards, encdec_iop_backwards, encdec_bop_backwards, encdec_mul_op_backwards,
    width_enc_backwards, bool_bit_backwards, Functions.base_E_enabled, Functions.not,
    Functions.regidx_bit_width, Sail.BitVec.extractLsb, extractLsb_full, runSail_map])

/-! ## Extension checks reached by the decoder prefix -/

/-- What the decoder prefix reads besides the word: machine mode, no landing pads, `misa.M`. -/
structure DecodeInv (t : SailState) : Prop where
  machine : t.regs.get? Register.cur_privilege = some .Machine
  noLandingPads : ∃ c, t.regs.get? Register.mseccfg = some c ∧ _get_Seccfg_MLPE c = 0
  misaM : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_M m = 1

theorem ExecPre.decodeInv {s t} (h : ExecPre s t) : DecodeInv t :=
  ⟨h.machine, h.noLandingPads, h.misaM⟩

theorem runSail_currentlyEnabled_pause (t : SailState) :
    runSail (currentlyEnabled .Ext_Zihintpause) t = some (true, t) := by
  rw [currentlyEnabled]; simp [hartSupports]

theorem runSail_currentlyEnabled_zicbop (t : SailState) :
    runSail (currentlyEnabled .Ext_Zicbop) t = some (true, t) := by
  rw [currentlyEnabled]; simp [hartSupports]

theorem runSail_currentlyEnabled_ntl (t : SailState) :
    runSail (currentlyEnabled .Ext_Zihintntl) t = some (true, t) := by
  rw [currentlyEnabled]; simp [hartSupports]

theorem runSail_currentlyEnabled_M {t} (h : DecodeInv t) :
    runSail (currentlyEnabled .Ext_M) t = some (true, t) := by
  obtain ⟨m, hm, hM⟩ := h.misaM
  rw [currentlyEnabled]
  rw [runSail_bind_of_eq (runSail_readReg hm)]
  simp [hartSupports, hM]

theorem runSail_currentlyEnabled_Zmmul {t} (h : DecodeInv t) :
    runSail (currentlyEnabled .Ext_Zmmul) t = some (true, t) := by
  rw [currentlyEnabled]
  rw [runSail_bind_of_eq (runSail_currentlyEnabled_M h)]
  simp [hartSupports]

theorem runSail_currentlyEnabled_zicfilp {t} (h : DecodeInv t) :
    runSail (currentlyEnabled .Ext_Zicfilp) t = some (false, t) := by
  obtain ⟨c, hc, hL⟩ := h.noLandingPads
  rw [currentlyEnabled]
  rw [runSail_bind_of_eq (show runSail (currentlyEnabled .Ext_Zicsr) t = some (true, t) by
    rw [currentlyEnabled]; simp [hartSupports])]
  simp only [hartSupports, Bool.true_and]
  rw [runSail_bind_of_eq (runSail_readReg h.machine)]
  simp [get_xLPE, runSail, EStateM.run, EStateM.bind, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get, hc, hL,
    bind, pure, bool_bit_backwards]

end FlapjackRiscvCheck
