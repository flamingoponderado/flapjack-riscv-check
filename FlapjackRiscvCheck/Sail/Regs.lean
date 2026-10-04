import FlapjackRiscvCheck.Sail.Run
import LeanRV64D.Regs
import Mathlib.Tactic.IntervalCases

/-!
# Sail general-purpose registers

`sailGpr t n` reads Sail's `x<n>` register out of the state's register map (`0`
for `x0`, which Sail does not store). The lemmas reduce `rX_bits` / `wX_bits`
to it.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

set_option linter.unusedSimpArgs false

/-- The value of Sail register `x<n>` in `t`, `none` if absent from the register map. -/
def sailGpr (t : SailState) (n : BitVec 5) : Option (BitVec 64) :=
  match n.toNat with
  | 0 => some 0
  | 1 => t.regs.get? Register.x1
  | 2 => t.regs.get? Register.x2
  | 3 => t.regs.get? Register.x3
  | 4 => t.regs.get? Register.x4
  | 5 => t.regs.get? Register.x5
  | 6 => t.regs.get? Register.x6
  | 7 => t.regs.get? Register.x7
  | 8 => t.regs.get? Register.x8
  | 9 => t.regs.get? Register.x9
  | 10 => t.regs.get? Register.x10
  | 11 => t.regs.get? Register.x11
  | 12 => t.regs.get? Register.x12
  | 13 => t.regs.get? Register.x13
  | 14 => t.regs.get? Register.x14
  | 15 => t.regs.get? Register.x15
  | 16 => t.regs.get? Register.x16
  | 17 => t.regs.get? Register.x17
  | 18 => t.regs.get? Register.x18
  | 19 => t.regs.get? Register.x19
  | 20 => t.regs.get? Register.x20
  | 21 => t.regs.get? Register.x21
  | 22 => t.regs.get? Register.x22
  | 23 => t.regs.get? Register.x23
  | 24 => t.regs.get? Register.x24
  | 25 => t.regs.get? Register.x25
  | 26 => t.regs.get? Register.x26
  | 27 => t.regs.get? Register.x27
  | 28 => t.regs.get? Register.x28
  | 29 => t.regs.get? Register.x29
  | 30 => t.regs.get? Register.x30
  | _ => t.regs.get? Register.x31

theorem runSail_readReg {r : Register} {t : SailState} {v : RegisterType r}
    (h : t.regs.get? r = some v) :
    runSail (Sail.ConcurrencyInterfaceV1.PreSail.readReg r : SailM (RegisterType r)) t = some (v, t) := by
  simp [runSail, Sail.ConcurrencyInterfaceV1.PreSail.readReg, EStateM.run, h, bind, EStateM.bind, get, getThe,
    MonadStateOf.get, EStateM.get, pure, EStateM.pure]

theorem runSail_rX_bits {t : SailState} {n : BitVec 5} {v : BitVec 64}
    (h : sailGpr t n = some v) :
    runSail (rX_bits (.Regidx n)) t = some (v, t) := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  simp only [sailGpr, BitVec.toNat_ofNat] at h
  interval_cases k <;> (try simp only [Nat.reduceMod] at h) <;>
    simp only [rX_bits, rX, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.reduceMod,
      Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, Int.reduceToNat] <;>
    first
    | (cases h; rfl)
    | (rw [runSail_bind_of_eq (runSail_readReg h)]; rfl)

/-- `t` with Sail register `x<n>` set to `v` (unchanged for `x0`). -/
def sailSetGpr (t : SailState) (n : BitVec 5) (v : BitVec 64) : SailState :=
  match n.toNat with
  | 0 => t
  | 1 => { t with regs := t.regs.insert Register.x1 v }
  | 2 => { t with regs := t.regs.insert Register.x2 v }
  | 3 => { t with regs := t.regs.insert Register.x3 v }
  | 4 => { t with regs := t.regs.insert Register.x4 v }
  | 5 => { t with regs := t.regs.insert Register.x5 v }
  | 6 => { t with regs := t.regs.insert Register.x6 v }
  | 7 => { t with regs := t.regs.insert Register.x7 v }
  | 8 => { t with regs := t.regs.insert Register.x8 v }
  | 9 => { t with regs := t.regs.insert Register.x9 v }
  | 10 => { t with regs := t.regs.insert Register.x10 v }
  | 11 => { t with regs := t.regs.insert Register.x11 v }
  | 12 => { t with regs := t.regs.insert Register.x12 v }
  | 13 => { t with regs := t.regs.insert Register.x13 v }
  | 14 => { t with regs := t.regs.insert Register.x14 v }
  | 15 => { t with regs := t.regs.insert Register.x15 v }
  | 16 => { t with regs := t.regs.insert Register.x16 v }
  | 17 => { t with regs := t.regs.insert Register.x17 v }
  | 18 => { t with regs := t.regs.insert Register.x18 v }
  | 19 => { t with regs := t.regs.insert Register.x19 v }
  | 20 => { t with regs := t.regs.insert Register.x20 v }
  | 21 => { t with regs := t.regs.insert Register.x21 v }
  | 22 => { t with regs := t.regs.insert Register.x22 v }
  | 23 => { t with regs := t.regs.insert Register.x23 v }
  | 24 => { t with regs := t.regs.insert Register.x24 v }
  | 25 => { t with regs := t.regs.insert Register.x25 v }
  | 26 => { t with regs := t.regs.insert Register.x26 v }
  | 27 => { t with regs := t.regs.insert Register.x27 v }
  | 28 => { t with regs := t.regs.insert Register.x28 v }
  | 29 => { t with regs := t.regs.insert Register.x29 v }
  | 30 => { t with regs := t.regs.insert Register.x30 v }
  | _ => { t with regs := t.regs.insert Register.x31 v }

theorem runSail_reg_name_forwards (r : regidx) (t : SailState) :
    ∃ name, runSail (reg_name_forwards r) t = some (name, t) := by
  cases r
  simp [reg_name_forwards, encdec_reg_forwards_matches, get_config_use_abi_names, Functions.not]

theorem runSail_writeReg {r : Register} (v : RegisterType r) (t : SailState) :
    runSail (Sail.ConcurrencyInterfaceV1.PreSail.writeReg r v : SailM PUnit) t =
      some (⟨⟩, { t with regs := t.regs.insert r v }) := rfl

theorem runSail_xreg_write_callback (r : regidx) (v : BitVec 64) (t : SailState) :
    runSail (xreg_write_callback r v) t = some ((), t) := by
  obtain ⟨name, h⟩ := runSail_reg_name_forwards r t
  unfold xreg_write_callback
  rw [runSail_bind_of_eq h]
  rfl

theorem runSail_wX_bits (t : SailState) (n : BitVec 5) (v : BitVec 64) :
    runSail (wX_bits (.Regidx n) v) t = some ((), sailSetGpr t n v) := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;>
    simp only [wX_bits, wX, Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.reduceMod,
      Int.ofNat_eq_natCast, Int.toNat_natCast, BitVec.reduceToNat, Int.reduceToNat] <;>
    rfl

end FlapjackRiscvCheck
