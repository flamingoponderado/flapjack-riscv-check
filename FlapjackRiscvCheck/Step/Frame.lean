import FlapjackRiscvCheck.Sail.Step
import FlapjackRiscvCheck.Exec.Contract

/-!
# Sail registers a step may change, and invariants that survive them

A tier-1 step changes only the integer registers, `nextPC`, `PC`, `minstret`
and `minstret_increment` (`volatileReg`). Every Sail-side invariant reads
other registers only, so it transfers along `RegsAgree`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions

def volatileReg (r : Register) : Bool :=
  Register.isGpr r || r == .nextPC || r == .PC || r == .minstret || r == .minstret_increment

/-- `t'` agrees with `t` on every non-volatile register. -/
def RegsAgree (t t' : SailState) : Prop :=
  ∀ r, volatileReg r = false → t'.regs.get? r = t.regs.get? r

theorem RegsAgree.refl (t : SailState) : RegsAgree t t := fun _ _ => rfl

theorem RegsAgree.trans {t₁ t₂ t₃ : SailState} (h₁ : RegsAgree t₁ t₂) (h₂ : RegsAgree t₂ t₃) :
    RegsAgree t₁ t₃ := fun r hr => (h₂ r hr).trans (h₁ r hr)

theorem RegsAgree.insert (t : SailState) {r : Register} (hr : volatileReg r = true)
    (v : RegisterType r) : RegsAgree t { t with regs := t.regs.insert r v } := by
  intro r' hr'
  have : r ≠ r' := by rintro rfl; simp_all
  simp [Std.ExtDHashMap.get?_insert, this]

theorem RegsAgree.ofFrame {t t' : SailState} (h : SailRegFrame t t') : RegsAgree t t' := by
  intro r hr
  apply h r
  · simp [volatileReg] at hr; exact hr.1.1.1.1
  · intro e; subst e; simp [volatileReg] at hr

/-- Rewrite a read of a non-volatile register. -/
macro "agree_rw" h:ident : tactic =>
  `(tactic| (rw [($h) _ rfl]))

theorem SailMemInv.transfer {t t'} (h : SailMemInv t) (ha : RegsAgree t t') : SailMemInv t' where
  machine := by rw [ha _ rfl]; exact h.machine
  mstatus := by rw [ha _ rfl]; exact h.mstatus
  mseccfg := by rw [ha _ rfl]; exact h.mseccfg

theorem PmpOff.transfer {t t'} (h : PmpOff t) (ha : RegsAgree t t') : PmpOff t' where
  cfg := by rw [ha _ rfl]; exact h.cfg
  addr := by rw [ha _ rfl]; exact h.addr

theorem PmaOK.transfer {t t' a w b} (h : PmaOK t a w b) (ha : RegsAgree t t') : PmaOK t' a w b where
  region := by rw [ha _ rfl]; exact h.region

theorem PmaExecOK.transfer {t t' a w} (h : PmaExecOK t a w) (ha : RegsAgree t t') :
    PmaExecOK t' a w where
  region := by rw [ha _ rfl]; exact h.region

theorem MmioFree.transfer {t t' a w} (h : MmioFree t a w) (ha : RegsAgree t t') :
    MmioFree t' a w where
  clint := h.clint
  sig := h.sig
  htif := by rw [ha _ rfl]; exact h.htif

theorem SailAccessOK.transfer {t t' a w b} (h : SailAccessOK t a w b) (ha : RegsAgree t t') :
    SailAccessOK t' a w b where
  mem := h.mem.transfer ha
  pmp := h.pmp.transfer ha
  pma := h.pma.transfer ha
  mmio := h.mmio.transfer ha
  width := h.width
  aligned := h.aligned

theorem SailFetchOK.transfer {t t' pc} (h : SailFetchOK t pc) (ha : RegsAgree t t') :
    SailFetchOK t' pc where
  mem := h.mem.transfer ha
  pmp := h.pmp.transfer ha
  pma := h.pma.transfer ha
  mmio := h.mmio.transfer ha
  aligned := h.aligned

theorem SailStepInv.transfer {t t'} (h : SailStepInv t) (ha : RegsAgree t t')
    (hm : ∃ v, t'.regs.get? Register.minstret = some v) : SailStepInv t' where
  active := by rw [ha _ rfl]; exact h.active
  elp := by rw [ha _ rfl]; exact h.elp
  mstatus := by rw [ha _ rfl]; exact h.mstatus
  misa := by rw [ha _ rfl]; exact h.misa
  mideleg := by rw [ha _ rfl]; exact h.mideleg
  mip := by rw [ha _ rfl]; exact h.mip
  mie := by rw [ha _ rfl]; exact h.mie
  sig_meip := by rw [ha _ rfl]; exact h.sig_meip
  sig_seip := by rw [ha _ rfl]; exact h.sig_seip
  mcountinhibit := by rw [ha _ rfl]; exact h.mcountinhibit
  minstretcfg := by rw [ha _ rfl]; exact h.minstretcfg
  minstret := hm

end FlapjackRiscvCheck
