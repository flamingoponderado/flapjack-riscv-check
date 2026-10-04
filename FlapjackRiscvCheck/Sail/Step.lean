import FlapjackRiscvCheck.Sail.Mem.Fetch
import LeanRV64D.Step

/-!
# Sail's top-level step around `execute`

`SailStepInv t`: the registers `try_step` consults outside `execute` exist, the
hart is active, no landing pad is expected, and machine interrupts are
globally disabled (`mstatus.MIE = 0`), so `dispatchInterrupt` finds nothing.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

structure SailStepInv (t : SailState) : Prop where
  active : t.regs.get? Register.hart_state = some (.HART_ACTIVE ())
  elp : t.regs.get? Register.elp = some 0#1
  mstatus : ∃ m, t.regs.get? Register.mstatus = some m ∧ _get_Mstatus_MIE m = 0
  misa : ∃ m, t.regs.get? Register.misa = some m
  mideleg : ∃ v, t.regs.get? Register.mideleg = some v
  mip : ∃ v, t.regs.get? Register.mip = some v
  mie : ∃ v, t.regs.get? Register.mie = some v
  sig_meip : ∃ v, t.regs.get? Register.sig_meip = some v
  sig_seip : ∃ v, t.regs.get? Register.sig_seip = some v
  mcountinhibit : ∃ v, t.regs.get? Register.mcountinhibit = some v
  minstretcfg : ∃ v, t.regs.get? Register.minstretcfg = some v
  minstret : ∃ v, t.regs.get? Register.minstret = some v

theorem runSail_currentlyEnabled_S {t : SailState} (h : SailStepInv t) :
    ∃ b, runSail (currentlyEnabled .Ext_S) t = some (b, t) := by
  obtain ⟨m, hm⟩ := h.misa
  rw [currentlyEnabled]
  rw [runSail_bind_of_eq (runSail_readReg hm)]
  rw [runSail_bind_of_eq (show runSail (currentlyEnabled .Ext_Zicsr) t = some (true, t) by
    rw [currentlyEnabled]; simp [hartSupports])]
  exact ⟨_, rfl⟩

theorem runSail_read_mip {t : SailState} (h : SailStepInv t) :
    ∃ v, runSail (read_mip .IncludePlatformInterrupts) t = some (v, t) := by
  obtain ⟨a, ha⟩ := h.mip
  obtain ⟨b, hb⟩ := h.sig_meip
  obtain ⟨c, hc⟩ := h.sig_seip
  obtain ⟨s, hs⟩ := runSail_currentlyEnabled_S h
  unfold read_mip external_interrupts_pending
  simp only [bind_assoc, pure_bind]
  rw [runSail_bind_of_eq (runSail_readReg ha), runSail_bind_of_eq (runSail_readReg hb),
    runSail_bind_of_eq hs]
  cases s
  · exact ⟨_, rfl⟩
  · simp only [if_true, bind_assoc]
    rw [runSail_bind_of_eq (runSail_readReg hc)]
    exact ⟨_, rfl⟩

theorem runSail_dispatchInterrupt {t : SailState} (h : SailStepInv t) :
    runSail (dispatchInterrupt .Machine) t = some (none, t) := by
  obtain ⟨m, hm, hMIE⟩ := h.mstatus
  obtain ⟨d, hd⟩ := h.mideleg
  obtain ⟨e, he⟩ := h.mie
  obtain ⟨s, hs⟩ := runSail_currentlyEnabled_S h
  obtain ⟨v, hv⟩ := runSail_read_mip h
  unfold dispatchInterrupt getPendingSet
  simp only [bind_assoc]
  rw [runSail_bind_of_eq hs]
  have hmach : (Privilege.Machine == Privilege.Machine) = true := rfl
  have hms : (Privilege.Machine == Privilege.Supervisor) = false := rfl
  have hmu : (Privilege.Machine == Privilege.User) = false := rfl
  cases s <;> simp only [if_true, Bool.false_eq_true, if_false, bind_assoc, pure_bind] <;>
    (try rw [runSail_bind_of_eq (runSail_readReg hd)]) <;>
    rw [runSail_bind_of_eq hv, runSail_bind_of_eq (runSail_readReg he),
      runSail_bind_of_eq (runSail_readReg he), runSail_bind_of_eq (runSail_readReg hm),
      runSail_bind_of_eq (runSail_readReg hm)] <;>
    simp [hMIE, hmach, hms, hmu] <;> rfl

end FlapjackRiscvCheck
