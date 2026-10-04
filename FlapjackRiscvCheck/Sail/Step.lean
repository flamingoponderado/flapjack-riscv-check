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

theorem runSail_is_landing_pad_expected {t : SailState} (h : SailStepInv t) :
    runSail (is_landing_pad_expected ()) t = some (false, t) := by
  unfold is_landing_pad_expected
  rw [runSail_bind_of_eq (runSail_readReg h.elp)]
  rfl

/-- `run_hart_active` for a 32-bit instruction that decodes to `si` and retires. -/
theorem runSail_run_hart_active {t t2 : SailState} (h : SailStepInv t) (n : Nat)
    (hcur : t.regs.get? Register.cur_privilege = some .Machine)
    {pc : BitVec 64} (hpc : t.regs.get? Register.PC = some pc)
    {w : BitVec 32} (hfetch : runSail (fetch ()) t = some (.F_Base w, t))
    {si : instruction} (hdec : runSail (ext_decode w) t = some (si, t))
    (hexec : runSail (execute si) { t with regs := t.regs.insert Register.nextPC (pc + 4) } =
      some (RETIRE_SUCCESS, t2)) :
    runSail (run_hart_active n) t =
      some (.Step_Execute (RETIRE_SUCCESS, zero_extend (m := 32) w), t2) := by
  unfold run_hart_active
  rw [SailME.run, runSail_SailME_run]
  simp only [bind_assoc, ExceptT_run_lift_bind]
  rw [runSail_bind_of_eq (runSail_readReg hcur), runSail_bind_of_eq (runSail_dispatchInterrupt h)]
  simp only [pure_bind, ExceptT_run_lift_bind, ext_fetch_hook]
  rw [runSail_bind_of_eq hfetch]
  simp only [ExceptT_run_lift_bind, bind_assoc]
  rw [runSail_bind_of_eq hdec]
  simp only [get_config_print_instr, Bool.false_eq_true, if_false, ExceptT_run_lift_bind, bind_assoc,
    pure_bind]
  rw [runSail_bind_of_eq (runSail_is_landing_pad_expected h)]
  simp only [Bool.false_and, Bool.false_eq_true, if_false, ExceptT_run_lift_bind, bind_assoc]
  rw [runSail_bind_of_eq (runSail_readReg hpc)]
  have h4 : Sail.BitVec.addInt pc 4 = pc + 4 := by simp [Sail.BitVec.addInt]
  rw [h4, runSail_bind_of_eq (runSail_writeReg _ _), runSail_bind_of_eq hexec]
  rfl

theorem runSail_should_inc_minstret {t : SailState} (h : SailStepInv t) :
    ∃ b, runSail (should_inc_minstret .Machine) t = some (b, t) := by
  obtain ⟨a, ha⟩ := h.mcountinhibit
  obtain ⟨c, hc⟩ := h.minstretcfg
  unfold should_inc_minstret
  rw [runSail_bind_of_eq (runSail_readReg ha), runSail_bind_of_eq (runSail_readReg hc)]
  exact ⟨_, rfl⟩

/-- The state after `tick_pc` and the `minstret` update that follow a retired instruction. -/
def sailCommit (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64) : SailState :=
  let t3 := { t2 with regs := t2.regs.insert Register.PC npc }
  if inc then { t3 with regs := t3.regs.insert Register.minstret (Sail.BitVec.addInt m 1) } else t3

/-- `try_step` when `run_hart_active` retires an instruction. -/
theorem runSail_try_step {t t2 : SailState} (h : SailStepInv t) (n : Nat)
    (hcur : t.regs.get? Register.cur_privilege = some .Machine) {inc : Bool}
    (hinc : runSail (should_inc_minstret .Machine) t = some (inc, t)) {ib : BitVec 32}
    (hrun : runSail (run_hart_active n)
      { t with regs := t.regs.insert Register.minstret_increment inc } =
        some (.Step_Execute (RETIRE_SUCCESS, ib), t2))
    (hact : t2.regs.get? Register.hart_state = some (.HART_ACTIVE ()))
    {npc : BitVec 64} (hnpc : t2.regs.get? Register.nextPC = some npc)
    (hmi : t2.regs.get? Register.minstret_increment = some inc)
    {m : BitVec 64} (hm : t2.regs.get? Register.minstret = some m) :
    runSail (try_step n false) t = some (false, sailCommit t2 npc inc m) := by
  unfold try_step
  simp only [bind_assoc]
  rw [runSail_bind_of_eq (runSail_readReg hcur), runSail_bind_of_eq hinc,
    runSail_bind_of_eq (runSail_writeReg _ _)]
  have hact0 : ({ t with regs := t.regs.insert Register.minstret_increment inc } : SailState).regs.get?
      Register.hart_state = some (.HART_ACTIVE ()) := by
    simp [Std.ExtDHashMap.get?_insert]; exact h.active
  rw [runSail_bind_of_eq (runSail_readReg hact0)]
  simp only []
  rw [runSail_bind_of_eq hrun]
  simp only [RETIRE_SUCCESS, hart_is_active, bind_assoc]
  rw [runSail_bind_of_eq (runSail_readReg hact)]
  rw [runSail_bind_of_eq (runSail_assert_true _ t2), runSail_bind_of_eq (runSail_readReg hact)]
  simp only []
  unfold tick_pc
  simp only [bind_assoc]
  rw [runSail_bind_of_eq (runSail_readReg hnpc), runSail_bind_of_eq (runSail_writeReg _ _)]
  have hpc3 : ({ t2 with regs := t2.regs.insert Register.PC npc } : SailState).regs.get? Register.PC =
      some npc := by simp [Std.ExtDHashMap.get?_insert]
  have hmi3 : ({ t2 with regs := t2.regs.insert Register.PC npc } : SailState).regs.get?
      Register.minstret_increment = some inc := by simp [Std.ExtDHashMap.get?_insert]; exact hmi
  have hm3 : ({ t2 with regs := t2.regs.insert Register.PC npc } : SailState).regs.get?
      Register.minstret = some m := by simp [Std.ExtDHashMap.get?_insert]; exact hm
  rw [runSail_bind_of_eq (runSail_readReg hpc3)]
  simp only [pure_bind]
  rw [runSail_bind_of_eq (runSail_readReg hmi3)]
  cases inc
  · simp [get_config_rvfi, sailCommit]
  · simp only [Bool.true_and, if_true, bind_assoc]
    rw [runSail_bind_of_eq (runSail_readReg hm3), runSail_bind_of_eq (runSail_writeReg _ _)]
    simp [get_config_rvfi, sailCommit]

end FlapjackRiscvCheck
