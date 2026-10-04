import FlapjackRiscvCheck.Sail.Monad
import FlapjackRiscvCheck.Sail.Regs
import LeanRV64D.VmemUtils

/-!
# The Sail-side memory invariant and machine-mode address handling

`SailMemInv t` pins the configuration under which a data access in Sail is a
plain physical RAM access:

* machine mode with `mstatus.MPRV = 0`, so the effective privilege is Machine
  and translation is `Bare`;
* `mseccfg.PMM = 0`, so pointer masking is off.

The PMP and PMA conditions are added in `Sail/Mem/Phys.lean`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

structure SailMemInv (t : SailState) : Prop where
  machine : t.regs.get? Register.cur_privilege = some .Machine
  mstatus : ∃ m, t.regs.get? Register.mstatus = some m ∧ _get_Mstatus_MPRV m = 0
  mseccfg : ∃ c, t.regs.get? Register.mseccfg = some c ∧ _get_Seccfg_PMM c = 0

/-- The simp set that evaluates small register-reading Sail computations. -/
macro "sail_eval" : tactic =>
  `(tactic| simp [runSail, EStateM.run, EStateM.bind, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get, EStateM.get,
    bind, pure, *])

theorem effectivePrivilege_machine {m : BitVec 64} (hm : _get_Mstatus_MPRV m = 0)
    (acc : MemoryAccessType mem_payload) (t : SailState) :
    runSail (effectivePrivilege acc m .Machine) t = some (.Machine, t) := by
  unfold effectivePrivilege
  rw [hm]
  simp

theorem runSail_readReg_mstatus_priv {t : SailState} (h : SailMemInv t)
    (acc : MemoryAccessType mem_payload) {β : Type} (k : Privilege → SailM β) :
    runSail (do
      let p ← effectivePrivilege acc (← readReg Register.mstatus)
        (← readReg Register.cur_privilege)
      k p) t = runSail (k .Machine) t := by
  obtain ⟨m, hm, hp⟩ := h.mstatus
  rw [runSail_bind_of_eq (runSail_readReg hm), runSail_bind_of_eq (runSail_readReg h.machine),
    runSail_bind_of_eq (effectivePrivilege_machine hp acc t)]

theorem runSail_translationMode_machine (t : SailState) :
    runSail (translationMode .Machine) t = some (.Bare, t) := by
  unfold translationMode; rfl

theorem runSail_get_pmlen {t : SailState} (h : SailMemInv t)
    (acc : MemoryAccessType mem_payload) :
    runSail (get_pmlen acc .Machine) t = some (0, t) := by
  obtain ⟨c, hc, hpmm⟩ := h.mseccfg
  obtain ⟨m, hm, _⟩ := h.mstatus
  obtain ⟨b, hb⟩ : ∃ b, runSail (is_pmm_applicable acc .Machine) t = some (b, t) :=
    ⟨_, by unfold is_pmm_applicable; rw [runSail_bind_of_eq (runSail_readReg hm)]; rfl⟩
  unfold get_pmlen
  rw [runSail_bind_of_eq hb]
  cases b
  · rfl
  · simp only [if_true]
    unfold get_pmm
    simp only [bind_assoc]
    rw [runSail_bind_of_eq (runSail_readReg hc)]
    simp only [hpmm, pure_bind]
    rfl

end FlapjackRiscvCheck
