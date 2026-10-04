import FlapjackRiscvCheck.Sail.Mem.Inv
import FlapjackRiscvCheck.Sail.Loop
import LeanRV64D.PmpControl

/-!
# PMP with every entry OFF

If every `pmpcfg` entry has address-matching mode OFF, no entry matches, and a
machine-mode access passes `pmpCheck`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

structure PmpOff (t : SailState) : Prop where
  cfg : ∃ cfgs, t.regs.get? Register.pmpcfg_n = some cfgs ∧ ∀ c ∈ cfgs, _get_Pmpcfg_ent_A c = 0
  addr : ∃ addrs, t.regs.get? Register.pmpaddr_n = some addrs

theorem pmpA_getElem! {cfgs : Vector (BitVec 8) 64} (h : ∀ c ∈ cfgs, _get_Pmpcfg_ent_A c = 0)
    (n : Nat) : _get_Pmpcfg_ent_A cfgs[n]! = 0 := by
  by_cases hn : n < 64
  · rw [getElem!_pos cfgs n hn]; exact h _ (Vector.getElem_mem hn)
  · rw [getElem!_neg cfgs n hn]; rfl

theorem pmpA_getElem!_int {cfgs : Vector (BitVec 8) 64} (h : ∀ c ∈ cfgs, _get_Pmpcfg_ent_A c = 0)
    (i : Int) : _get_Pmpcfg_ent_A cfgs[i]! = 0 := by
  have : cfgs[i]! = cfgs[i.toNat]! := by simp only [getElem!_def]; rfl
  rw [this]
  exact pmpA_getElem! h i.toNat

theorem runSail_pmpReadAddrReg {t : SailState} (h : PmpOff t) (n : Nat) :
    ∃ v, runSail (pmpReadAddrReg n) t = some (v, t) := by
  obtain ⟨cfgs, hc, hA⟩ := h.cfg
  obtain ⟨addrs, ha⟩ := h.addr
  unfold pmpReadAddrReg
  simp only [bind_assoc, pure_bind]
  rw [runSail_bind_of_eq (runSail_readReg hc), runSail_bind_of_eq (runSail_readReg ha)]
  simp only [pmpA_getElem! hA, sys_pmp_grain]
  exact ⟨_, rfl⟩

theorem runSail_pmpMatchAddr_off {cfg : BitVec 8} (hA : _get_Pmpcfg_ent_A cfg = 0)
    (a : physaddr) (w pa ppa : BitVec 64) (t : SailState) :
    runSail (pmpMatchAddr a w cfg pa ppa) t = some (.PMP_NoMatch, t) := by
  unfold pmpMatchAddr
  simp only [hA]
  rfl

theorem runSail_pmpCheck_off {t : SailState} (h : PmpOff t) (a : physaddr) (w : Nat)
    (acc : MemoryAccessType mem_payload) :
    runSail (pmpCheck a w acc .Machine) t = some (none, t) := by
  obtain ⟨cfgs, hc, hA⟩ := h.cfg
  unfold pmpCheck
  rw [SailME.run, runSail_SailME_run]
  simp only [sys_pmp_count]
  rw [if_neg (by decide), runSail_ExceptT_bind, runSail_forIn_IntRange_noop _ _ t ?body]
  · rfl
  case body =>
    intro i _
    obtain ⟨p, hp⟩ := runSail_pmpReadAddrReg h (i - 1).toNat
    obtain ⟨q, hq⟩ := runSail_pmpReadAddrReg h i.toNat
    have hm := runSail_pmpMatchAddr_off (pmpA_getElem!_int hA i) a (to_bits w)
    split
    · simp only [ExceptT_run_lift_bind, ExceptT_run_lift]
      rw [runSail_bind_of_eq hp, runSail_bind_of_eq (runSail_readReg hc)]
      simp only [pure_bind, ExceptT.run_bind, ExceptT_run_lift]
      rw [runSail_bind_of_eq (runSail_map_ok hq), runSail_bind_of_eq (runSail_map_ok (hm _ _ t))]
      rfl
    · simp only [pure_bind, ExceptT_run_lift_bind, ExceptT_run_lift]
      rw [runSail_bind_of_eq (runSail_readReg hc), runSail_bind_of_eq hq,
        runSail_bind_of_eq (hm _ _ t)]
      rfl

end FlapjackRiscvCheck
