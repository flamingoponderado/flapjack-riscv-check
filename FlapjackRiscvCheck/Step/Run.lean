import FlapjackRiscvCheck.Step.Sim

/-!
# Runs: iterating the step simulation

`l3Run k s` runs `NextRISCV` `k` times; `sailRun k` runs Sail's `try_step`
`k` times. `GoodRun t₀ D k s` says that every L3 state reached in the first
`k` steps satisfies the per-step side conditions (tier-1 hint-free code at
`PC`, fetchable and with plain RAM accesses), checked against the initial
Sail state `t₀`: the platform registers they read never change.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step

/-- `k` L3 steps. -/
noncomputable def l3Run : Nat → L3State → Option L3State
  | 0, s => some s
  | k + 1, s => (NextRISCV s).bind (l3Run k)

/-- `k` Sail steps (the step number only labels trace output). -/
noncomputable def sailRun : Nat → SailM Unit
  | 0 => pure ()
  | k + 1 => do let _ ← try_step k false; sailRun k

/-- The per-step side conditions hold along the first `k` steps of the L3 run from `s`. -/
def GoodRun (t₀ : SailState) (D : BitVec 64 → Prop) : Nat → L3State → Prop
  | 0, _ => True
  | k + 1, s => (∃ i, StepSide s t₀ D i) ∧ ∀ s', NextRISCV s = some s' → GoodRun t₀ D k s'

theorem StepSide.transfer {s t t' D i} (h : StepSide s t D i) (ha : RegsAgree t t') :
    StepSide s t' D i where
  tier1 := h.tier1
  hintFree := h.hintFree
  code := h.code
  codeD := h.codeD
  fetchPma := h.fetchPma.transfer ha
  fetchMmio := h.fetchMmio.transfer ha
  pcAligned := h.pcAligned
  memSide := h.memSide.transfer (fun _ => rfl) ha

/-- **Run simulation.** From related states, along an L3 run whose steps meet the side
conditions, Sail's `try_step` loop runs in lockstep and the states stay related. -/
theorem run_sim {t₀ : SailState} {D : BitVec 64 → Prop} :
    ∀ (k : Nat) (s : L3State) (t : SailState), StepRel s t D → RegsAgree t₀ t →
      GoodRun t₀ D k s →
      ∃ s' t', l3Run k s = some s' ∧ runSail (sailRun k) t = some ((), t') ∧
        StepRel s' t' D ∧ RegsAgree t₀ t'
  | 0, s, t, h, ha, _ => ⟨s, t, rfl, rfl, h, ha⟩
  | k + 1, s, t, h, ha, ⟨⟨i, hside⟩, hrest⟩ => by
    obtain ⟨s₁, t₁, hn, hst, h₁, ha₁⟩ := step_sim h (hside.transfer ha) k
    obtain ⟨s', t', hr, hsr, h', ha'⟩ := run_sim k s₁ t₁ h₁ (ha.trans ha₁) (hrest s₁ hn)
    refine ⟨s', t', ?_, ?_, h', ha'⟩
    · simp [l3Run, hn, hr]
    · simp only [sailRun, bind_assoc]
      rw [runSail_bind_of_eq hst]
      exact hsr

end FlapjackRiscvCheck
