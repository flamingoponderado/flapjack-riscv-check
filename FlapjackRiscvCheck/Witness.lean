import FlapjackRiscvCheck.Step.Run

/-!
# Anti-vacuity: the step hypotheses are satisfiable

A concrete pair of states, an L3 machine and a Sail machine both about to execute
`ADDI x1, x0, 1` at `0x80000000` in a RAM region, satisfying `StepRel` and
`StepSide`. So `step_sim` and `run_sim` are not vacuous.
-/

namespace FlapjackRiscvCheck.Witness

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3 FlapjackRiscvCheck

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def pc0 : BitVec 64 := 0x80000000

def instr : Flapjack.RiscV.L3.instruction := .ArithI (.ADDI (1#5, 0#5, 1#12))

theorem encode_instr : Encode instr = 0x00100093#32 := by decide

def codeByte : BitVec 64 → BitVec 8 := fun a =>
  if a = pc0 then 0x93 else if a = pc0 + 1 then 0x00 else if a = pc0 + 2 then 0x10 else 0x00

def l3State : L3State :=
  { (default : riscv_state) with
    MEM8 := codeByte
    c_PC := fun _ => pc0
    c_gpr := fun _ _ => 0
    c_NextFetch := fun _ => none
    c_MCSR := fun _ => { (default : MachineCSR) with
      mcpuid := { (default : mcpuid) with ArchBase := 2 }
      mstatus := { (default : mstatus) with VM := 0 } }
    exception := .NoException
    procID := 0 }

def ram : PMA_Region :=
  { base := 0x80000000, size := 0x10000000, include_in_device_tree := true,
    attributes := { (default : PMA) with readable := true, writable := true, executable := true } }

def regs0 : Std.ExtDHashMap Register RegisterType :=
  (∅ : Std.ExtDHashMap Register RegisterType)
  |>.insert Register.x1 (0 : BitVec 64)
  |>.insert Register.x2 (0 : BitVec 64)
  |>.insert Register.x3 (0 : BitVec 64)
  |>.insert Register.x4 (0 : BitVec 64)
  |>.insert Register.x5 (0 : BitVec 64)
  |>.insert Register.x6 (0 : BitVec 64)
  |>.insert Register.x7 (0 : BitVec 64)
  |>.insert Register.x8 (0 : BitVec 64)
  |>.insert Register.x9 (0 : BitVec 64)
  |>.insert Register.x10 (0 : BitVec 64)
  |>.insert Register.x11 (0 : BitVec 64)
  |>.insert Register.x12 (0 : BitVec 64)
  |>.insert Register.x13 (0 : BitVec 64)
  |>.insert Register.x14 (0 : BitVec 64)
  |>.insert Register.x15 (0 : BitVec 64)
  |>.insert Register.x16 (0 : BitVec 64)
  |>.insert Register.x17 (0 : BitVec 64)
  |>.insert Register.x18 (0 : BitVec 64)
  |>.insert Register.x19 (0 : BitVec 64)
  |>.insert Register.x20 (0 : BitVec 64)
  |>.insert Register.x21 (0 : BitVec 64)
  |>.insert Register.x22 (0 : BitVec 64)
  |>.insert Register.x23 (0 : BitVec 64)
  |>.insert Register.x24 (0 : BitVec 64)
  |>.insert Register.x25 (0 : BitVec 64)
  |>.insert Register.x26 (0 : BitVec 64)
  |>.insert Register.x27 (0 : BitVec 64)
  |>.insert Register.x28 (0 : BitVec 64)
  |>.insert Register.x29 (0 : BitVec 64)
  |>.insert Register.x30 (0 : BitVec 64)
  |>.insert Register.x31 (0 : BitVec 64)
  |>.insert Register.PC pc0
  |>.insert Register.misa ((1 <<< 2 : BitVec 64) ||| (1 <<< 12 : BitVec 64))
  |>.insert Register.cur_privilege Privilege.Machine
  |>.insert Register.mstatus (0 : BitVec 64)
  |>.insert Register.mseccfg (0 : BitVec 64)
  |>.insert Register.pmpcfg_n (Vector.replicate 64 (0 : BitVec 8))
  |>.insert Register.pmpaddr_n (Vector.replicate 64 (0 : BitVec 64))
  |>.insert Register.pma_regions [ram]
  |>.insert Register.htif_tohost_base none
  |>.insert Register.hart_state (HartState.HART_ACTIVE ())
  |>.insert Register.elp (0 : BitVec 1)
  |>.insert Register.mideleg (0 : BitVec 64)
  |>.insert Register.mip (0 : BitVec 64)
  |>.insert Register.mie (0 : BitVec 64)
  |>.insert Register.sig_meip (0 : BitVec 1)
  |>.insert Register.sig_seip (0 : BitVec 1)
  |>.insert Register.mcountinhibit (0 : BitVec 32)
  |>.insert Register.minstretcfg (0 : BitVec 64)
  |>.insert Register.minstret (0 : BitVec 64)

def mem0 : Std.ExtHashMap Nat (BitVec 8) :=
  (∅ : Std.ExtHashMap Nat (BitVec 8))
  |>.insert pc0.toNat 0x93 |>.insert (pc0.toNat + 1) 0x00
  |>.insert (pc0.toNat + 2) 0x10 |>.insert (pc0.toNat + 3) 0x00

def sailState : SailState :=
  { (default : SailState) with regs := regs0, mem := mem0 }

def dom : BitVec 64 → Prop := fun a => a = pc0 ∨ a = pc0 + 1 ∨ a = pc0 + 2 ∨ a = pc0 + 3

theorem get_regs0 {r : Register} {v : RegisterType r} (h : regs0.get? r = some v) :
    sailState.regs.get? r = some v := h

macro "reg_val" : tactic => `(tactic| (apply get_regs0; simp [regs0, Std.ExtDHashMap.get?_insert]))

theorem gpr0 (n : BitVec 5) : sailGpr sailState n = some (GPR n l3State) := by
  have : GPR n l3State = 0 := by simp [GPR, gpr, l3State]
  rw [this]
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailGpr, sailState, regs0, Std.ExtDHashMap.get?_insert]

theorem stepRel : StepRel l3State sailState dom where
  rel := ⟨gpr0, by reg_val; rfl⟩
  mem := ⟨fun a ha => by
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp [sailState, mem0, codeByte, pc0, l3State, Std.ExtHashMap.get?_eq_getElem?,
        Std.ExtHashMap.getElem?_insert, Std.ExtHashMap.getElem_insert]⟩
  nextFetch := rfl
  noExc := rfl
  rv64 := rfl
  bareVM := rfl
  misaC := ⟨_, by reg_val; rfl, by decide⟩
  misaM := ⟨_, by reg_val; rfl, by decide⟩
  machine := by reg_val
  noLandingPads := ⟨_, by reg_val; rfl, by decide⟩
  memInv := ⟨by reg_val, ⟨_, by reg_val; rfl, by decide⟩, ⟨_, by reg_val; rfl, by decide⟩⟩
  pmp := ⟨⟨_, by reg_val; rfl, by intro c hc; simp at hc; subst hc; decide⟩, ⟨_, by reg_val; rfl⟩⟩
  stepInv := {
    active := by reg_val
    elp := by reg_val
    mstatus := ⟨_, by reg_val; rfl, by decide⟩
    misa := ⟨_, by reg_val; rfl⟩
    mideleg := ⟨_, by reg_val; rfl⟩
    mip := ⟨_, by reg_val; rfl⟩
    mie := ⟨_, by reg_val; rfl⟩
    sig_meip := ⟨_, by reg_val; rfl⟩
    sig_seip := ⟨_, by reg_val; rfl⟩
    mcountinhibit := ⟨_, by reg_val; rfl⟩
    minstretcfg := ⟨_, by reg_val; rfl⟩
    minstret := ⟨_, by reg_val; rfl⟩ }

theorem stepSide : StepSide l3State sailState dom instr where
  tier1 := rfl
  hintFree := trivial
  code := by
    intro k hk
    rw [encode_instr]
    interval_cases k <;> decide
  codeD := by
    intro k hk
    interval_cases k <;> simp [dom, PC, l3State]
  fetchPma := ⟨⟨[ram], ram, by reg_val, rfl, rfl⟩⟩
  fetchMmio := {
    clint := by decide
    sig := by decide
    htif := ⟨none, by reg_val, by simp⟩ }
  pcAligned := by decide
  memSide := trivial

/-- The hypotheses of `step_sim` are satisfiable. -/
theorem step_sim_nonvacuous : ∃ s t D i, StepRel s t D ∧ StepSide s t D i :=
  ⟨_, _, _, _, stepRel, stepSide⟩

theorem goodRun : GoodRun sailState dom 1 l3State := ⟨⟨instr, stepSide⟩, fun _ _ => trivial⟩

/-- On the witness, `run_sim` gives a concrete lockstep step: both models execute the `ADDI`
and end up related again. -/
theorem run_sim_nonvacuous :
    ∃ s' t', l3Run 1 l3State = some s' ∧ runSail (sailRun 1) sailState = some ((), t') ∧
      StepRel s' t' dom :=
  let ⟨s', t', h1, h2, h3, _⟩ := run_sim 1 l3State sailState stepRel (RegsAgree.refl _) goodRun
  ⟨s', t', h1, h2, h3⟩

end FlapjackRiscvCheck.Witness
