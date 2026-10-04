import FlapjackRiscvCheck.Step.Frame
import FlapjackRiscvCheck.Decode.Dispatch
import FlapjackRiscvCheck.L3.Step

/-!
# One step: L3 `NextRISCV` against Sail `try_step`

`StepRel s t D` is the relation kept across steps. `StepSide s t D i` collects
the conditions of one particular step: the word at `PC` is the encoding of the
tier-1 instruction `i` (and is fetchable in Sail), and a load/store makes a
plain RAM access.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step

structure StepRel (s : L3State) (t : SailState) (D : BitVec 64 → Prop) : Prop where
  rel : RegRel s t
  mem : MemRel s t D
  nextFetch : NextFetch s = none
  noExc : s.exception = .NoException
  rv64 : (MCSR s).mcpuid.ArchBase = 2
  bareVM : (s.c_MCSR s.procID).mstatus.VM = 0#5
  misaC : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_C m = 1
  misaM : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_M m = 1
  machine : t.regs.get? Register.cur_privilege = some .Machine
  noLandingPads : ∃ c, t.regs.get? Register.mseccfg = some c ∧ _get_Seccfg_MLPE c = 0
  memInv : SailMemInv t
  pmp : PmpOff t
  stepInv : SailStepInv t

structure StepSide (s : L3State) (t : SailState) (D : BitVec 64 → Prop)
    (i : Flapjack.RiscV.L3.instruction) : Prop where
  tier1 : (toSail i).isSome
  hintFree : HintFree i
  code : ∀ k < 4, s.MEM8 (PC s + BitVec.ofNat 64 k) = wordByte (Encode i) k
  codeD : ∀ k < 4, D (PC s + BitVec.ofNat 64 k)
  fetchPma : PmaExecOK t (PC s) 4
  fetchMmio : MmioFree t (PC s) 4
  pcAligned : (PC s).toNat % 4 = 0
  memSide : MemSide s t D i

theorem leNat_wordByte (w : BitVec 32) : leNat (fun k => wordByte w k) 4 = w.toNat := by
  have := w.isLt
  simp only [leNat, wordByte, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

theorem isRVC_false {w : BitVec 32} (h : w.toNat % 4 = 3) :
    isRVC (Sail.BitVec.extractLsb w 15 0) = false := by
  have : Sail.BitVec.extractLsb (Sail.BitVec.extractLsb w 15 0) 1 0 = 3#2 := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat]
    omega
  simp [isRVC, this, Functions.not]

theorem MemSide.transfer {s s1 : L3State} {t t1 : SailState} {D} {i}
    (h : MemSide s t D i) (hgpr : ∀ n, GPR n s1 = GPR n s) (ha : RegsAgree t t1) :
    MemSide s1 t1 D i := by
  have hea : ∀ rs1 imm, l3EA s1 rs1 imm = l3EA s rs1 imm := fun rs1 imm => by simp [l3EA, hgpr]
  revert h
  unfold MemSide
  split <;> intro h <;> simp only [hea] <;>
    first
    | exact ⟨h.1.transfer ha, h.2⟩
    | exact h.transfer ha
    | trivial

theorem sailGpr_insert_of_not_gpr (t : SailState) {r : Register} (hr : Register.isGpr r = false)
    (v : RegisterType r) (n : BitVec 5) :
    sailGpr { t with regs := t.regs.insert r v } n = sailGpr t n := by
  have hn := n.isLt
  generalize hk : n.toNat = k at hn
  obtain rfl : n = BitVec.ofNat 5 k := by rw [← hk]; simp
  interval_cases k <;> simp [sailGpr, Std.ExtDHashMap.get?_insert] <;>
    (intro e; subst e; simp [Register.isGpr] at hr)

theorem leNat_congr {f g : Nat → BitVec 8} :
    ∀ n, (∀ k < n, f k = g k) → leNat f n = leNat g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [leNat]
    rw [h 0 (by omega), leNat_congr n (fun k hk => h (k + 1) (by omega))]

@[simp] theorem l3_GPR_write'PC (s : riscv_state) (v : BitVec 64) (n : BitVec 5) :
    GPR n («write'PC» v s) = GPR n s := by
  simp [«write'PC», GPR, gpr]

@[simp] theorem l3_GPR_write'NextFetch (s : riscv_state) (v) (n : BitVec 5) :
    GPR n («write'NextFetch» v s) = GPR n s := by
  simp [«write'NextFetch», GPR, gpr]

@[simp] theorem l3_PC_write'PC (s : riscv_state) (v : BitVec 64) : PC («write'PC» v s) = v := by
  simp [«write'PC», PC, holUpdate]

@[simp] theorem l3_NextFetch_write'PC_none (s : riscv_state) (v : BitVec 64) :
    NextFetch («write'PC» v («write'NextFetch» none s)) = none := by
  simp [«write'PC», «write'NextFetch», NextFetch, holUpdate]

theorem sailCommit_agree (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64) :
    RegsAgree t2 (sailCommit t2 npc inc m) := by
  unfold sailCommit
  have h1 := RegsAgree.insert (r := .PC) t2 rfl npc
  cases inc
  · exact h1
  · exact h1.trans (RegsAgree.insert (r := .minstret) _ rfl _)

theorem sailCommit_gpr (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64) (n : BitVec 5) :
    sailGpr (sailCommit t2 npc inc m) n = sailGpr t2 n := by
  cases inc
  · exact sailGpr_insert_of_not_gpr (r := .PC) t2 rfl npc n
  · exact (sailGpr_insert_of_not_gpr (r := .minstret)
      ({ t2 with regs := t2.regs.insert Register.PC npc } : SailState) rfl _ n).trans
      (sailGpr_insert_of_not_gpr (r := .PC) t2 rfl npc n)

theorem sailCommit_pc (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64) :
    (sailCommit t2 npc inc m).regs.get? Register.PC = some npc := by
  unfold sailCommit; cases inc <;> simp [Std.ExtDHashMap.get?_insert]

theorem sailCommit_minstret (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64)
    (hm : t2.regs.get? Register.minstret = some m) :
    ∃ v, (sailCommit t2 npc inc m).regs.get? Register.minstret = some v := by
  unfold sailCommit; cases inc <;> simp [Std.ExtDHashMap.get?_insert, hm]

theorem sailCommit_mem (t2 : SailState) (npc : BitVec 64) (inc : Bool) (m : BitVec 64) :
    (sailCommit t2 npc inc m).mem = t2.mem := by
  unfold sailCommit; cases inc <;> rfl

/-- One step of both models from related states. -/
theorem step_sim {s t D i} (h : StepRel s t D) (hs : StepSide s t D i) (n : Nat) :
    ∃ s' t', NextRISCV s = some s' ∧ runSail (try_step n false) t = some (false, t') ∧
      StepRel s' t' D := by
  obtain ⟨si, hsi⟩ := Option.isSome_iff_exists.mp hs.tier1
  have hlow := encode_low_bits i si hsi
  generalize hw : Encode i = w at hlow
  have low0 : w.getLsbD 0 = true := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
  have low1 : w.getLsbD 1 = true := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; simp; omega
  have hcode : ∀ k < 4, s.MEM8 (PC s + BitVec.ofNat 64 k) = wordByte w k := hw ▸ hs.code
  have hfetchL3 := l3_fetch_word s w h.bareVM low0 low1 hcode
  -- the Sail states before `execute`
  obtain ⟨inc, hinc⟩ := runSail_should_inc_minstret h.stepInv
  generalize ht0 : ({ t with regs := t.regs.insert Register.minstret_increment inc } : SailState) = t0
  generalize ht1 : ({ t0 with regs := t0.regs.insert Register.nextPC (PC s + 4) } : SailState) = t1
  have ha0 : RegsAgree t t0 := ht0 ▸ RegsAgree.insert (r := .minstret_increment) t rfl inc
  have ha01 : RegsAgree t0 t1 := ht1 ▸ RegsAgree.insert (r := .nextPC) t0 rfl _
  have ha1 : RegsAgree t t1 := ha0.trans ha01
  have hgpr0 : ∀ n, sailGpr t0 n = sailGpr t n := fun n =>
    ht0 ▸ sailGpr_insert_of_not_gpr (r := .minstret_increment) t rfl _ n
  have hgpr1 : ∀ n, sailGpr t1 n = sailGpr t n := fun n =>
    (ht1 ▸ sailGpr_insert_of_not_gpr (r := .nextPC) t0 rfl _ n).trans (hgpr0 n)
  have hpc0 : t0.regs.get? Register.PC = some (PC s) := by
    subst ht0; simp [Std.ExtDHashMap.get?_insert]; exact h.rel.pc
  have hpc1 : t1.regs.get? Register.PC = some (PC s) := by
    subst ht1; simp [Std.ExtDHashMap.get?_insert]; exact hpc0
  have hmem0 : t0.mem = t.mem := by subst ht0; rfl
  have hmem1 : t1.mem = t.mem := by subst ht1; rw [← hmem0]
  -- the L3 state after fetch
  generalize hs1 : ({ s with c_Skip := holUpdate s.procID 4 s.c_Skip } : riscv_state) = s1
  rw [hs1] at hfetchL3
  have hG1 : ∀ n, GPR n s1 = GPR n s := fun n => by subst hs1; rfl
  have hPC1 : PC s1 = PC s := by subst hs1; rfl
  have hMEM1 : s1.MEM8 = s.MEM8 := by subst hs1; rfl
  have hpre : ExecPre s1 t1 := {
    rel := ⟨fun n => by rw [hgpr1, hG1]; exact h.rel.gpr n, by rw [hPC1]; exact hpc1⟩
    nextFetch := by subst hs1; exact h.nextFetch
    skip := by subst hs1; simp [Skip, holUpdate]
    nextPC := by subst ht1; simp [Std.ExtDHashMap.get?_insert, hPC1]
    rv64 := by subst hs1; exact h.rv64
    bareVM := by subst hs1; exact h.bareVM
    pcEven := by
      rw [hPC1, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]; have := hs.pcAligned; simp; omega
    misaC := by rw [ha1 _ rfl]; exact h.misaC
    misaM := by rw [ha1 _ rfl]; exact h.misaM
    machine := by rw [ha1 _ rfl]; exact h.machine
    noLandingPads := by rw [ha1 _ rfl]; exact h.noLandingPads }
  have hm1 : MemRel s1 t1 D := h.mem.of_eq hMEM1 hmem1
  have hside1 : MemSide s1 t1 D i := hs.memSide.transfer hG1 ha1
  obtain ⟨t2, hexec, hpost⟩ := exec_sim hpre hm1 i si hsi hside1
  -- Sail fetch and decode in `t0`
  have hfok : SailFetchOK t0 (PC s) :=
    { mem := h.memInv.transfer ha0, pmp := h.pmp.transfer ha0,
      pma := hs.fetchPma.transfer ha0, mmio := hs.fetchMmio.transfer ha0, aligned := hs.pcAligned }
  obtain ⟨v, hv, hrb⟩ := runSail_readBytes 4 (PC s).toNat (fun k => wordByte w k) t0 (fun k hk => by
    rw [hmem0, ← toNat_add_small (w := 4) (by decide) hs.pcAligned hk, ← hcode k hk]
    exact h.mem.agree _ (hs.codeD k hk))
  have hvw : v = w := BitVec.eq_of_toNat_eq (by rw [hv, leNat_wordByte])
  subst hvw
  obtain ⟨m, hm, hC⟩ := h.misaC
  have hfetch := runSail_fetch hfok hpc0 (by rw [ha0 _ rfl]; exact hm) hC (runSail_read_ram hrb)
    (isRVC_false hlow)
  have hdinv : DecodeInv t0 :=
    ⟨by rw [ha0 _ rfl]; exact h.machine, by rw [ha0 _ rfl]; exact h.noLandingPads,
      by rw [ha0 _ rfl]; exact h.misaM⟩
  have hdec := sail_decode_sim hdinv i si hsi hs.hintFree
  rw [hw] at hdec
  obtain ⟨mi, hmi⟩ := h.stepInv.minstret
  have hinv0 : SailStepInv t0 := h.stepInv.transfer ha0 ⟨mi, by rw [← ht0]; simp [Std.ExtDHashMap.get?_insert]; exact hmi⟩
  have hrun := runSail_run_hart_active hinv0 n (by rw [ha0 _ rfl]; exact h.machine) hpc0 hfetch hdec
    (ht1 ▸ hexec)
  -- Sail registers after `execute`
  have ha12 : RegsAgree t1 t2 := RegsAgree.ofFrame hpost.frame
  have ha2 : RegsAgree t t2 := ha1.trans ha12
  obtain ⟨npc, hnpcL3⟩ := hpost.npc
  have hnpc : t2.regs.get? Register.nextPC = some npc := hpost.nextPC.trans hnpcL3
  have hmi2 : t2.regs.get? Register.minstret_increment = some inc := by
    rw [hpost.frame _ rfl (by decide), ← ht1]
    simp [Std.ExtDHashMap.get?_insert, ← ht0]
  have hm2 : t2.regs.get? Register.minstret = some mi := by
    rw [hpost.frame _ rfl (by decide), ← ht1, ← ht0]
    simp [Std.ExtDHashMap.get?_insert]; exact hmi
  have htry := runSail_try_step h.stepInv n h.machine hinc (ht0 ▸ hrun)
    (by rw [ha2 _ rfl]; exact h.stepInv.active) hnpc hmi2 hm2
  -- L3
  have hexc : (Run i s1).exception = .NoException := by
    rw [hpost.l3frame.exception]; subst hs1; exact h.noExc
  have hnext := l3_next s s1 (Run i s1) _ i npc hfetchL3
    (by rw [← hw]; exact l3_decode_sim i si hsi) rfl hexc hnpcL3
  refine ⟨_, _, hnext, htry, ?_⟩
  have ha3 : RegsAgree t (sailCommit t2 npc inc mi) := ha2.trans (sailCommit_agree _ _ _ _)
  have hmcsr : («write'PC» npc («write'NextFetch» none (Run i s1))).c_MCSR = s.c_MCSR := by
    simp only [«write'PC», «write'NextFetch»]; rw [hpost.l3frame.mcsr]; subst hs1; rfl
  have hpid : («write'PC» npc («write'NextFetch» none (Run i s1))).procID = s.procID := by
    simp only [«write'PC», «write'NextFetch»]; rw [hpost.l3frame.procID]; subst hs1; rfl
  exact {
    rel := ⟨fun n => by rw [sailCommit_gpr, l3_GPR_write'PC, l3_GPR_write'NextFetch]; exact hpost.rel.gpr n,
      by rw [sailCommit_pc, l3_PC_write'PC]⟩
    mem := by
      have := hpost.mem D hm1
      exact ⟨fun a ha => by
        rw [sailCommit_mem]
        exact (this.agree a ha).trans (by simp [«write'PC», «write'NextFetch»])⟩
    nextFetch := l3_NextFetch_write'PC_none _ _
    noExc := by simpa [«write'PC», «write'NextFetch»] using hexc
    rv64 := by simp only [MCSR, hmcsr, hpid]; exact h.rv64
    bareVM := by rw [hmcsr, hpid]; exact h.bareVM
    misaC := by rw [ha3 _ rfl]; exact h.misaC
    misaM := by rw [ha3 _ rfl]; exact h.misaM
    machine := by rw [ha3 _ rfl]; exact h.machine
    noLandingPads := by rw [ha3 _ rfl]; exact h.noLandingPads
    memInv := h.memInv.transfer ha3
    pmp := h.pmp.transfer ha3
    stepInv := h.stepInv.transfer ha3 (sailCommit_minstret _ _ _ _ hm2) }

end FlapjackRiscvCheck
