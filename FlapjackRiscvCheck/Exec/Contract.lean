import FlapjackRiscvCheck.Relation
import FlapjackRiscvCheck.Sail.RegsOther
import FlapjackRiscvCheck.L3.Control
import LeanRV64D.InstsEnd

/-!
# The execute-level contract

Every per-instruction lemma has the shape

  `ExecPre s t → ∃ t', runSail (execute_X ...) t = some (RETIRE_SUCCESS, t') ∧ ExecPost s s' t t'`

where `s'` is L3's `Run` result. `ExecPre` is what holds between Sail's
`set_next_pc (PC + 4)` and `execute` in `try_step`, matched with L3 after
`Fetch` of a 4-byte instruction. `ExecPost` relates the results: registers,
the next PC (Sail `nextPC` against L3 `l3NextPC`), a frame condition on the
Sail registers the instruction may not touch, and preservation of `MemRel`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

structure ExecPre (s : L3State) (t : SailState) : Prop where
  rel : RegRel s t
  nextFetch : NextFetch s = none
  skip : Skip s = 4
  nextPC : t.regs.get? Register.nextPC = some (PC s + 4)
  rv64 : (MCSR s).mcpuid.ArchBase = 2
  bareVM : (s.c_MCSR s.procID).mstatus.VM = 0#5
  pcEven : (PC s).getLsbD 0 = false
  misaC : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_C m = 1
  misaM : ∃ m, t.regs.get? Register.misa = some m ∧ _get_Misa_M m = 1
  machine : t.regs.get? Register.cur_privilege = some .Machine
  noLandingPads : ∃ c, t.regs.get? Register.mseccfg = some c ∧ _get_Seccfg_MLPE c = 0

/-- Sail registers other than `x1..x31` and `nextPC` are unchanged. -/
def SailRegFrame (t t' : SailState) : Prop :=
  ∀ r, Register.isGpr r = false → r ≠ Register.nextPC → t'.regs.get? r = t.regs.get? r

/-- On the address domain `D`, Sail's partial memory holds exactly L3's `MEM8`. -/
structure MemRel (s : L3State) (t : SailState) (D : BitVec 64 → Prop) : Prop where
  agree : ∀ a, D a → t.mem.get? a.toNat = some (s.MEM8 a)

/-- Memory unchanged on both sides preserves `MemRel`. -/
theorem MemRel.of_eq {s s' t t' D} (h : MemRel s t D) (hs : s'.MEM8 = s.MEM8)
    (ht : t'.mem = t.mem) : MemRel s' t' D :=
  ⟨fun a ha => by rw [hs, ht]; exact h.agree a ha⟩

/-- The L3 fields a tier-1 `Run` leaves unchanged. -/
structure L3Frame (s s' : L3State) : Prop where
  exception : s'.exception = s.exception
  mcsr : s'.c_MCSR = s.c_MCSR
  procID : s'.procID = s.procID
  skip : s'.c_Skip = s.c_Skip
  pc : s'.c_PC = s.c_PC

theorem L3Frame.ofWrite (s : L3State) (n : BitVec 5) (v : BitVec 64) :
    L3Frame s («write'GPR» (v, n) s) := by
  simp only [«write'GPR», «write'gpr»]
  by_cases h : n = 0#5 <;> simp [h] <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem L3Frame.ofBranchTo (s : L3State) (a : BitVec 64) : L3Frame s (branchTo a s) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem L3Frame.trans {s₁ s₂ s₃ : L3State} (h₁ : L3Frame s₁ s₂) (h₂ : L3Frame s₂ s₃) :
    L3Frame s₁ s₃ :=
  ⟨h₂.exception.trans h₁.exception, h₂.mcsr.trans h₁.mcsr, h₂.procID.trans h₁.procID,
    h₂.skip.trans h₁.skip, h₂.pc.trans h₁.pc⟩

structure ExecPost (s s' : L3State) (t t' : SailState) : Prop where
  rel : RegRel s' t'
  nextPC : t'.regs.get? Register.nextPC = l3NextPC s'
  frame : SailRegFrame t t'
  mem : ∀ D, MemRel s t D → MemRel s' t' D
  l3frame : L3Frame s s'

theorem ExecPre.l3NextPC {s t} (h : ExecPre s t) : l3NextPC s = some (PC s + 4) := by
  simp [FlapjackRiscvCheck.l3NextPC, h.nextFetch, h.skip]

/-- An instruction that only writes `v` to `rd` on both sides meets the contract. -/
theorem ExecPost.of_write {s t} (h : ExecPre s t) (rd : BitVec 5) (v : BitVec 64) :
    ExecPost s («write'GPR» (v, rd) s) t (sailSetGpr t rd v) where
  rel := h.rel.write rd v
  nextPC := by
    rw [sailSetGpr_get?_of_not_gpr _ _ _ rfl, l3NextPC_write'GPR, h.l3NextPC, h.nextPC]
  frame _ hr _ := sailSetGpr_get?_of_not_gpr _ _ _ hr
  mem _ hm := hm.of_eq (l3_MEM8_write'GPR s rd v) (sailSetGpr_mem _ _ _)
  l3frame := L3Frame.ofWrite s rd v

end FlapjackRiscvCheck
