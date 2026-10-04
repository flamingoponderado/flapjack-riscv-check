import FlapjackRiscvCheck.L3.Load
import FlapjackRiscvCheck.L3.Control
import Flapjack.RiscV.L3.Step.StoreStep

/-!
# L3 stores as byte writes

From Flapjack's ported HOL step theorems (`dfnSD`, `dfnSW`, `dfnSH`, `dfnSB`):
a `w`-byte store at an aligned effective address `A` replaces the bytes at
`A, …, A + w - 1` with the low bytes of `x[rs2]` and changes nothing else.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step

/-- `MEM8` after storing the low `w` bytes of `v` at `A`. -/
def l3StoreMem (m : BitVec 64 → BitVec 8) (A : BitVec 64) (w : Nat) (v : BitVec 64) :
    BitVec 64 → BitVec 8 :=
  fun x => if A.toNat ≤ x.toNat ∧ x.toNat < A.toNat + w then v.extractLsb' (8 * (x.toNat - A.toNat)) 8
    else m x

theorem holWordExtract_byte (v : BitVec 64) (k : Nat) (hk : k < 8) :
    holWordExtract 8 (8 * k + 7) (8 * k) v = v.extractLsb' (8 * k) 8 := by
  apply BitVec.eq_of_toNat_eq
  have : min (8 * k + 7) 63 + 1 - 8 * k = 8 := by omega
  simp [holWordExtract, BitVec.extractLsb'_toNat, this]

theorem l3_rs2_val (s : riscv_state) (rs2 : BitVec 5) (hi lo : Nat) :
    (if rs2 = 0 then 0#8 else holWordExtract 8 hi lo (s.c_gpr s.procID rs2)) =
      holWordExtract 8 hi lo (GPR rs2 s) := by
  by_cases h : rs2 = 0
  · subst h; simp [GPR, holWordExtract]
  · have h' : ¬ rs2 = 0#5 := h
    simp [GPR, gpr, h, h']

theorem l3StoreMem_zero (m : BitVec 64 → BitVec 8) (A v : BitVec 64) : l3StoreMem m A 0 v = m := by
  funext x; simp only [l3StoreMem, Nat.add_zero]; rw [if_neg (by omega)]

theorem l3StoreMem_step (m : BitVec 64 → BitVec 8) (A v : BitVec 64) (k : Nat) (hk : k < 8)
    (hA : A.toNat + k < 2 ^ 64) :
    holUpdate (A + BitVec.ofNat 64 k) (holWordExtract 8 (8 * k + 7) (8 * k) v) (l3StoreMem m A k v) =
      l3StoreMem m A (k + 1) v := by
  funext x
  rw [holWordExtract_byte v k hk]
  simp only [holUpdate, l3StoreMem]
  have hAk : (A + BitVec.ofNat 64 k).toNat = A.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64),
      Nat.mod_eq_of_lt hA]
  by_cases hx : A + BitVec.ofNat 64 k = x
  · subst hx
    rw [if_pos rfl, hAk, if_pos (by omega)]
    congr 2; omega
  · rw [if_neg hx]
    have hx' : x.toNat ≠ A.toNat + k := by
      intro h; apply hx; apply BitVec.eq_of_toNat_eq; rw [hAk, h]
    by_cases hr : A.toNat ≤ x.toNat ∧ x.toNat < A.toNat + k
    · rw [if_pos hr, if_pos (by omega)]
    · rw [if_neg hr, if_neg (by omega)]

theorem l3StoreMem_step' (m : BitVec 64 → BitVec 8) (A v : BitVec 64) (k k' hi lo : Nat)
    (hk : k < 8) (hA : A.toNat + k < 2 ^ 64) (hk' : k' = k + 1) (hhi : hi = 8 * k + 7)
    (hlo : lo = 8 * k) :
    holUpdate (A + BitVec.ofNat 64 k) (holWordExtract 8 hi lo v) (l3StoreMem m A k v) =
      l3StoreMem m A k' v := by
  subst hk' hhi hlo; exact l3StoreMem_step m A v k hk hA

theorem l3StoreMem_one (m : BitVec 64 → BitVec 8) (A v : BitVec 64) (hA : A.toNat < 2 ^ 64) :
    holUpdate A (holWordExtract 8 7 0 v) m = l3StoreMem m A 1 v := by
  have := l3StoreMem_step m A v 0 (by decide) (by simpa using hA)
  simpa [l3StoreMem_zero] using this

/-- The L3 state after a `w`-byte store of `x[rs2]` at the effective address. -/
def l3Store (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12) (w : Nat) : riscv_state :=
  { s with MEM8 := l3StoreMem s.MEM8 (l3EA s rs1 offs) w (GPR rs2 s) }

theorem l3_sd (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12)
    (hA : (s.c_MCSR s.procID).mcpuid.ArchBase = 2) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (hal : (l3EA s rs1 offs).toNat % 8 = 0) :
    «dfn'SD» (rs1, rs2, offs) s = l3Store s rs1 rs2 offs 8 := by
  have h0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0 := by rw [hA]; decide
  have h1 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1 := by rw [hA]; decide
  have hal' : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  have hlt := (l3EA s rs1 offs).isLt
  have hal2 : (GPR rs1 s + BitVec.signExtend 64 offs).toNat % 8 = 0 := hal
  have hlt2 := (GPR rs1 s + BitVec.signExtend 64 offs).isLt
  rw [dfnSD _ _ _ s h0 h1 hVM hal']
  simp only [l3_ea, l3_ea_add, l3_rs2_val, l3Store]
  rw [l3StoreMem_one _ _ _ hlt,
    l3StoreMem_step' _ _ _ 1 2 15 8 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 2 3 23 16 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 3 4 31 24 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 4 5 39 32 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 5 6 47 40 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 6 7 55 48 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 7 8 63 56 (by decide) (by omega) rfl rfl rfl]

theorem l3_sw (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) (hal : (l3EA s rs1 offs).toNat % 4 = 0) :
    «dfn'SW» (rs1, rs2, offs) s = l3Store s rs1 rs2 offs 4 := by
  have hal' : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  have hal2 : (GPR rs1 s + BitVec.signExtend 64 offs).toNat % 4 = 0 := hal
  have hlt2 := (GPR rs1 s + BitVec.signExtend 64 offs).isLt
  rw [dfnSW _ _ _ s hVM hal']
  simp only [l3_ea, l3_ea_add, l3_rs2_val, l3Store]
  rw [l3StoreMem_one _ _ _ hlt2,
    l3StoreMem_step' _ _ _ 1 2 15 8 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 2 3 23 16 (by decide) (by omega) rfl rfl rfl,
    l3StoreMem_step' _ _ _ 3 4 31 24 (by decide) (by omega) rfl rfl rfl]

theorem l3_sh (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) (hal : (l3EA s rs1 offs).toNat % 2 = 0) :
    «dfn'SH» (rs1, rs2, offs) s = l3Store s rs1 rs2 offs 2 := by
  have hal' : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  have hal2 : (GPR rs1 s + BitVec.signExtend 64 offs).toNat % 2 = 0 := hal
  have hlt2 := (GPR rs1 s + BitVec.signExtend 64 offs).isLt
  rw [dfnSH _ _ _ s hVM hal']
  simp only [l3_ea, l3_ea_add, l3_rs2_val, l3Store]
  rw [l3StoreMem_one _ _ _ hlt2,
    l3StoreMem_step' _ _ _ 1 2 15 8 (by decide) (by omega) rfl rfl rfl]

theorem l3_sb (s : riscv_state) (rs1 rs2 : BitVec 5) (offs : BitVec 12)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    «dfn'SB» (rs1, rs2, offs) s = l3Store s rs1 rs2 offs 1 := by
  have hlt2 := (GPR rs1 s + BitVec.signExtend 64 offs).isLt
  rw [dfnSB _ _ _ s hVM]
  simp only [l3_ea, l3_rs2_val, l3Store]
  rw [l3StoreMem_one _ _ _ hlt2]

end FlapjackRiscvCheck
