import FlapjackRiscvCheck.L3.Regs
import FlapjackRiscvCheck.Sail.Mem.Bytes
import Flapjack.RiscV.L3.Step.LoadStep

/-!
# L3 loads as byte reads

From Flapjack's ported HOL step theorems (`dfnLD`, `dfnLWU`, `dfnLHU`,
`dfnLBU` and their `rd = 0` companions): each tier-1 load writes to `rd` a
value whose `toNat` is the little-endian number `leNat` of the bytes at the
effective address.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step

theorem toNat_byte_append {n : Nat} (b : BitVec 8) (x : BitVec n) :
    (b ++ x).toNat = b.toNat * 2 ^ n + x.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]

theorem l3_ea (s : riscv_state) (rs1 : BitVec 5) (offs : BitVec 12) :
    (if rs1 = 0 then BitVec.signExtend 64 offs else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs)
      = GPR rs1 s + BitVec.signExtend 64 offs := by
  by_cases h : rs1 = 0
  · simp [GPR, h]
  · have h' : ¬ rs1 = 0#5 := h
    simp [GPR, gpr, h']

theorem l3_ea_add (s : riscv_state) (rs1 : BitVec 5) (offs : BitVec 12) (k : BitVec 64) :
    (if rs1 = 0 then BitVec.signExtend 64 offs + k
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs + k)
      = GPR rs1 s + BitVec.signExtend 64 offs + k := by
  by_cases h : rs1 = 0
  · simp [GPR, h]
  · have h' : ¬ rs1 = 0#5 := h
    simp [GPR, gpr, h']

theorem l3_write'GPR_eq (s : riscv_state) (rd : BitVec 5) (hrd : rd ≠ 0) (v : BitVec 64) :
    «write'GPR» (v, rd) s =
      { s with c_gpr := holUpdate s.procID (holUpdate rd v (s.c_gpr s.procID)) s.c_gpr } := by
  have hrd' : ¬ rd = 0#5 := hrd
  simp [«write'GPR», «write'gpr», hrd']

theorem l3_write'GPR_zero (s : riscv_state) (v : BitVec 64) : «write'GPR» (v, 0) s = s := by
  simp [«write'GPR»]

/-- The effective address of a load/store. -/
abbrev l3EA (s : riscv_state) (rs1 : BitVec 5) (offs : BitVec 12) : BitVec 64 :=
  GPR rs1 s + BitVec.signExtend 64 offs

theorem l3_ld (s : riscv_state) (rd rs1 : BitVec 5) (offs : BitVec 12)
    (hA : (s.c_MCSR s.procID).mcpuid.ArchBase = 2) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (hal : (l3EA s rs1 offs).toNat % 8 = 0) :
    ∃ v : BitVec 64, «dfn'LD» (rd, rs1, offs) s = «write'GPR» (v, rd) s ∧
      v.toNat = leNat (fun i => s.MEM8 (l3EA s rs1 offs + BitVec.ofNat 64 i)) 8 := by
  have h0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0 := by rw [hA]; decide
  have h1 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1 := by rw [hA]; decide
  have hal' : Flapjack.holAligned 3 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  let A := l3EA s rs1 offs
  refine ⟨s.MEM8 (A + 7#64) ++ (s.MEM8 (A + 6#64) ++ (s.MEM8 (A + 5#64) ++ (s.MEM8 (A + 4#64) ++
    (s.MEM8 (A + 3#64) ++ (s.MEM8 (A + 2#64) ++ (s.MEM8 (A + 1#64) ++ s.MEM8 A)))))), ?_, ?_⟩
  · by_cases hrd : rd = 0
    · subst hrd; rw [dfnLDNop _ _ _ s h0 h1 rfl hVM hal', l3_write'GPR_zero]
    · rw [dfnLD _ _ _ s h0 h1 hrd hVM hal', l3_write'GPR_eq _ _ hrd]
      simp only [l3_ea, l3_ea_add, A, l3EA]
  · simp only [toNat_byte_append, leNat, A]
    simp
    omega

theorem l3_lwu (s : riscv_state) (rd rs1 : BitVec 5) (offs : BitVec 12)
    (hA : (s.c_MCSR s.procID).mcpuid.ArchBase = 2) (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5)
    (hal : (l3EA s rs1 offs).toNat % 4 = 0) :
    ∃ v : BitVec 64, «dfn'LWU» (rd, rs1, offs) s = «write'GPR» (v, rd) s ∧
      v.toNat = leNat (fun i => s.MEM8 (l3EA s rs1 offs + BitVec.ofNat 64 i)) 4 := by
  have h0 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 0 := by rw [hA]; decide
  have h1 : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1 := by rw [hA]; decide
  have hal' : Flapjack.holAligned 2 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  let A := l3EA s rs1 offs
  refine ⟨BitVec.setWidth 64 (s.MEM8 (A + 3#64) ++ (s.MEM8 (A + 2#64) ++ (s.MEM8 (A + 1#64) ++
    s.MEM8 A))), ?_, ?_⟩
  · by_cases hrd : rd = 0
    · subst hrd; rw [dfnLWUNop _ _ _ s h0 h1 rfl hVM, l3_write'GPR_zero]
    · rw [dfnLWU _ _ _ s h0 h1 hrd hVM hal', l3_write'GPR_eq _ _ hrd]
      simp only [l3_ea, l3_ea_add, A, l3EA]
  · simp only [BitVec.toNat_setWidth, toNat_byte_append, leNat, A]
    simp
    omega

theorem l3_lhu (s : riscv_state) (rd rs1 : BitVec 5) (offs : BitVec 12)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) (hal : (l3EA s rs1 offs).toNat % 2 = 0) :
    ∃ v : BitVec 64, «dfn'LHU» (rd, rs1, offs) s = «write'GPR» (v, rd) s ∧
      v.toNat = leNat (fun i => s.MEM8 (l3EA s rs1 offs + BitVec.ofNat 64 i)) 2 := by
  have hal' : Flapjack.holAligned 1 (if rs1 = 0 then BitVec.signExtend 64 offs
      else s.c_gpr s.procID rs1 + BitVec.signExtend 64 offs) = true := by
    rw [Flapjack.holAligned_iff, l3_ea]; simpa using hal
  let A := l3EA s rs1 offs
  refine ⟨BitVec.setWidth 64 (s.MEM8 (A + 1#64) ++ s.MEM8 A), ?_, ?_⟩
  · by_cases hrd : rd = 0
    · subst hrd; rw [dfnLHUNop _ _ _ s rfl hVM, l3_write'GPR_zero]
    · rw [dfnLHU _ _ _ s hrd hVM hal', l3_write'GPR_eq _ _ hrd]
      simp only [l3_ea, l3_ea_add, A, l3EA]
  · simp only [BitVec.toNat_setWidth, toNat_byte_append, leNat, A]
    simp
    omega

theorem l3_lbu (s : riscv_state) (rd rs1 : BitVec 5) (offs : BitVec 12)
    (hVM : (s.c_MCSR s.procID).mstatus.VM = 0#5) :
    ∃ v : BitVec 64, «dfn'LBU» (rd, rs1, offs) s = «write'GPR» (v, rd) s ∧
      v.toNat = leNat (fun i => s.MEM8 (l3EA s rs1 offs + BitVec.ofNat 64 i)) 1 := by
  let A := l3EA s rs1 offs
  refine ⟨BitVec.setWidth 64 (s.MEM8 A), ?_, ?_⟩
  · by_cases hrd : rd = 0
    · subst hrd; rw [dfnLBUNop _ _ _ s rfl hVM, l3_write'GPR_zero]
    · rw [dfnLBU _ _ _ s hrd hVM, l3_write'GPR_eq _ _ hrd]
      simp only [l3_ea, A, l3EA]
  · simp only [BitVec.toNat_setWidth, leNat, A]
    simp
    omega

end FlapjackRiscvCheck
