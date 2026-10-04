import FlapjackRiscvCheck.Exec.ALU
import FlapjackRiscvCheck.Exec.Imm
import FlapjackRiscvCheck.Exec.MulDiv
import FlapjackRiscvCheck.Exec.Branch
import FlapjackRiscvCheck.Exec.Jump
import FlapjackRiscvCheck.Exec.Load
import FlapjackRiscvCheck.Exec.Store
import Flapjack.RiscV.L3.Defs.Run

/-!
# The tier-1 instruction map and the execute-level simulation

`toSail i` is the Sail AST for the L3 instruction `i`, for the 37 instructions
Flapjack's `riscvEnc` emits (and `none` otherwise). `exec_sim` says that, under
`ExecPre` and the per-instruction memory side condition `MemSide`, Sail's
`execute (toSail i)` retires and its result is related by `ExecPost` to L3's
`Run i`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3

/-- The Sail instruction for a tier-1 L3 instruction. -/
def toSail : Flapjack.RiscV.L3.instruction → Option LeanRV64D.instruction
  | .ArithR (.ADD (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD))
  | .ArithR (.SUB (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB))
  | .ArithR (.AND (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND))
  | .ArithR (.OR (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR))
  | .ArithR (.XOR (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR))
  | .ArithR (.SLTU (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU))
  | .Shift (.SLL (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL))
  | .Shift (.SRL (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL))
  | .Shift (.SRA (rd, rs1, rs2)) => some (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA))
  | .ArithI (.ADDI (rd, rs1, imm)) => some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))
  | .ArithI (.ANDI (rd, rs1, imm)) => some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI))
  | .ArithI (.ORI (rd, rs1, imm)) => some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI))
  | .ArithI (.XORI (rd, rs1, imm)) => some (.ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI))
  | .ArithI (.LUI (rd, imm)) => some (.UTYPE (imm, .Regidx rd, .LUI))
  | .ArithI (.AUIPC (rd, imm)) => some (.UTYPE (imm, .Regidx rd, .AUIPC))
  | .Shift (.SLLI (rd, rs1, sh)) => some (.SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SLLI))
  | .Shift (.SRLI (rd, rs1, sh)) => some (.SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SRLI))
  | .Shift (.SRAI (rd, rs1, sh)) => some (.SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SRAI))
  | .MulDiv (.MUL (rd, rs1, rs2)) =>
    some (.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩))
  | .MulDiv (.MULHU (rd, rs1, rs2)) =>
    some (.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩))
  | .MulDiv (.DIV (rd, rs1, rs2)) => some (.DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, false))
  | .Load (.LD (rd, rs1, imm)) => some (.LOAD (imm, .Regidx rs1, .Regidx rd, false, 8))
  | .Load (.LWU (rd, rs1, imm)) => some (.LOAD (imm, .Regidx rs1, .Regidx rd, true, 4))
  | .Load (.LHU (rd, rs1, imm)) => some (.LOAD (imm, .Regidx rs1, .Regidx rd, true, 2))
  | .Load (.LBU (rd, rs1, imm)) => some (.LOAD (imm, .Regidx rs1, .Regidx rd, true, 1))
  | .Store (.SD (rs1, rs2, imm)) => some (.STORE (imm, .Regidx rs2, .Regidx rs1, 8))
  | .Store (.SW (rs1, rs2, imm)) => some (.STORE (imm, .Regidx rs2, .Regidx rs1, 4))
  | .Store (.SH (rs1, rs2, imm)) => some (.STORE (imm, .Regidx rs2, .Regidx rs1, 2))
  | .Store (.SB (rs1, rs2, imm)) => some (.STORE (imm, .Regidx rs2, .Regidx rs1, 1))
  | .Branch (.BEQ (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BEQ))
  | .Branch (.BNE (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BNE))
  | .Branch (.BLT (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BLT))
  | .Branch (.BGE (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BGE))
  | .Branch (.BLTU (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BLTU))
  | .Branch (.BGEU (rs1, rs2, offs)) => some (.BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .BGEU))
  | .Branch (.JAL (rd, imm)) => some (.JAL (imm ++ 0#1, .Regidx rd))
  | .Branch (.JALR (rd, rs1, imm)) => some (.JALR (imm, .Regidx rs1, .Regidx rd))
  | _ => none

/-- Memory side condition: a load/store is a plain aligned RAM access in Sail and, for
loads, its bytes lie in the related domain `D`. -/
def MemSide (s : L3State) (t : SailState) (D : BitVec 64 → Prop) : Flapjack.RiscV.L3.instruction → Prop
  | .Load (.LD (_, rs1, imm)) => SailAccessOK t (l3EA s rs1 imm) 8 false ∧
      ∀ i < 8, D (l3EA s rs1 imm + BitVec.ofNat 64 i)
  | .Load (.LWU (_, rs1, imm)) => SailAccessOK t (l3EA s rs1 imm) 4 false ∧
      ∀ i < 4, D (l3EA s rs1 imm + BitVec.ofNat 64 i)
  | .Load (.LHU (_, rs1, imm)) => SailAccessOK t (l3EA s rs1 imm) 2 false ∧
      ∀ i < 2, D (l3EA s rs1 imm + BitVec.ofNat 64 i)
  | .Load (.LBU (_, rs1, imm)) => SailAccessOK t (l3EA s rs1 imm) 1 false ∧
      ∀ i < 1, D (l3EA s rs1 imm + BitVec.ofNat 64 i)
  | .Store (.SD (rs1, _, imm)) => SailAccessOK t (l3EA s rs1 imm) 8 true
  | .Store (.SW (rs1, _, imm)) => SailAccessOK t (l3EA s rs1 imm) 4 true
  | .Store (.SH (rs1, _, imm)) => SailAccessOK t (l3EA s rs1 imm) 2 true
  | .Store (.SB (rs1, _, imm)) => SailAccessOK t (l3EA s rs1 imm) 1 true
  | _ => True

/-- Lift a "writes `v` to `rd`" simulation to the execute contract. -/
theorem post_of_write {s t} (h : ExecPre s t) {m : SailM ExecutionResult} {s' : L3State}
    {rd : BitVec 5} {v : BitVec 64}
    (hm : runSail m t = some (RETIRE_SUCCESS, sailSetGpr t rd v)) (hs : s' = «write'GPR» (v, rd) s) :
    ∃ t', runSail m t = some (RETIRE_SUCCESS, t') ∧ ExecPost s s' t t' :=
  ⟨_, hm, hs ▸ ExecPost.of_write h rd v⟩

theorem exec_sim {s t} {D : BitVec 64 → Prop} (h : ExecPre s t) (hm : MemRel s t D)
    (i : Flapjack.RiscV.L3.instruction) (si : LeanRV64D.instruction) (hi : toSail i = some si) (hside : MemSide s t D i) :
    ∃ t', runSail (execute si) t = some (RETIRE_SUCCESS, t') ∧ ExecPost s (Run i s) t t' := by
  cases i with
  | ArithR a =>
    cases a with
    | ADD x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := add_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | SUB x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := sub_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | AND x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := and_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | OR x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := or_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | XOR x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := xor_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | SLTU x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := sltu_sim h.rel h.rv64 rd rs1 rs2; exact post_of_write h hr hl
    | _ => simp [toSail] at hi
  | Shift a =>
    cases a with
    | SLL x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := sll_sim h.rel h.rv64 rd rs1 rs2; exact post_of_write h hr hl
    | SRL x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := srl_sim h.rel h.rv64 rd rs1 rs2; exact post_of_write h hr hl
    | SRA x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := sra_sim h.rel h.rv64 rd rs1 rs2; exact post_of_write h hr hl
    | SLLI x =>
      obtain ⟨rd, rs1, sh⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := slli_sim h.rel h.rv64 rd rs1 sh; exact post_of_write h hr hl
    | SRLI x =>
      obtain ⟨rd, rs1, sh⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := srli_sim h.rel h.rv64 rd rs1 sh; exact post_of_write h hr hl
    | SRAI x =>
      obtain ⟨rd, rs1, sh⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := srai_sim h.rel h.rv64 rd rs1 sh; exact post_of_write h hr hl
    | _ => simp [toSail] at hi
  | ArithI a =>
    cases a with
    | ADDI x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := addi_sim h.rel rd rs1 imm; exact post_of_write h hr hl
    | ANDI x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := andi_sim h.rel rd rs1 imm; exact post_of_write h hr hl
    | ORI x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := ori_sim h.rel rd rs1 imm; exact post_of_write h hr hl
    | XORI x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := xori_sim h.rel rd rs1 imm; exact post_of_write h hr hl
    | LUI x =>
      obtain ⟨rd, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := lui_sim (s := s) (t := t) rd imm; exact post_of_write h hr hl
    | AUIPC x =>
      obtain ⟨rd, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := auipc_sim h.rel rd imm; exact post_of_write h hr hl
    | _ => simp [toSail] at hi
  | MulDiv a =>
    cases a with
    | MUL x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := mul_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | MULHU x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := mulhu_sim h.rel h.rv64 rd rs1 rs2; exact post_of_write h hr hl
    | DIV x =>
      obtain ⟨rd, rs1, rs2⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      obtain ⟨v, hr, hl⟩ := div_sim h.rel rd rs1 rs2; exact post_of_write h hr hl
    | _ => simp [toSail] at hi
  | Load a =>
    cases a with
    | LD x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact ld_sim h hm rd rs1 imm hside.1 hside.2
    | LWU x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact lwu_sim h hm rd rs1 imm hside.1 hside.2
    | LHU x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact lhu_sim h hm rd rs1 imm hside.1 hside.2
    | LBU x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact lbu_sim h hm rd rs1 imm hside.1 hside.2
    | _ => simp [toSail] at hi
  | Store a =>
    cases a with
    | SD x =>
      obtain ⟨rs1, rs2, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact sd_sim h rs1 rs2 imm hside
    | SW x =>
      obtain ⟨rs1, rs2, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact sw_sim h rs1 rs2 imm hside
    | SH x =>
      obtain ⟨rs1, rs2, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact sh_sim h rs1 rs2 imm hside
    | SB x =>
      obtain ⟨rs1, rs2, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact sb_sim h rs1 rs2 imm hside
  | Branch a =>
    cases a with
    | BEQ x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact beq_sim h rs1 rs2 offs
    | BNE x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact bne_sim h rs1 rs2 offs
    | BLT x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact blt_sim h rs1 rs2 offs
    | BGE x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact bge_sim h rs1 rs2 offs
    | BLTU x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact bltu_sim h rs1 rs2 offs
    | BGEU x =>
      obtain ⟨rs1, rs2, offs⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact bgeu_sim h rs1 rs2 offs
    | JAL x =>
      obtain ⟨rd, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact jal_sim h rd imm
    | JALR x =>
      obtain ⟨rd, rs1, imm⟩ := x
      simp only [toSail, Option.some.injEq] at hi; subst hi
      exact jalr_sim h rd rs1 imm
  | _ => simp [toSail] at hi

end FlapjackRiscvCheck
