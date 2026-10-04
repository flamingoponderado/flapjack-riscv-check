#!/usr/bin/env python3
"""Generate FlapjackRiscvCheck/Decode/<Family>.lean: for each tier-1 instruction,
Sail's decoder maps the L3 encoding `Encode i` to the Sail AST `toSail i`.

Each proof steps through the decoder blocks up to the matching one
(`unfold decodeBlock<k>; guard_simp hw [facts]`), where `facts` give the bit
ranges of the word that are constants or whole fields.
"""
from pathlib import Path

root = Path(__file__).resolve().parent.parent

# bit ranges extracted somewhere in the decoder prefix
RANGES = [(6, 0), (7, 7), (11, 0), (11, 7), (11, 8), (12, 12), (13, 12), (14, 0), (14, 12), (14, 13), (14, 14), (19, 0), (19, 12), (19, 15), (20, 20), (23, 20), (24, 20), (25, 20), (25, 25), (26, 26), (27, 24), (30, 21), (30, 25), (31, 12), (31, 20), (31, 25), (31, 26), (31, 27), (31, 28), (31, 31)]

def facts(layout):
    """layout: list of (hi, lo, value) with value an int (constant) or a Lean BitVec term."""
    out = []
    for (hi, lo) in RANGES:
        covering = [f for f in layout if f[1] <= hi and lo <= f[0]]
        if not covering:
            continue
        if all(isinstance(f[2], int) for f in covering):
            v = 0
            for (fh, fl, fv) in layout:
                if isinstance(fv, int):
                    v |= fv << fl
            val = (v >> lo) & ((1 << (hi - lo + 1)) - 1)
            out.append((hi, lo, f"{val}#{hi - lo + 1}"))
        elif len(covering) == 1 and covering[0][0] == hi and covering[0][1] == lo:
            out.append((hi, lo, covering[0][2]))
    return out

R = lambda f3, f7, op=0x33: [(31,25,f7),(24,20,"rs2"),(19,15,"rs1"),(14,12,f3),(11,7,"rd"),(6,0,op)]
I = lambda f3, op: [(31,20,"imm"),(19,15,"rs1"),(14,12,f3),(11,7,"rd"),(6,0,op)]
SH = lambda f3, f6: [(31,26,f6),(25,20,"sh"),(19,15,"rs1"),(14,12,f3),(11,7,"rd"),(6,0,0x13)]
S = lambda f3: [(31,25,"imm.extractLsb 11 5"),(24,20,"rs2"),(19,15,"rs1"),(14,12,f3),
                (11,7,"imm.extractLsb 4 0"),(6,0,0x23)]
U = lambda op: [(31,12,"imm"),(11,7,"rd"),(6,0,op)]
B = lambda f3: [(31,31,"offs.extractLsb 11 11"),(30,25,"offs.extractLsb 9 4"),(24,20,"rs2"),
                (19,15,"rs1"),(14,12,f3),(11,8,"offs.extractLsb 3 0"),(7,7,"offs.extractLsb 10 10"),(6,0,0x63)]
J = [(31,31,"imm.extractLsb 19 19"),(30,21,"imm.extractLsb 9 0"),(20,20,"imm.extractLsb 10 10"),
     (19,12,"imm.extractLsb 18 11"),(11,7,"rd"),(6,0,0x6F)]

RA = "(rd rs1 rs2 : BitVec 5)"
IA = "(rd rs1 : BitVec 5) (imm : BitVec 12)"
# family -> list of (name, args, L3 instruction, Sail AST, layout, block, extra hyps)
FAM = {
 "RType": [
  ("add", RA, ".ArithR (.ADD (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .ADD)", R(0,0), 11, "(hrd : rd ≠ 0)"),
  ("sub", RA, ".ArithR (.SUB (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB)", R(0,0x20), 19, ""),
  ("and", RA, ".ArithR (.AND (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .AND)", R(7,0), 14, ""),
  ("or", RA, ".ArithR (.OR (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .OR)", R(6,0), 15, ""),
  ("xor", RA, ".ArithR (.XOR (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .XOR)", R(4,0), 16, ""),
  ("sltu", RA, ".ArithR (.SLTU (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLTU)", R(3,0), 13, ""),
  ("sll", RA, ".Shift (.SLL (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SLL)", R(1,0), 17, ""),
  ("srl", RA, ".Shift (.SRL (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRL)", R(5,0), 18, ""),
  ("sra", RA, ".Shift (.SRA (rd, rs1, rs2))", ".RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SRA)", R(5,0x20), 20, ""),
 ],
 "MulDiv": [
  ("mul", RA, ".MulDiv (.MUL (rd, rs1, rs2))", ".MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.Low, .Signed, .Signed⟩)", R(0,1), 37, ""),
  ("mulhu", RA, ".MulDiv (.MULHU (rd, rs1, rs2))", ".MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, ⟨.High, .Unsigned, .Unsigned⟩)", R(3,1), 37, ""),
  ("div", RA, ".MulDiv (.DIV (rd, rs1, rs2))", ".DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, false)", R(4,1), 38, ""),
 ],
 "IType": [
  ("addi", IA, ".ArithI (.ADDI (rd, rs1, imm))", ".ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI)", I(0,0x13), 7, ""),
  ("andi", IA, ".ArithI (.ANDI (rd, rs1, imm))", ".ITYPE (imm, .Regidx rs1, .Regidx rd, .ANDI)", I(7,0x13), 7, ""),
  ("ori", IA, ".ArithI (.ORI (rd, rs1, imm))", ".ITYPE (imm, .Regidx rs1, .Regidx rd, .ORI)", I(6,0x13), 7, "(hrd : rd ≠ 0)"),
  ("xori", IA, ".ArithI (.XORI (rd, rs1, imm))", ".ITYPE (imm, .Regidx rs1, .Regidx rd, .XORI)", I(4,0x13), 7, ""),
  ("slli", "(rd rs1 : BitVec 5) (sh : BitVec 6)", ".Shift (.SLLI (rd, rs1, sh))", ".SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SLLI)", SH(1,0), 8, ""),
  ("srli", "(rd rs1 : BitVec 5) (sh : BitVec 6)", ".Shift (.SRLI (rd, rs1, sh))", ".SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SRLI)", SH(5,0), 9, ""),
  ("srai", "(rd rs1 : BitVec 5) (sh : BitVec 6)", ".Shift (.SRAI (rd, rs1, sh))", ".SHIFTIOP (sh, .Regidx rs1, .Regidx rd, .SRAI)", SH(5,0x10), 10, ""),
  ("lui", "(rd : BitVec 5) (imm : BitVec 20)", ".ArithI (.LUI (rd, imm))", ".UTYPE (imm, .Regidx rd, .LUI)", U(0x37), 3, ""),
  ("auipc", "(rd : BitVec 5) (imm : BitVec 20)", ".ArithI (.AUIPC (rd, imm))", ".UTYPE (imm, .Regidx rd, .AUIPC)", U(0x17), 3, ""),
 ],
 "Mem": [
  ("ld", IA, ".Load (.LD (rd, rs1, imm))", ".LOAD (imm, .Regidx rs1, .Regidx rd, false, 8)", I(3,0x03), 21, ""),
  ("lwu", IA, ".Load (.LWU (rd, rs1, imm))", ".LOAD (imm, .Regidx rs1, .Regidx rd, true, 4)", I(6,0x03), 21, ""),
  ("lhu", IA, ".Load (.LHU (rd, rs1, imm))", ".LOAD (imm, .Regidx rs1, .Regidx rd, true, 2)", I(5,0x03), 21, ""),
  ("lbu", IA, ".Load (.LBU (rd, rs1, imm))", ".LOAD (imm, .Regidx rs1, .Regidx rd, true, 1)", I(4,0x03), 21, ""),
  ("sd", "(rs1 rs2 : BitVec 5) (imm : BitVec 12)", ".Store (.SD (rs1, rs2, imm))", ".STORE (imm, .Regidx rs2, .Regidx rs1, 8)", S(3), 22, ""),
  ("sw", "(rs1 rs2 : BitVec 5) (imm : BitVec 12)", ".Store (.SW (rs1, rs2, imm))", ".STORE (imm, .Regidx rs2, .Regidx rs1, 4)", S(2), 22, ""),
  ("sh", "(rs1 rs2 : BitVec 5) (imm : BitVec 12)", ".Store (.SH (rs1, rs2, imm))", ".STORE (imm, .Regidx rs2, .Regidx rs1, 2)", S(1), 22, ""),
  ("sb", "(rs1 rs2 : BitVec 5) (imm : BitVec 12)", ".Store (.SB (rs1, rs2, imm))", ".STORE (imm, .Regidx rs2, .Regidx rs1, 1)", S(0), 22, ""),
 ],
 "Control": [
  ("jal", "(rd : BitVec 5) (imm : BitVec 20)", ".Branch (.JAL (rd, imm))", ".JAL (imm ++ 0#1, .Regidx rd)", J, 4, ""),
  ("jalr", IA, ".Branch (.JALR (rd, rs1, imm))", ".JALR (imm, .Regidx rs1, .Regidx rd)", I(0,0x67), 5, ""),
 ] + [(n, "(rs1 rs2 : BitVec 5) (offs : BitVec 12)", f".Branch (.{n.upper()} (rs1, rs2, offs))",
       f".BTYPE (offs ++ 0#1, .Regidx rs2, .Regidx rs1, .{n.upper()})", B(f3), 6, "")
      for n, f3 in [("beq",0),("bne",1),("blt",4),("bge",5),("bltu",6),("bgeu",7)]],
}

def args_vars(args):
    vs = []
    for part in args.split(")"):
        part = part.strip(" (")
        if ":" in part:
            vs += part.split(":")[0].split()
    return vs

for fam, items in FAM.items():
    out = ["import FlapjackRiscvCheck.Decode.Basic", "import FlapjackRiscvCheck.Decode.Encoding",
           "import FlapjackRiscvCheck.Decode.Imm", "",
           "/-! GENERATED by scripts/gen-decode-proofs.py. Sail decodes the L3 encodings of the",
           f"tier-1 {fam} instructions to the Sail ASTs `toSail` assigns them. -/", "",
           "namespace FlapjackRiscvCheck", "", "open LeanRV64D LeanRV64D.Functions Flapjack.RiscV.L3", "",
           "set_option maxRecDepth 100000", ""]
    for (name, args, inst, ast, layout, block, hyp) in items:
        vs = args_vars(args)
        fs = facts(layout)
        out.append(f"theorem dec_{name} {{s t}} (h : ExecPre s t) {args} {hyp} :")
        out.append(f"    runSail (encdec_backwards (Encode ({inst}))) t = some ({ast}, t) := by")
        out.append("  obtain ⟨tail, htail⟩ := encdec_backwards_prefix")
        out.append("  rw [htail]")
        out.append(f"  have hw := enc_{name} {' '.join(vs)}")
        out.append("  generalize Encode _ = w at hw ⊢")
        out.append("  " + "; ".join(f"have := {v}.isLt" for v in vs))
        pieces = [v for (_, _, v) in layout if isinstance(v, str) and "extractLsb" in v]
        if pieces:
            out.append("  " + "; ".join(f"have := ({p}).isLt" for p in pieces))
        if "hrd" in hyp:
            out.append("  have : rd.toNat ≠ 0 := fun e => hrd (BitVec.eq_of_toNat_eq e)")
        names = []
        for i, (hi, lo, val) in enumerate(fs):
            out.append(f"  have f{i} : Sail.BitVec.extractLsb w {hi} {lo} = {val} :=")
            out.append(f"    BitVec.eq_of_toNat_eq (by guard_omega hw)")
            names.append(f"f{i}")
        fl = ", ".join(names)
        out.append("  unfold decodePrefix")
        for k in range(1, block + 1):
            out.append(f"  unfold decodeBlock{k}")
            if k == 3:
                out.append("  simp only [runSail_bind_of_eq (runSail_currentlyEnabled_pause t)]")
                out.append(f"  try guard_simp hw [{fl}]")
                out.append("  simp only [runSail_bind_of_eq (runSail_currentlyEnabled_zicfilp h)]")
            out.append(f"  try guard_simp hw [{fl}]")
        out.append("  decode_finish")
        if fam == "MulDiv":
            out.append("  try simp only [runSail_bind_of_eq (runSail_currentlyEnabled_M h),")
            out.append("    runSail_bind_of_eq (runSail_currentlyEnabled_Zmmul h)]")
            out.append("  try decode_finish")
        if fam in ("Mem", "Control"):
            out.append("  all_goals first | exact imm_S _ | (rw [imm_B]) | (rw [imm_J]) | rfl")
        out.append("")
    out.append("end FlapjackRiscvCheck")
    (root / f"FlapjackRiscvCheck/Decode/{fam}.lean").write_text("\n".join(out) + "\n")
    print(fam, len(items))
