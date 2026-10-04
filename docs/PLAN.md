# Plan: Flapjack L3 RISC-V vs Sail RISC-V

## What the proof is for

Flapjack proves Pancake-to-RISC-V compiler correctness against its port of the
HOL4 L3 RISC-V model (`Flapjack.RiscV.L3`, through `riscvTarget` /
`riscvNext := holThe ∘ NextRISCV`). That model has not been validated. The
goal here is to carry the guarantee over to the Sail RISC-V model
(`LeanRV64D`), the RISC-V International golden model.

Both models are deterministic, so what is needed is a **forward simulation from
L3 to Sail**: from related states, if L3 takes a step, Sail takes a step to a
related state. Iterating this turns every L3 run that the compiler theorem
talks about into a Sail run with the same observable registers and memory.

## Prior art

- **No published L3-vs-Sail proof for RISC-V turned up.** The closest
  precedent is Kanabar, Fox, Myreen et al., "Taming an Authoritative Armv8 ISA
  Specification: L3 Validation and CakeML Compiler Verification" (ITP 2022).
  It proves in HOL4 that CakeML's L3 Armv8 model simulates the Sail/ASL Armv8.6
  model, and re-targets the CakeML compiler theorem. Code:
  HOL `examples/l3-machine-code/arm8/asl-equiv` (HOL PR #981) and CakeML PR #858.
  Its proof organisation (per-instruction simulation lemmas under a
  state-relation plus side-condition invariant, then a step theorem used to
  re-instantiate the compiler theorem) is the model for this project.
- **riscv-zkvm** (`Verified-zkEVM/riscv-zkvm`) proves 51 per-instruction
  `*_sail_equiv` theorems for a hand-written RV64IM model against a *scoped*
  Sail extraction, plus a step/run simulation. Its techniques transfer
  directly (see "Proof technique"). Its code cannot be a Lake dependency here:
  it pins lean-sail v4 and its own `RiscvZkvm.Sail` namespace, while
  sail-riscv-lean uses lean-sail v5 and `LeanRV64D`, and the two `Sail`
  packages would conflict. Lemmas are ported instead. They are BSD 2-Clause
  (Sail RISC-V model contributors), so ported files keep that header and
  `LICENSE` lists them (see README).

## Scope

The compiler theorem only uses GPRs, PC, `MEM8`, `NextFetch`, `exception`,
`mstatus.VM` and `mcpuid.ArchBase`. `riscvEnc` emits only these 37
instructions (no compressed encodings):

    LUI AUIPC ADDI ORI XORI ANDI ADD SUB AND OR XOR SLTU
    SLLI SRLI SRAI SLL SRL SRA DIV MUL MULHU
    LD LWU LHU LBU SD SW SH SB
    BEQ BNE BLT BGE BLTU BGEU JAL JALR

**Tier 1 (the target):** these 37 instructions.
**Tier 2:** the rest of RV64IM, then A (LR/SC needs the
`load_reservation`/`match_reservation` axioms, so it is weaker).

**Out of scope, with reasons:**
- **F/D:** every floating-point primitive in `LeanRV64D/RiscvExtras.lean` is an
  `axiom` (`riscv_f64Add`, ...), so nothing can be proved equal to L3's
  `Rat`-based rendering. This is not a gap in the proof.
- **Zicsr, traps, MMU, privilege:** L3 follows the old privileged spec
  (priv 1.7: `mstatus.VM`, `mcpuid`, `MRTS`, `ERET`), and Sail follows the
  current one. Divergence is expected by construction. Machine-mode bare
  execution is fixed by invariants instead of being related.

## The statements

The files under `FlapjackRiscvCheck/` are planned:

1. **`Models.lean` (exists):** names for the two states and step functions.
2. **`Relation.lean`:**
   - `Rel (s : L3State) (t : SailState)`: x1..x31 agree (`c_gpr s.procID` vs
     `regs.get? Register.xN`), `PC` agrees, and memory agrees on a declared
     region (`MEM8 a = b` iff `t.mem.get? a.toNat = some b` for `a` in the
     region; Sail memory is a partial `ExtHashMap`, L3's is total).
   - `L3Inv s`: `riscvOk s`, the condition Flapjack's target layer already
     requires.
   - `SailInv t`:
     - Machine privilege, `MPRV = 0`, no pointer masking, so translation is bare.
     - PMP off and `pma_regions` fixed, with the region RAM, not MMIO.
     - No pending-and-enabled interrupts.
     - `misa` present, Zicfilp landing pads inactive.
     - CLINT/HTIF outside the region.
   - **Anti-vacuity:** a concrete `(s, t)` satisfying all three. riscv-zkvm
     lost real coverage twice to vacuous hypotheses (`update_elp_state` always
     faulting, PC ignored in branch proofs).
3. **`Instr.lean`:** `toSail : L3.instruction → Option LeanRV64D.instruction`,
   defined on the tier-1 subset.
4. **`Exec/*.lean`:** per-instruction lemmas, grouped by family as in riscv-zkvm:
   ```
   Rel s t → L3Inv s → SailInv t → side i s →
   ∃ t', runSail (execute (toSail i)) t = some (RETIRE_SUCCESS, t') ∧
         Rel (L3.Run i s) t' ∧ nextPC t' = PC of the L3 result ∧ SailInv t'
   ```
5. **`Decode.lean`:** for every 32-bit `w`, if `L3.Decode w = i` with `i` in
   scope, then Sail's `ext_decode w` gives `toSail i`. Both decoders are
   reduced by case analysis on opcode/funct fields. riscv-zkvm left this out
   ("known gap 3"); this project should not.
6. **`Step.lean`:** `l3Next s = some s'` together with the invariants gives
   Sail `try_step` from `t` with `t'` related to `s'`. This covers the whole
   top-level step: interrupt check, fetch, decode, execute, `tick_pc`.
7. **`Run.lean` and the compiler transfer:** iterate `Step` to get a run
   simulation. Then restate `panToTargetCompileSemanticsRiscV` with its
   machine behaviour observed through Sail, which needs the L3 premises
   (`riscvOk`, code installed in `MEM8`) to be derivable from the Sail-side
   initial state.

## Expected divergences

Each of these either becomes a side condition or is reported as a finding:

- **Misaligned loads/stores:** L3's `rawReadData`/`rawWriteData` perform them.
  Sail traps or splits them depending on the PMA region's
  `misaligned_exceptions`. The side condition is alignment, or a PMA that
  allows misaligned access. The finding to check is whether Flapjack's
  generated code only makes aligned accesses.
- **Jump-target alignment:** L3's JAL/JALR trap only when bit 0 is set, so
  they check 2-byte alignment. That matches Sail with C enabled. JALR clears
  bit 0 first, so on L3 its check never fires. Conditional branches have no
  check in L3, but their offsets are even. These are expected to agree; the
  thing to confirm is Sail's own JAL/branch target check under the `misa.C`
  value the invariant fixes.
- **`JALR`:** Sail additionally updates Zicfilp `elp` state.
- **Counters:** L3 `c_instret`/`c_cycles` vs Sail `minstret`/`mcycle` are not
  related, and the compiler theorem does not observe them.
- **Memory domain:** total vs partial memory, PMA regions and MMIO. Byte
  presence is part of `Rel` on the region.

## Proof technique (adapted from riscv-zkvm)

- **Running Sail:** `runSail m t : Option (α × SailState)` over `EStateM`, with
  simp lemmas `runSail_bind`/`runSail_pure`. Add a `sail_step` simp attribute
  (`SailME.run`, ExceptT/EStateM bind, `monadLift`) and a `sail_reduce` macro.
- **Registers:** one simp lemma per register for `rX_bits`/`wX_bits`, plus a
  32-way case split with `Std.ExtDHashMap.get?_insert`.
- **Memory:** reduce bare mode stage by stage (`translateAddr` bare, PMP-off
  `pmpCheck`, PMA load/store OK, page-boundary split for aligned accesses),
  then a little-endian byte-assembly bridge to L3's `MEM`.
- **The L3 side** is HOL-style state passing (`riscv_state → α × riscv_state`,
  `holUpdate`). Unfold `Run` and simp on record updates. In-scope paths must
  not reach `holArb`, which is opaque. A path that does is a finding.
- **Bitvectors:** use `omega`, `decide`, `BitVec.eq_of_toNat_eq` and per-operator
  bridge lemmas (signed division/rounding, SLTU, shifts by `shamt`).
- **Trusted base:** no `native_decide`. `bv_decide` is allowed only if we accept
  `Lean.ofReduceBool`; the default is not to. Add a `scripts/check-axioms.sh`
  that pins the axiom set to Lean's 3 classical axioms plus the Sail platform
  axioms actually reached.
- **Build:** import `LeanRV64D` modules narrowly (e.g. `InstsEnd`, `Step`), and
  never the umbrella. Split proofs by instruction family. Keep
  `--tstack=400000`.

## Status (2026-10-05)

Milestones 1–5 are done; see "Main theorems" in the README. Milestone 6, transferring
Flapjack's top theorem, is still open (below). Milestone 7 (tier 2) has not been
started.

- **Execute (`Exec/`):** `exec_sim` covers all 37 tier-1 instructions against
  Sail's `execute`.
- **Decode (`Decode/`):** `sail_decode_sim` and `l3_decode_sim` show that both
  models decode `Encode i` as expected. Sail's 56k-line decoder is handled by
  divide and conquer:
  - `scripts/gen-decode-prefix.py` copies its first 41 pattern blocks into one
    definition each.
  - `encdec_backwards = decodePrefix tail` holds by `rfl`.
  - `scripts/gen-decode-proofs.py` steps through the blocks for each
    instruction. Each guard is decided by `omega` on the encoded word's numeric
    formula.
- **Step (`Step/Sim.lean`):** `step_sim` relates `NextRISCV` to `try_step`. This
  covers interrupt dispatch, fetch, decode, the landing-pad check, `execute`,
  `tick_pc` and `minstret`.
- **Run (`Step/Run.lean`):** `run_sim` iterates the step simulation.
- **Anti-vacuity (`Witness.lean`):** concrete states satisfy every hypothesis,
  and `run_sim` executes one step on them.
- **Trusted base:** `scripts/check-axioms.sh` checks for no `sorry`, no
  `native_decide`/`bv_decide`, and only Lean's three classical axioms plus the
  functions the Sail extraction declares as `axiom`.

## Divergences and assumptions found

- **Hint encodings.** Sail decodes `ADD x0, x0, x2..x5` as Zihintntl `NTL` and
  `ORI x0, rs1, imm` (with `imm[4:0] ∈ {0,1,3}`) as a Zicbop prefetch. L3
  decodes them as plain ALU ops with `rd = x0`, so they are excluded (`HintFree`).
  Both are architectural no-ops, but the prefetch probes PMA/PMP.
- **Misaligned accesses.** L3 performs them; Sail's behaviour depends on the
  PMA. Loads and stores are assumed aligned (`SailAccessOK.aligned`).
- **Memory.** Sail's memory is a partial map with PMA regions and MMIO windows,
  whereas L3 has a total `MEM8`. Accesses must lie in a readable/writable PMA
  region, miss CLINT/signature/HTIF, and (for loads and fetch) hit the related
  domain `D`.
- **Compressed instructions and jump alignment.** These match when
  `misa.C = 1`. The fetch path assumes a 4-aligned PC, which `riscvOk`
  provides.
- **Zicfilp.** Sail's JALR updates `elp` unless `mseccfg.MLPE = 0`. That, plus
  `elp = 0`, is part of the invariant.
- **Interrupts** are excluded by `mstatus.MIE = 0` in machine mode.
- **M extension.** DIV needs `misa.M = 1` in Sail, which is in the invariant.

## Open: transferring the compiler theorem (milestone 6)

`panToTargetCompileSemanticsRiscV` is stated over CakeML's machine semantics
with `next = riscvNext`, including FFI interference and halting. Moving it to
Sail needs two things:

1. A Sail-based `MachineConfig` whose `next` is `try_step` on related states.
   `run_sim` relates the two runs.
2. A proof that every execution of compiled Pancake code meets `GoodRun`. The
   code region must hold hint-free tier-1 encodings (`riscvEnc` produces
   `Encode i`), every load/store must be aligned and inside a RAM region in
   `D`, and every PC must stay 4-aligned.

Part 2 needs facts from Flapjack's compiler-correctness proof (code
installation, `target_state_rel`, the memory domain). That is a separate
project on the Flapjack side.

## Build notes

- `LeanRV64D.RvfiDii` takes about 25 minutes to build, and `LeanRV64D.Step`
  imports it. Proof files should import `LeanRV64D.InstsEnd` (about 2 minutes)
  or smaller modules. Only the final step theorem needs `Step`.
- Check a single file with `lake lean <file>`. `lake env lean` cannot find
  dependency `.olean`s that live in Lake's artifact cache.
- `Sail/RegsFrame.lean` (the 32 × 32 register read-after-write case split)
  takes about 100 s. It has its own module so it rebuilds rarely.

## Milestones

1. `Relation.lean` with the anti-vacuity witness.
2. ADD/ADDI end to end through `execute`, to validate the setup.
3. All tier-1 ALU/shift/mul/div instructions, then branches/JAL/JALR, then
   loads/stores.
4. Decode equivalence for tier 1.
5. `try_step` simulation, then the run simulation.
6. Transfer of the Flapjack top theorem to Sail.
7. Tier 2.
