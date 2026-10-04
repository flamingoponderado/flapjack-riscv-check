# flapjack-riscv-check

Lean 4 project comparing two RISC-V semantics:

- **Flapjack's L3 model** (`Flapjack.RiscV.L3`, from
  [flamingoponderado/flapjack](https://github.com/flamingoponderado/flapjack) `main`).
  This is a port of the HOL4 L3 RISC-V model. Flapjack's Pancake-to-RISC-V
  compiler correctness theorem is stated against it.
- **The Sail RISC-V model** (`LeanRV64D`, from
  [flamingoponderado/sail-riscv-lean](https://github.com/flamingoponderado/sail-riscv-lean) `main`).
  This is the Lean extraction of the RISC-V International golden model.

The goal is a simulation theorem: on the instructions Flapjack's backend emits,
and from related machine states, every L3 step is matched by a Sail step. The
approach is in [`docs/PLAN.md`](docs/PLAN.md).

> [!WARNING]
> **The two models are not equivalent in general.** The proof covers only the
> 37 instructions Flapjack's backend emits, under these restrictions:
>
> - **Hint encodings are excluded.** Sail decodes `ADD x0, x0, x2..x5` as a
>   Zihintntl `NTL` hint and `ORI x0, rs1, imm` (with `imm[4:0] ∈ {0,1,3}`) as
>   a Zicbop prefetch. L3 decodes both as plain ALU ops writing `x0`.
> - **Misaligned loads and stores are excluded.** L3 performs them, while Sail
>   traps or splits them depending on the PMA region.
> - **Memory must be plain RAM.** Sail's memory is a partial map with PMA
>   regions and MMIO windows (CLINT, signature, HTIF); L3's `MEM8` is total.
>   Accesses must lie in a readable/writable/executable PMA region, miss the
>   MMIO windows, and touch only addresses in the related domain.
> - **Sail must be configured to match L3's assumptions:**
>   - machine mode with `mstatus.MPRV = 0`;
>   - pointer masking off and all PMP entries OFF;
>   - `misa.C = misa.M = 1`;
>   - `mseccfg.MLPE = 0` and `elp = 0` (Sail's JALR otherwise updates
>     Zicfilp landing-pad state, which L3 does not model);
>   - `mstatus.MIE = 0` (no interrupts);
>   - the PC 4-aligned.
> - **Not covered:**
>   - floating point (every Sail FP primitive is an uninterpreted `axiom`);
>   - CSRs, traps, privilege changes and virtual memory (L3 follows the old
>     privileged spec 1.7);
>   - atomics, and RV64IM instructions outside Flapjack's set.
> - **Flapjack's compiler theorem has not yet been transferred to Sail.**
>
> Details are in [`docs/PLAN.md`](docs/PLAN.md).

## Prior work

The approach and target follow the Armv8 version of the same problem:

> Hrutvik Kanabar, Anthony C. J. Fox, Magnus O. Myreen.
> *Taming an Authoritative Armv8 ISA Specification: L3 Validation and CakeML
> Compiler Verification.* ITP 2022, LIPIcs 237, paper 20.
> [doi:10.4230/LIPIcs.ITP.2022.20](https://doi.org/10.4230/LIPIcs.ITP.2022.20)

That paper proves in HOL4 that CakeML's L3 Armv8 model simulates Arm's
official Sail specification, then re-targets the CakeML compiler correctness
theorem. This project does the same for RISC-V in Lean. It proves that
Flapjack's port of the L3 RISC-V model and the Sail RISC-V model run in
lockstep on the instructions Flapjack emits. Re-targeting Flapjack's Pancake
compiler theorem on top of that is the remaining step.

The per-instruction proof technique against the Lean Sail extraction is
modelled on [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm).

## Main theorems

All are `sorry`-free; `scripts/check-axioms.sh` lists their axioms.

- `exec_sim` (`Exec/Dispatch.lean`): for each of the 37 instructions Flapjack's
  backend emits, L3 `Run i` and Sail `execute (toSail i)` agree. The agreement
  covers registers, the next PC, memory (`MemRel`) and a frame on everything
  else.
- `sail_decode_sim` / `l3_decode_sim` (`Decode/Dispatch.lean`): both models
  decode the encoding `Encode i`.
- `step_sim` (`Step/Sim.lean`): one L3 `NextRISCV` step matches one Sail
  `try_step` from related states (`StepRel`), under per-step side conditions
  (`StepSide`):
  - the word at `PC` encodes a tier-1, hint-free instruction;
  - the fetch and any load/store are plain aligned RAM accesses.
- `run_sim` (`Step/Run.lean`): the same for `k` steps, along any L3 run that
  meets the side conditions (`GoodRun`).
- `Witness.run_sim_nonvacuous`: concrete states satisfy all the hypotheses.

The Sail-side invariants are:

- machine mode, `MPRV = 0`;
- pointer masking off, PMP entries all OFF;
- `misa.C = misa.M = 1`;
- `mseccfg.MLPE = 0`, `elp = 0`;
- `mstatus.MIE = 0`;
- the hart is active.

The L3 side assumes Flapjack's `riscvOk` conditions. Divergences found, and the
open step of transferring Flapjack's compiler theorem, are in
[`docs/PLAN.md`](docs/PLAN.md).

Some files are generated:

- `scripts/gen-decode-prefix.py` produces `Sail/DecodePrefixDef.lean`.
- `scripts/gen-decode-proofs.py` produces `Decode/{RType,MulDiv,IType,Mem,Control}.lean`.
- `scripts/gen-decode-dispatch.py` produces `Decode/Dispatch.lean`.

## Build

```sh
lake exe cache get   # Mathlib oleans (Flapjack depends on Mathlib)
lake build
```

Both dependencies track `main`. `lake-manifest.json` pins the exact commits;
run `lake update` to move them.

## License

BSD 3-Clause; see [`LICENSE`](LICENSE).

Code ported from another project is a derived work and keeps that project's
license. If code is ported from, for example, riscv-zkvm's Sail-equivalence
proofs (BSD 2-Clause, Sail RISC-V model contributors), the ported files keep
their original copyright and license header, and `LICENSE` gains an "Other
licensed material" section naming them.
