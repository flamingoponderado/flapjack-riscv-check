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

## Prior work

The approach and target follow the Armv8 version of the same problem:

> Hrutvik Kanabar, Anthony C. J. Fox, Magnus O. Myreen.
> *Taming an Authoritative Armv8 ISA Specification: L3 Validation and CakeML
> Compiler Verification.* ITP 2022, LIPIcs 237, paper 20.
> [doi:10.4230/LIPIcs.ITP.2022.20](https://doi.org/10.4230/LIPIcs.ITP.2022.20)

That paper proves in HOL4 that CakeML's L3 Armv8 model simulates Arm's
official Sail specification, then re-targets the CakeML compiler correctness
theorem. This project does the same for RISC-V in Lean: it proves that
Flapjack's port of the L3 RISC-V model simulates the Sail RISC-V model, then
transfers Flapjack's Pancake compiler theorem.

The per-instruction proof technique against the Lean Sail extraction is
modelled on [riscv-zkvm](https://github.com/Verified-zkEVM/riscv-zkvm).

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
