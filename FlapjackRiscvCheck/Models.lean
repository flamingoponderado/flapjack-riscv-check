import Flapjack.RiscV.L3.Step.Next
import LeanRV64D.Step

/-!
# The two RISC-V models under comparison

* `L3State` / `l3Next`: Flapjack's port of the HOL4 L3 RISC-V model
  (`HOL/examples/l3-machine-code/riscv`), the semantics the Flapjack compiler
  correctness theorem is stated against.
* `SailState` / `sailStep`: the Lean extraction of the Sail RISC-V model
  (`LeanRV64D`), the RISC-V International golden model.
-/

namespace FlapjackRiscvCheck

/-- Flapjack's L3 machine state. -/
abbrev L3State := Flapjack.RiscV.L3.riscv_state

/-- One L3 step (`NextRISCV`); `none` when an exception or trap is raised. -/
noncomputable abbrev l3Next : L3State → Option L3State :=
  Flapjack.RiscV.L3.Step.NextRISCV

/-- The sequential state the Sail monad `LeanRV64D.SailM` runs over. -/
abbrev SailState :=
  Sail.ConcurrencyInterfaceV1.SequentialState LeanRV64D.RegisterType
    Sail.ConcurrencyInterfaceV1.trivialChoiceSource

/-- One Sail step through the model's own top-level stepper. -/
noncomputable abbrev sailTryStep (stepNo : Nat) : LeanRV64D.SailM Bool :=
  LeanRV64D.Functions.try_step stepNo false

end FlapjackRiscvCheck
