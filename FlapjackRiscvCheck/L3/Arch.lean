import Flapjack.RiscV.L3.Defs.IntegerLoadMode

/-!
# L3 in 64-bit mode

With `mcpuid.ArchBase = 2` (required by Flapjack's `riscvOk`), `in32BitMode`
is `false` and leaves the state unchanged.
-/

namespace FlapjackRiscvCheck

open Flapjack.RiscV.L3

theorem l3_in32BitMode_of_rv64 {s : riscv_state} (h : (MCSR s).mcpuid.ArchBase = 2) :
    in32BitMode () s = (false, s) := by
  simp [in32BitMode, curArch, architecture, h]

end FlapjackRiscvCheck
