import FlapjackRiscvCheck.Sail.DecodePrefixDef

/-!
# Sail's decoder is its first blocks followed by the rest

`encdec_backwards` agrees with `decodePrefix tail` for the remaining decoder
`tail`. Checked by unification, so the full 56k-line decoder is never
traversed by tactics: decode proofs work against `decodePrefix` with an
abstract `tail`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions

set_option maxRecDepth 100000 in
theorem encdec_backwards_prefix :
    ∃ tail : BitVec 32 → SailM instruction, ∀ w, encdec_backwards w = decodePrefix tail w :=
  ⟨_, fun _ => rfl⟩

end FlapjackRiscvCheck
