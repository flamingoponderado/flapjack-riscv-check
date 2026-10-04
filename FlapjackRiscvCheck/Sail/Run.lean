import FlapjackRiscvCheck.Models

/-!
# Running Sail computations

`runSail` exposes a `SailM` computation as a partial function on `SailState`,
with failure (`EStateM.Result.error`) as `none`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D Sail.ConcurrencyInterfaceV1

/-- Run a Sail computation; `none` on any Sail error (trap, assertion, unreachable). -/
def runSail {α : Type} (m : SailM α) (t : SailState) : Option (α × SailState) :=
  match m.run t with
  | .ok a t' => some (a, t')
  | .error _ _ => none

@[simp] theorem runSail_pure {α : Type} (a : α) (t : SailState) :
    runSail (pure a : SailM α) t = some (a, t) := rfl

theorem runSail_bind {α β : Type} (m : SailM α) (f : α → SailM β) (t : SailState) :
    runSail (m >>= f) t =
      match runSail m t with
      | some (a, t') => runSail (f a) t'
      | none => none := by
  unfold runSail
  simp only [EStateM.run, bind, EStateM.bind]
  cases m t <;> rfl

theorem runSail_bind_of_eq {α β : Type} {m : SailM α} {f : α → SailM β} {t t' : SailState}
    {a : α} (h : runSail m t = some (a, t')) :
    runSail (m >>= f) t = runSail (f a) t' := by
  rw [runSail_bind, h]

@[simp] theorem runSail_assert_true (msg : String) (t : SailState) :
    runSail (Sail.ConcurrencyInterfaceV1.PreSail.assert true msg : SailM Unit) t = some ((), t) :=
  rfl

end FlapjackRiscvCheck
