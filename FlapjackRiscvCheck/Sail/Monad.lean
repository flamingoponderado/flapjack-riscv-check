import FlapjackRiscvCheck.Sail.Run

/-!
# Sail's early-return layer `SailME`

Sail functions with early `return` run in `SailME β = ExceptT (Error ⊕ β) SailM`
and are closed off by `PreSailME.run`. These lemmas push `runSail` through
that layer.
-/

namespace FlapjackRiscvCheck

open LeanRV64D Sail.ConcurrencyInterfaceV1

theorem runSail_SailME_run {α : Type} (m : SailME α α) (t : SailState) :
    runSail (PreSail.PreSailME.run m) t =
      match runSail (ExceptT.run m) t with
      | some (.ok a, t') => some (a, t')
      | some (.error (.inr e), t') => some (e, t')
      | some (.error (.inl _), _) => none
      | none => none := by
  unfold PreSail.PreSailME.run
  rw [runSail_bind]
  rcases h : runSail (ExceptT.run m) t with _ | ⟨_ | _, t'⟩
  · rfl
  · rename_i e; rcases e with e | e
    · rfl
    · rfl
  · rfl

theorem ExceptT_run_lift_bind {β α γ : Type} (x : SailM α) (f : α → SailME β γ) :
    ExceptT.run (monadLift x >>= f : SailME β γ) = x >>= fun a => ExceptT.run (f a) := by
  simp only [ExceptT.run_bind]
  show (ExceptT.lift x).run >>= _ = _
  simp [ExceptT.run_lift]

theorem ExceptT_run_lift {β α : Type} (x : SailM α) :
    ExceptT.run (monadLift x : SailME β α) = Except.ok <$> x := by
  show (ExceptT.lift x).run = _
  simp [ExceptT.run_lift]

theorem runSail_map {α β : Type} (f : α → β) (x : SailM α) (t : SailState) :
    runSail (f <$> x) t = (runSail x t).map (fun p => (f p.1, p.2)) := by
  unfold runSail
  simp only [EStateM.run, Functor.map, EStateM.map]
  cases x t <;> rfl

end FlapjackRiscvCheck
