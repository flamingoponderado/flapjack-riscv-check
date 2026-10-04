import FlapjackRiscvCheck.Sail.Monad

/-!
# Sail `for` loops whose body does nothing

Sail's `for i in [a:b]i` loops (`IntRange.forIn'`) running in `SailME`: if
every iteration yields `()` without changing the state, the loop returns `()`
and leaves the state unchanged.
-/

namespace FlapjackRiscvCheck

open LeanRV64D Sail.ConcurrencyInterfaceV1

theorem runSail_ExceptT_bind {ε α β : Type} (m : SailME ε α) (f : α → SailME ε β)
    (t : SailState) :
    runSail (ExceptT.run (m >>= f)) t =
      match runSail (ExceptT.run m) t with
      | some (.ok a, t') => runSail (ExceptT.run (f a)) t'
      | some (.error e, t') => some (.error e, t')
      | none => none := by
  rw [ExceptT.run_bind, runSail_bind]
  rcases runSail (ExceptT.run m) t with _ | ⟨_ | _, _⟩ <;> rfl

theorem IntRange_loop_noop {ε : Type} (r : IntRange)
    (f : (i : Int) → i ∈ r → Unit → SailME ε (ForInStep Unit)) (t : SailState)
    (hf : ∀ i h, runSail (ExceptT.run (f i h ())) t = some (.ok (.yield ()), t)) :
    ∀ (b : Unit) (i : Int) (hs : (i - r.start) % r.step = 0),
      runSail (ExceptT.run (IntRange.forIn'.loop r f b i hs)) t = some (.ok (), t) := by
  intro b i hs
  induction b, i, hs using IntRange.forIn'.loop.induct r with
  | case1 b i hs hmem ih =>
    rw [IntRange.forIn'.loop.eq_1, dif_pos hmem, runSail_ExceptT_bind, hf i hmem]
    exact ih ()
  | case2 b i hs hmem =>
    rw [IntRange.forIn'.loop.eq_1, dif_neg hmem]
    rfl

theorem runSail_forIn_IntRange_noop {ε : Type} (r : IntRange)
    (f : Int → Unit → SailME ε (ForInStep Unit)) (t : SailState)
    (hf : ∀ i, i ∈ r → runSail (ExceptT.run (f i ())) t = some (.ok (.yield ()), t)) :
    runSail (ExceptT.run (forIn r () f)) t = some (.ok (), t) := by
  show runSail (ExceptT.run (IntRange.forIn' r () (fun i _ b => f i b))) t = _
  unfold IntRange.forIn'
  exact IntRange_loop_noop r _ t (fun i h => hf i h) () _ _

end FlapjackRiscvCheck
