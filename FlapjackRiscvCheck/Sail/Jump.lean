import FlapjackRiscvCheck.Sail.RegsOther
import FlapjackRiscvCheck.Sail.Monad
import LeanRV64D.BaseInsts

/-!
# Sail `jump_to` with compressed instructions enabled
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

theorem runSail_currentlyEnabled_C {t : SailState} {m : BitVec 64}
    (hm : t.regs.get? Register.misa = some m) (hC : _get_Misa_C m = 1) :
    runSail (currentlyEnabled .Ext_C) t = some (true, t) := by
  rw [currentlyEnabled]
  simp [runSail, EStateM.run, EStateM.bind, EStateM.pure, PreSail.readReg, get, getThe,
    MonadStateOf.get, EStateM.get, hm, hC, hartSupports, bind, pure, Functions.not, Functions.xlen]

theorem runSail_currentlyEnabled_Zca {t : SailState} {m : BitVec 64}
    (hm : t.regs.get? Register.misa = some m) (hC : _get_Misa_C m = 1) :
    runSail (currentlyEnabled .Ext_Zca) t = some (true, t) := by
  rw [currentlyEnabled]
  rw [runSail_bind_of_eq (runSail_currentlyEnabled_C hm hC)]
  simp [hartSupports]

/-- With `misa.C = 1`, a jump to an even target sets `nextPC` and retires. -/
theorem runSail_jump_to {t : SailState} {m : BitVec 64}
    (hm : t.regs.get? Register.misa = some m) (hC : _get_Misa_C m = 1)
    (target : BitVec 64) (h0 : target.getLsbD 0 = false) :
    runSail (jump_to target) t =
      some (RETIRE_SUCCESS, { t with regs := t.regs.insert Register.nextPC target }) := by
  have h0' : (Sail.BitVec.access target 0 == 0#1) = true := by
    have : target[0] = false := by rw [← BitVec.getLsbD_eq_getElem]; exact h0
    simp [Sail.BitVec.access, this]
  unfold jump_to
  rw [SailME.run, runSail_SailME_run]
  simp only [ext_control_check_pc, ExceptT_run_lift_bind, h0']
  rw [runSail_bind_of_eq (show runSail (PreSail.assert true _) t = some ((), t) from rfl),
    runSail_bind_of_eq (runSail_currentlyEnabled_Zca hm hC)]
  simp only [Functions.not, Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false,
    ExceptT_run_lift_bind]
  rfl

end FlapjackRiscvCheck
