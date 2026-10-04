import FlapjackRiscvCheck.Sail.Mem.Inv

/-!
# Effective data addresses in machine mode

Under `SailMemInv`, `get_transformed_data_addr base offset` is just
`x[base] + offset`: no pointer masking and no translation.
-/

namespace FlapjackRiscvCheck

open LeanRV64D LeanRV64D.Functions Sail.ConcurrencyInterfaceV1

theorem pm_transform_PA_zero (a : BitVec 64) :
    pm_transform_PA (.Virtaddr a) 0 = .Virtaddr a := by
  simp only [pm_transform_PA, Sail.BitVec.extractLsb, zero_extend, Sail.BitVec.zeroExtend,
    Functions.xlen]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb_toNat]
  omega

theorem runSail_transform_effective_address {t : SailState} (h : SailMemInv t)
    (acc : MemoryAccessType mem_payload) (a : BitVec 64) :
    runSail (transform_effective_address (.Virtaddr a) acc) t = some (.Virtaddr a, t) := by
  unfold transform_effective_address
  rw [runSail_readReg_mstatus_priv h acc, runSail_bind_of_eq (runSail_get_pmlen h acc),
    runSail_bind_of_eq (runSail_translationMode_machine t)]
  rw [show ((0 : Int) : Nat) = 0 from rfl, pm_transform_PA_zero]
  rfl

theorem runSail_get_transformed_data_addr {t : SailState} (h : SailMemInv t)
    {n : BitVec 5} {x : BitVec 64} (hx : sailGpr t n = some x) (offset : BitVec 64)
    (acc : MemoryAccessType mem_payload) (w : Nat) :
    runSail (get_transformed_data_addr (.Regidx n) offset acc w) t =
      some (.Ext_DataAddr_OK (.Virtaddr (x + offset)), t) := by
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [bind_assoc, pure_bind]
  rw [runSail_bind_of_eq (runSail_rX_bits hx)]
  rw [runSail_bind_of_eq (runSail_transform_effective_address h acc _)]
  rfl

end FlapjackRiscvCheck
