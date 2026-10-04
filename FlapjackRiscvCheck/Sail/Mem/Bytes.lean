import FlapjackRiscvCheck.Sail.Run

/-!
# Sail's byte-level memory

`readBytes n addr` reads `n` bytes little-endian from Sail's partial memory
map; `writeBytes` stores them. `leNat f n` is the little-endian number
spelled by the bytes `f 0, …, f (n-1)`.
-/

namespace FlapjackRiscvCheck

open LeanRV64D Sail.ConcurrencyInterfaceV1

/-- `Σ_{i<n} (f i).toNat * 256^i`. -/
def leNat (f : Nat → BitVec 8) : Nat → Nat
  | 0 => 0
  | n + 1 => (f 0).toNat + 256 * leNat (fun i => f (i + 1)) n

theorem runSail_readByte {t : SailState} {addr : Nat} {b : BitVec 8}
    (h : t.mem.get? addr = some b) :
    runSail (PreSail.readByte addr : SailM (BitVec 8)) t = some (b, t) := by
  rw [Std.ExtHashMap.get?_eq_getElem?] at h
  simp [runSail, PreSail.readByte, EStateM.run, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, bind, pure, EStateM.pure, h]

theorem runSail_readBytes (n : Nat) :
    ∀ (addr : Nat) (f : Nat → BitVec 8) (t : SailState),
      (∀ i < n, t.mem.get? (addr + i) = some (f i)) →
      ∃ v : BitVec (8 * n), v.toNat = leNat f n ∧
        runSail (PreSail.readBytes n addr : SailM (BitVec (8 * n) × Option Bool)) t =
          some ((v, none), t) := by
  induction n with
  | zero => intro addr f t _; exact ⟨default, by simp [leNat]; rfl, rfl⟩
  | succ n ih =>
    intro addr f t hf
    have h0 := runSail_readByte (hf 0 (by omega))
    simp only [Nat.add_zero] at h0
    cases n with
    | zero =>
      refine ⟨f 0, by simp [leNat], ?_⟩
      unfold PreSail.readBytes
      simp only [Nat.zero_add]
      rw [runSail_bind_of_eq h0]
      rfl
    | succ m =>
      obtain ⟨v, hv, hr⟩ := ih (addr + 1) (fun i => f (i + 1)) t
        (fun i hi => by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact hf (i + 1) (by omega))
      refine ⟨(v ++ f 0).cast (by omega), ?_, ?_⟩
      · simp only [BitVec.toNat_cast, BitVec.toNat_append, hv]
        rw [← Nat.shiftLeft_add_eq_or_of_lt (f 0).isLt, Nat.shiftLeft_eq]
        simp only [leNat]
        omega
      · simp only [PreSail.readBytes]
        rw [runSail_bind_of_eq h0, runSail_bind_of_eq hr]
        rfl

end FlapjackRiscvCheck
