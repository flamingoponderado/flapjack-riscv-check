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

/-- Insert a list of `(address, byte)` pairs into the memory map, left to right. -/
def insertAll (m : Std.ExtHashMap Nat (BitVec 8)) (l : List (Nat × BitVec 8)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  l.foldl (fun m p => m.insert p.1 p.2) m

theorem runSail_forM_writeByte (l : List (Nat × BitVec 8)) :
    ∀ t : SailState, runSail (List.forM l (fun (p : Nat × BitVec 8) =>
        (PreSail.writeByte p.1 p.2 : SailM PUnit))) t =
      some (⟨⟩, { t with mem := insertAll t.mem l }) := by
  induction l with
  | nil => intro t; rfl
  | cons p l ih =>
    intro t
    show runSail (PreSail.writeByte p.1 p.2 >>= fun _ => List.forM l _) t = _
    rw [runSail_bind_of_eq (show runSail (PreSail.writeByte p.1 p.2 : SailM PUnit) t =
      some (⟨⟩, { t with mem := t.mem.insert p.1 p.2 }) from rfl), ih]
    rfl

theorem lookup_none_of_not_mem (l : List (Nat × BitVec 8)) (a : Nat)
    (h : a ∉ l.map Prod.fst) : l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rcases p with ⟨x, y⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have : (a == x) = false := by simpa [beq_iff_eq] using h.1
    simp [List.lookup_cons, this, ih h.2]

theorem insertAll_get? (l : List (Nat × BitVec 8)) (hnd : (l.map Prod.fst).Nodup) :
    ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat),
      (insertAll m l).get? k = (l.lookup k).or (m.get? k) := by
  induction l with
  | nil => intro m k; simp [insertAll]
  | cons p l ih =>
    intro m k
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [insertAll, List.foldl_cons] at ih ⊢
    rw [ih hnd.2]
    rcases p with ⟨a, b⟩
    simp only [List.lookup_cons, Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
    by_cases hk : a = k
    · subst hk
      simp [lookup_none_of_not_mem l a hnd.1]
    · have : (k == a) = false := by simpa [beq_iff_eq] using Ne.symm hk
      simp [hk, this]

theorem ofFn_addr_shift (n addr : Nat) (g : Nat → BitVec 8) :
    List.ofFn (fun i : Fin (n + 1) => (addr + i.val, g i.val)) =
      (addr, g 0) :: List.ofFn (fun i : Fin n => (addr + 1 + i.val, g (i.val + 1))) := by
  rw [List.ofFn_succ]
  simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ]
  congr 2
  funext i
  congr 1
  omega

theorem lookup_ofFn (n : Nat) : ∀ (addr : Nat) (g : Nat → BitVec 8) (k : Nat),
    (List.ofFn (fun i : Fin n => (addr + i.val, g i.val))).lookup k =
      if addr ≤ k ∧ k < addr + n then some (g (k - addr)) else none := by
  induction n with
  | zero => intro addr g k; simp
  | succ n ih =>
    intro addr g k
    rw [ofFn_addr_shift, List.lookup_cons]
    simp only [ih (addr + 1) (fun j => g (j + 1))]
    by_cases hk : k = addr
    · subst hk; simp
    · have : (k == addr) = false := by simpa [beq_iff_eq] using hk
      simp only [this]
      by_cases hr : addr + 1 ≤ k ∧ k < addr + 1 + n
      · rw [if_pos hr, if_pos (by omega)]
        congr 2; omega
      · rw [if_neg hr, if_neg (by omega)]

theorem nodup_ofFn_addr (n : Nat) : ∀ (addr : Nat) (g : Nat → BitVec 8),
    ((List.ofFn (fun i : Fin n => (addr + i.val, g i.val))).map Prod.fst).Nodup := by
  induction n with
  | zero => intro addr g; simp
  | succ n ih =>
    intro addr g
    rw [ofFn_addr_shift, List.map_cons, List.nodup_cons]
    refine ⟨?_, ih (addr + 1) (fun j => g (j + 1))⟩
    intro hmem
    obtain ⟨⟨x, y⟩, hx, hxa⟩ := List.mem_map.mp hmem
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hx
    simp only [Prod.mk.injEq] at hi
    simp only at hxa
    omega

/-- The `(address, byte)` list that `writeBytes addr value` stores. -/
def writeList {n : Nat} (addr : Nat) (value : BitVec (8 * n)) : List (Nat × BitVec 8) :=
  List.ofFn (fun i : Fin n => (addr + i.val, value.extractLsb' (8 * i.val) 8))

theorem runSail_writeBytes {n : Nat} (addr : Nat) (value : BitVec (8 * n)) (t : SailState) :
    runSail (PreSail.writeBytes addr value : SailM Bool) t =
      some (true, { t with mem := insertAll t.mem (writeList addr value) }) := by
  unfold PreSail.writeBytes
  rw [runSail_bind_of_eq (runSail_forM_writeByte _ t)]
  rfl

/-- After `writeBytes addr value`, byte `k` is byte `k - addr` of `value` inside the written
range and unchanged outside it. -/
theorem writeBytes_get? {n : Nat} (addr : Nat) (value : BitVec (8 * n))
    (m : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) :
    (insertAll m (writeList addr value)).get? k = if addr ≤ k ∧ k < addr + n then some (value.extractLsb' (8 * (k - addr)) 8)
        else m.get? k := by
  unfold writeList
  rw [insertAll_get? _ (nodup_ofFn_addr n addr (fun j => value.extractLsb' (8 * j) 8)),
    lookup_ofFn n addr (fun j => value.extractLsb' (8 * j) 8)]
  split <;> simp

end FlapjackRiscvCheck
