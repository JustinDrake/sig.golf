import SigGolfCandidate.T3M.Sim

/-!
# T3M memory lemmas: frames, stored digests, `writeHash`, `BitVec.ofNat 64` arithmetic

* `pcOf k` : the pc of instruction `k`;
* `Frame s t W` : every doubleword outside the set `W` (byte addresses of doublewords) is
  unchanged from `s` to `t`; `Frame.trans` (union), `Frame.mono`, `Frame.get`;
* `DigAt t A d` : the 16-byte digest `d` is stored little-endian at `A`, `A + 8`
  (`DigAt.frame`, `DigAt.words`); `DigsAt t A ds` : `ds[i]` at `A + 16 i`;
* `writeHash` : registers and pc, the four written doublewords (`getMem_writeHash`,
  `Frame.writeHash`), the answer's halves (`DigAt.writeHash_lo/hi`);
* `ofNat_*` : `BitVec.ofNat 64` normal forms used to read symbolic-block results;
* `hashArgs_const` : HASH argument validity for constant buffers;
* `getMem_writeBytesAsWords` : the loader.
-/

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SphincsSecurity (bytesLE bytesLE_length)

/-- The pc of instruction `k`. -/
abbrev pcOf (k : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * k)

/-! ## `BitVec.ofNat 64` arithmetic -/

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem ofNat_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rwa [toNat_ofNat_lt hx, toNat_ofNat_lt hy] at this
  · rintro rfl; rfl

theorem ofNat_eq_iff (x y : Nat) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x % 18446744073709551616 = y % 18446744073709551616 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add8 (a : Nat) : BitVec.ofNat 64 a + (8 : Word) = BitVec.ofNat 64 (a + 8) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add8' (a : Nat) : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_shl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ofNat_shr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_shl' (a k : Nat) :
    BitVec.ofNat 64 a <<< ((BitVec.ofNat 64 k).toNat % 64) =
      BitVec.ofNat 64 (a * 2 ^ (k % 2 ^ 64 % 64)) := by
  rw [ofNat_shl, BitVec.toNat_ofNat]

theorem ofNat_shr' (a k : Nat) :
    BitVec.ofNat 64 a >>> ((BitVec.ofNat 64 k).toNat % 64) =
      BitVec.ofNat 64 (a % 2 ^ 64 / 2 ^ (k % 2 ^ 64 % 64)) := by
  rw [BitVec.toNat_ofNat, show BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 64) by
    apply BitVec.eq_of_toNat_eq; simp, ofNat_shr _ _ (Nat.mod_lt _ (by decide))]

/-- OR of a value with a low field it does not overlap. -/
theorem ofNat_or_add (a b k : Nat) (ha : a < 2 ^ k) :
    BitVec.ofNat 64 (b * 2 ^ k) ||| BitVec.ofNat 64 a = BitVec.ofNat 64 (b * 2 ^ k + a) := by
  have e1 : BitVec.ofNat 64 (b * 2 ^ k) = BitVec.ofNat 64 b <<< k := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hz : (BitVec.ofNat 64 b <<< k) &&& BitVec.ofNat 64 a = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases h : i < k
    · simp [h]
    · have : a.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  rw [e1, ← BitVec.add_eq_or_of_and_eq_zero _ _ hz, ← e1]
  apply BitVec.eq_of_toNat_eq; simp

/-- OR of two values with disjoint bits (`a < 2^k`, `b` a multiple of `2^k`). -/
theorem ofNat_or_disjoint (a b k : Nat) (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) :
    BitVec.ofNat 64 b ||| BitVec.ofNat 64 a = BitVec.ofNat 64 (b + a) := by
  have e : b = b / 2 ^ k * 2 ^ k := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)).symm
  rw [e, ofNat_or_add a (b / 2 ^ k) k ha]

/-- OR of two values with disjoint bits, the low field first. -/
theorem ofNat_or_disjoint' (a b k : Nat) (ha : a < 2 ^ k) (hb : b % 2 ^ k = 0) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.or_comm, ofNat_or_disjoint a b k ha hb, Nat.add_comm]

/-- Put the fixed tree index into the unused high half of the node tag word. -/
theorem hdr0_or_tree (tag lay tree : Nat) (ht : tree < 2^32) :
    BitVec.ofNat 64 (hdr0 tag lay tree 0) ||| (BitVec.ofNat 64 tree <<< 32) =
      BitVec.ofNat 64 (hdr0 tag lay tree tree) := by
  have hlo : hdr0 tag lay tree 0 < 2^32 := by
    unfold hdr0
    have htag := Nat.mod_lt tag (by decide : 0 < 256)
    have hlay := Nat.mod_lt lay (by decide : 0 < 256)
    rw [Nat.div_eq_of_lt ht]
    omega
  rw [ofNat_shl, ofNat_or_disjoint' (hdr0 tag lay tree 0) (tree * 2^32) 32 hlo (by omega)]
  congr 1
  unfold hdr0
  rw [Nat.mod_eq_of_lt ht]
  omega

theorem ofNat_and1 (i : Nat) : BitVec.ofNat 64 i &&& 1#64 = BitVec.ofNat 64 (i % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by norm_num), Nat.and_one_is_mod]
  omega

theorem ofNat_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a).slt (BitVec.ofNat 64 b) = decide (a < b) := by
  have h1 : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
    rw [BitVec.msb_eq_decide]; simp; omega
  have h2 : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.slt, h1, h2]
  simp

/-! ## Frames -/

/-- Every doubleword outside `W` (a set of byte addresses) is unchanged from `s` to `t`. -/
def Frame (s t : MachineState) (W : Nat → Prop) : Prop :=
  ∀ A < 2 ^ 64, ¬ W A → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)

theorem Frame.refl (s : MachineState) (W : Nat → Prop) : Frame s s W := fun _ _ _ => rfl

theorem Frame.trans {s t u : MachineState} {W₁ W₂ : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) : Frame s u (fun A => W₁ A ∨ W₂ A) := by
  intro A hA hne
  rw [h₂ A hA (fun h => hne (Or.inr h)), h₁ A hA (fun h => hne (Or.inl h))]

theorem Frame.mono {s t : MachineState} {W W' : Nat → Prop} (h : Frame s t W)
    (hW : ∀ A, A < 2 ^ 64 → W A → W' A) : Frame s t W' :=
  fun A hA hn => h A hA (fun hw => hn (hW A hA hw))

theorem Frame.get {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {A : Nat} (hA : A < 2 ^ 64)
    (hn : ¬ W A) : t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := h A hA hn

/-! ## Stored digests -/

/-- The 16-byte digest `d` is stored little-endian at `A`, `A + 8`. -/
def DigAt (t : MachineState) (A : Nat) (d : BitVec 128) : Prop :=
  t.getMem (BitVec.ofNat 64 A) = d.extractLsb' 0 64 ∧ t.getMem (BitVec.ofNat 64 (A + 8)) = d.extractLsb' 64 64

theorem DigAt.frame {s t : MachineState} {W : Nat → Prop} {A : Nat} {d : BitVec 128} (h : DigAt s A d)
    (hf : Frame s t W) (hA : A + 8 < 2 ^ 64) (h0 : ¬ W A) (h1 : ¬ W (A + 8)) : DigAt t A d :=
  ⟨(hf A (by omega) h0).trans h.1, (hf (A + 8) hA h1).trans h.2⟩

theorem DigAt.words {t : MachineState} {A : Nat} {d : BitVec 128} (h : DigAt t A d) :
    t.readWords (BitVec.ofNat 64 A) 2 = wordsOf (bytesLE 16 d) := by
  rw [readWords_two, h.1, h.2, wordsOf_bytesLE16]

theorem DigAt.congr {t : MachineState} {A : Nat} {d e : BitVec 128} (h : DigAt t A d) (he : d = e) :
    DigAt t A e := he ▸ h

/-- Digests `ds[i]` stored at `A + 16 i`. -/
def DigsAt (t : MachineState) (A : Nat) (ds : List (BitVec 128)) : Prop :=
  ∀ i < ds.length, DigAt t (A + 16 * i) (ds.getD i 0)

theorem DigsAt.nil (t : MachineState) (A : Nat) : DigsAt t A [] := fun i hi => by simp at hi

theorem DigsAt.snoc {t : MachineState} {A : Nat} {ds : List (BitVec 128)} {d : BitVec 128}
    (h : DigsAt t A ds) (hd : DigAt t (A + 16 * ds.length) d) : DigsAt t A (ds ++ [d]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hlt : i < ds.length
  · have := h i hlt
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using this
  · have : i = ds.length := by omega
    subst this
    simpa [List.getD_eq_getElem?_getD] using hd

theorem DigsAt.frame {s t : MachineState} {W : Nat → Prop} {A : Nat} {ds : List (BitVec 128)}
    (h : DigsAt s A ds) (hf : Frame s t W) (hA : A + 16 * ds.length < 2 ^ 64)
    (hW : ∀ B, A ≤ B → B < A + 16 * ds.length → ¬ W B) : DigsAt t A ds := by
  intro i hi
  exact (h i hi).frame hf (by omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

theorem DigsAt.get {t : MachineState} {A : Nat} {ds : List (BitVec 128)} (h : DigsAt t A ds) {i : Nat}
    (hi : i < ds.length) : DigAt t (A + 16 * i) (ds.getD i 0) := h i hi

/-- A buffer of stored digests as doublewords. -/
theorem DigsAt.words {t : MachineState} {A : Nat} {ds : List (BitVec 128)} (h : DigsAt t A ds) :
    t.readWords (BitVec.ofNat 64 A) (2 * ds.length) = wordsOf (ds.flatMap (bytesLE 16)) := by
  induction ds using List.reverseRecOn with
  | nil => rfl
  | append_singleton ds d ih =>
    have h1 : DigsAt t A ds := fun i hi => by
      have := h i (by simp; omega)
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using this
    have h2 : DigAt t (A + 16 * ds.length) d := by
      have := h ds.length (by simp)
      simpa [List.getD_eq_getElem?_getD] using this
    rw [List.length_append, List.length_singleton, show 2 * (ds.length + 1) = 2 * ds.length + 2 by ring,
      readWords_add, ih h1, List.flatMap_append, wordsOf_append _ _ (by
        rw [List.length_flatMap]; simp [bytesLE_length]; omega),
      show A + 8 * (2 * ds.length) = A + 16 * ds.length by ring, h2.words]
    simp

/-! ## `writeHash` -/

@[simp] theorem getReg_setMem' (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := by cases r <;> rfl

@[simp] theorem getReg_writeHash (t : MachineState) (a : BitVec 256) (r : Reg) :
    (writeHash t a).getReg r = t.getReg r := by
  simp [writeHash]

@[simp] theorem pc_writeHash (t : MachineState) (a : BitVec 256) :
    (writeHash t a).pc = t.pc + 4 := by
  simp [writeHash, MachineState.setPC]

theorem getMem_writeHash (t : MachineState) (a : BitVec 256) (B A : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hA : A < 2 ^ 64) :
    (writeHash t a).getMem (BitVec.ofNat 64 A) =
      if A = B then a.extractLsb' 0 64 else if A = B + 8 then a.extractLsb' 64 64
      else if A = B + 16 then a.extractLsb' 128 64 else if A = B + 24 then a.extractLsb' 192 64
      else t.getMem (BitVec.ofNat 64 A) := by
  simp only [writeHash, h12, MachineState.writeWords_cons, MachineState.writeWords_nil,
    ofNat_add8, MachineState.getMem_setPC]
  simp only [MachineState.getMem, MachineState.setMem, beq_iff_eq,
    ofNat_inj hA (by omega : B + 8 + 8 + 8 < 2 ^ 64), ofNat_inj hA (by omega : B + 8 + 8 < 2 ^ 64),
    ofNat_inj hA (by omega : B + 8 < 2 ^ 64), ofNat_inj hA (by omega : B < 2 ^ 64)]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- `writeHash` writes exactly the 32 bytes at `x12`. -/
theorem Frame.writeHash (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := by
  intro A hA hne
  rw [getMem_writeHash t a B A h12 hB hA, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- The low 16 bytes of the answer (`shortHash`, `privatePair.1`, `mask`) at `x12`. -/
theorem DigAt.writeHash_lo (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    DigAt (writeHash t a) B (a.extractLsb' 0 128) := by
  constructor
  · rw [getMem_writeHash t a B B h12 hB (by omega), if_pos rfl]
    simp
  · rw [getMem_writeHash t a B (B + 8) h12 hB (by omega), if_neg (by omega), if_pos rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega

/-- The high 16 bytes of the answer (`privatePair.2`) at `x12 + 16`. -/
theorem DigAt.writeHash_hi (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    DigAt (writeHash t a) (B + 16) (a.extractLsb' 128 128) := by
  constructor
  · rw [getMem_writeHash t a B (B + 16) h12 hB (by omega), if_neg (by omega), if_neg (by omega),
      if_pos rfl]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  · rw [getMem_writeHash t a B (B + 16 + 8) h12 hB (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_pos (by omega)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega

/-- The full answer at `x12` (the MAC tag). -/
theorem readWords_writeHash (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    (writeHash t a).readWords (BitVec.ofNat 64 B) 4 = wordsOf (bytesLE 32 a) := by
  rw [wordsOf_bytesLE32, show (4 : Nat) = 2 + 2 from rfl, readWords_add, readWords_two, readWords_two,
    getMem_writeHash t a B B h12 hB (by omega), getMem_writeHash t a B (B + 8) h12 hB (by omega),
    getMem_writeHash t a B (B + 8 * 2) h12 hB (by omega),
    getMem_writeHash t a B (B + 8 * 2 + 8) h12 hB (by omega)]
  simp only [if_neg (show ¬ B + 8 = B by omega), if_neg (show ¬ B + 8 * 2 = B by omega),
    if_neg (show ¬ B + 8 * 2 = B + 8 by omega), if_neg (show ¬ B + 8 * 2 + 8 = B by omega),
    if_neg (show ¬ B + 8 * 2 + 8 = B + 8 by omega), if_neg (show ¬ B + 8 * 2 + 8 = B + 16 by omega)]
  simp

/-! ## HASH arguments -/

theorem hashArgs_const (t : MachineState) (a b c : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 b) (h12 : t.getReg .x12 = BitVec.ofNat 64 c)
    (ha : a % 8 = 0) (hb : 0 < b ∧ b % 64 = 0) (hab : a + b ≤ 2 ^ 24) (hc : c % 8 = 0)
    (hc' : c + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true := by
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, MEMORY_BYTES,
    Bool.and_eq_true, decide_eq_true_eq, toNat_ofNat_lt (by omega : a < 2 ^ 64),
    toNat_ofNat_lt (by omega : b < 2 ^ 64), toNat_ofNat_lt (by omega : c < 2 ^ 64)]
  omega

/-! ## The loader -/

theorem getMem_setMem_ofNat (s : MachineState) (B A : Nat) (w : Word) (hB : B < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    (s.setMem (BitVec.ofNat 64 B) w).getMem (BitVec.ofNat 64 A) =
      if A = B then w else s.getMem (BitVec.ofNat 64 A) := by
  simp only [MachineState.getMem, MachineState.setMem, beq_iff_eq, ofNat_inj hA hB]

theorem getMem_writeBytesAsWords (l : List (BitVec 8)) : ∀ (s : MachineState) (base A : Nat),
    base + 8 * ((l.length + 7) / 8) < 2 ^ 64 → A < 2 ^ 64 →
    (s.writeBytesAsWords (BitVec.ofNat 64 base) l).getMem (BitVec.ofNat 64 A) =
      if base ≤ A ∧ A < base + 8 * ((l.length + 7) / 8) ∧ (A - base) % 8 = 0 then
        bytesToWordLE ((l.drop (A - base)).take 8)
      else s.getMem (BitVec.ofNat 64 A) := by
  induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length) with
  | hwf => exact (measure List.length).wf
  | h l ih =>
    intro s base A hlen hA
    match l with
    | [] => simp only [MachineState.writeBytesAsWords_nil, List.length_nil]; rw [if_neg (by omega)]
    | b :: bs =>
      unfold MachineState.writeBytesAsWords
      simp only
      simp only [List.length_cons] at hlen
      rw [ofNat_add8, ih _ (by simp only [List.length_drop, List.length_cons]; omega) _ (base + 8) A
        (by simp only [List.length_drop, List.length_cons]; omega) hA,
        getMem_setMem_ofNat _ _ _ _ (by omega) hA]
      simp only [List.length_drop, List.length_cons]
      by_cases h1 : A = base
      · subst h1
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
        simp
      · by_cases h2 : base + 8 ≤ A ∧ A < base + 8 + 8 * ((bs.length + 1 - 8 + 7) / 8) ∧
            (A - (base + 8)) % 8 = 0
        · rw [if_pos h2, if_pos (by omega), List.drop_drop]
          congr 3; omega
        · rw [if_neg h2, if_neg h1, if_neg]
          omega

/-! ## Code placement and rebased block results -/

/-- A segment inside a placed code list. -/
theorem CodeAt.drop_prefix {image : Image} {pc : Word} {pre seg post : List (BitVec 32)}
    (h : CodeAt image pc (pre ++ seg ++ post)) :
    CodeAt image (pc + BitVec.ofNat 64 (4 * pre.length)) seg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.length_append] at h3
  have hpc : (pc + BitVec.ofNat 64 (4 * pre.length)).toNat = pc.toNat + 4 * pre.length := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 4 * pre.length) (by omega)]
    omega
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (pc.toNat + 4 * pre.length - 0x1000) / 4 = (pc.toNat - 0x1000) / 4 + pre.length by omega,
    ← List.drop_drop]
  obtain ⟨t, ht⟩ := h4
  rw [← ht]
  exact ⟨post ++ t, by simp⟩

/-- A segment of a layout placed at base `b`. -/
theorem codeAt_sublayout {image : Image} {b : Nat} {L : Rv.Layout}
    (hc : CodeAt image (pcOf b) (layoutCode L)) (hok : layoutOk 0 L = true) {i o : Nat}
    {seg : List (BitVec 32)} (hi : L[i]? = some (o, seg)) :
    CodeAt image (pcOf (b + o)) seg := by
  obtain ⟨pre, post, h1, h2⟩ := layout_split L 0 i o seg hok hi
  rw [h1] at hc
  have := CodeAt.drop_prefix hc
  have hlen : pre.length = o := by omega
  rw [hlen, ofNat_add_ofNat] at this
  rwa [pcOf, show 0x1000 + 4 * (b + o) = 0x1000 + 4 * b + 4 * o by ring]

/-- Re-target a block's final pc: a branch gets the targets `t1` (taken) and `t2`; any other
result the constant `t1`. -/
def rebase (e : E) (t1 t2 : Word) : E :=
  match e with
  | .ite op x y _ _ => .ite op x y (.c t1) (.c t2)
  | _ => .c t1

/-! ## Register frames -/

/-- Every register outside `l` is unchanged from `s` to `t`. -/
def RegsExcept (s t : MachineState) (l : List Reg) : Prop := ∀ r, r ∉ l → t.getReg r = s.getReg r

theorem RegsExcept.refl (s : MachineState) (l : List Reg) : RegsExcept s s l := fun _ _ => rfl

theorem RegsExcept.trans {s t u : MachineState} {l₁ l₂ : List Reg} (h₁ : RegsExcept s t l₁)
    (h₂ : RegsExcept t u l₂) : RegsExcept s u (l₁ ++ l₂) := by
  intro r hr
  rw [List.mem_append, not_or] at hr
  rw [h₂ r hr.2, h₁ r hr.1]

theorem RegsExcept.mono {s t : MachineState} {l l' : List Reg} (h : RegsExcept s t l)
    (hl : ∀ r ∈ l, r ∈ l') : RegsExcept s t l' := fun r hr => h r (fun hm => hr (hl r hm))

theorem RegsExcept.get {s t : MachineState} {l : List Reg} (h : RegsExcept s t l) {r : Reg}
    (hr : r ∉ l) : t.getReg r = s.getReg r := h r hr

/-- Normalization of symbolic-block results (`Result.toState` reads) to `BitVec.ofNat 64` terms. -/
macro "t3n" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, ofNat_add_ofNat, ofNat_shl', ofNat_shr', ofNat_eq_iff,
      BitVec.toNat_ofNat, accessValid_iff, MEMORY_BYTES, ne_eq, bne_iff_ne, decide_eq_true_eq,
      ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, ofNat_shl, $ts',*])

/-- Return addresses (pcs of instructions) are even: `jalr` lands on them exactly. -/
theorem pcOf_and_not1 (k : Nat) : pcOf k &&& ~~~1#64 = pcOf k := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [pcOf, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_ofNat, hj, decide_true,
    Bool.true_and]
  rcases j with _ | j
  · have : (0x1000 + 4 * k).testBit 0 = false := by
      rw [Nat.testBit_zero]; simp; omega
    simp [this]
  · have : (1 : Nat).testBit (j + 1) = false := by
      rw [Nat.testBit_succ]; simp
    simp [this]

@[simp] theorem pcOf_and_max (k : Nat) : pcOf k &&& 18446744073709551614#64 = pcOf k :=
  pcOf_and_not1 k

theorem pcOf_add4 (k : Nat) : pcOf k + 4 = pcOf (k + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat, show (4 : Word).toNat = 4 from rfl]
  omega

theorem readWords_eight (t : MachineState) (B : Nat) :
    t.readWords (BitVec.ofNat 64 B) 8 =
      [t.getMem (BitVec.ofNat 64 B), t.getMem (BitVec.ofNat 64 (B + 8)),
        t.getMem (BitVec.ofNat 64 (B + 16)), t.getMem (BitVec.ofNat 64 (B + 24)),
        t.getMem (BitVec.ofNat 64 (B + 32)), t.getMem (BitVec.ofNat 64 (B + 40)),
        t.getMem (BitVec.ofNat 64 (B + 48)), t.getMem (BitVec.ofNat 64 (B + 56))] := by
  rw [show (8 : Nat) = 2 + 2 + 2 + 2 from rfl, readWords_add, readWords_add, readWords_add,
    readWords_two, readWords_two, readWords_two, readWords_two]
  simp only [List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]

/-- One `lbu rd, off(rs)` step (bytes need no alignment; the symbolic executor's sub-doubleword
path needs an 8-aligned base, so unaligned symbolic byte loads are stepped by hand). -/
theorem steps_lbu {image : Image} {s : MachineState} {pc : Word} {w : BitVec 32}
    (hc : CodeAt image pc [w]) (hpc : s.pc = pc) {rd rs : Reg} {off : BitVec 12}
    (hdec : decodeInstruction w = some (.base (.LBU rd rs off)))
    (hv : accessValid (s.getReg rs + signExtend12 off) 1 = true) :
    Steps image s 1 1 ((s.setReg rd ((s.getByte (s.getReg rs + signExtend12 off)).zeroExtend 64)).setPC
      (s.pc + 4)) := by
  have hf : fetch image s = some (.base (.LBU rd rs off)) := (hc.fetch s hpc).trans hdec
  have hcl : classify (.base (.LBU rd rs off)) = some (.load .bu rd rs (signExtend12 off)) := rfl
  have hs : ordinaryStep s (.base (.LBU rd rs off)) =
      some ((s.setReg rd ((s.getByte (s.getReg rs + signExtend12 off)).zeroExtend 64)).setPC
        (s.pc + 4)) := by
    rw [classify_sound hcl]
    simp only [Micro.exec, LoadKind.width, hv, if_true, LoadKind.read]
  exact Steps.of_eq (Steps.step hf hs (Steps.refl _)) rfl rfl

theorem getByte_eq_word (t : MachineState) (a : Nat) (ha : a < 2 ^ 64) :
    t.getByte (BitVec.ofNat 64 a) = extractByte (t.getMem (BitVec.ofNat 64 (a / 8 * 8))) (a % 8) := by
  unfold MachineState.getByte
  rw [byteOffset_eq, toNat_ofNat_lt ha]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega)]
  omega

/-- A byte inside an unchanged doubleword is unchanged. -/
theorem Frame.getByte {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {a : Nat} (ha : a < 2 ^ 64)
    (hn : ¬ W (a / 8 * 8)) : t.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := by
  rw [getByte_eq_word t a ha, getByte_eq_word s a ha, h.get (by omega) hn]

end SigGolfCandidate.T3M
