import SigGolfCandidate.T3M.Verify.Judg
import SigGolfCandidate.T3M.Mem
import SigGolfCandidate.T3M.Witness.VerifyP

/-!
# Doublewords of the verify image's hash inputs and of the witness

* `dlo d`, `dhi d` : the two little-endian doublewords of a 16-byte digest;
* `wword w j` : witness doubleword `j` (bytes `8 j .. 8 j + 8`; **zero past the witness**, as the machine's
  memory after `WIT + W` during verify), `wdig_lo`, `wdig_hi` (`wdig w (8 j)` = `wword w j`, `wword w (j+1)`);
* `blk4 a b c d` : a 64-byte block of four 16-byte fields, `wordsOf_blk4`, `pad64_blk4`, `blocks_blk4`;
* Core's and `verifyP`'s formats as `blk4` (`ftsLeafP_eq`, `nodeHashP_eq`, `nodeHash_eq`, `chainInputP_eq`) and the
  doublewords of the other inputs: `wordsOf_digestInput`, `wordsOf_encodingInput`, `wordsOf_forestInput`,
  `wordsOf_pad64` (for `leafHash`);
* `hashInput_words8` : a one-block HASH input given by its eight doublewords (`hashInput_toQ` of M0 at `n = 0`).
-/

namespace SigGolfCandidate.T3M.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3 (header pad64 zero16 Digest HashOutput HashInput Layer)
open SphincsSecurity (bytesLE bytesLE_length)

/-! ## Digests and witness words -/

/-- Low doubleword of a digest. -/
abbrev dlo (d : BitVec 128) : Word := d.extractLsb' 0 64
/-- High doubleword of a digest. -/
abbrev dhi (d : BitVec 128) : Word := d.extractLsb' 64 64

/-- Witness doubleword `j` (zero for `8 j ≥ 25240`). -/
def wword (w : WBytes) (j : Nat) : Word := w.extractLsb' (64 * j) 64

theorem wword_toNat (w : WBytes) (j : Nat) : (wword w j).toNat = w.toNat / 2 ^ (64 * j) % 2 ^ 64 := by
  simp only [wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem wword_zero (w : WBytes) (j : Nat) (h : 3155 ≤ j) : wword w j = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [wword_toNat]
  have hw : w.toNat < 2 ^ (64 * j) :=
    lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.div_eq_of_lt hw]; rfl

theorem wdig_lo (w : WBytes) (j : Nat) : dlo (wdig w (8 * j)) = wword w j := by
  apply BitVec.eq_of_toNat_eq
  simp only [wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show 8 * (8 * j) = 64 * j by ring, Nat.mod_mod_of_dvd _ (by norm_num)]

theorem wdig_hi (w : WBytes) (j : Nat) : dhi (wdig w (8 * j)) = wword w (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [wdig, wword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add, show 8 * (8 * j) + 64 = 64 * (j + 1) by ring, Nat.mod_mod]

/-- The digest stored at witness offset `8 j`. -/
theorem wdig_words (w : WBytes) (j : Nat) :
    wordsOf (bytesLE 16 (wdig w (8 * j))) = [wword w j, wword w (j + 1)] := by
  rw [wordsOf_bytesLE16, ← wdig_lo, ← wdig_hi]

/-! ## Blocks of four 16-byte fields -/

/-- A 64-byte block `[a | b | c | d]`. -/
def blk4 (a b c d : BitVec 128) : List UInt8 := bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d

theorem blk4_length (a b c d : BitVec 128) : (blk4 a b c d).length = 64 := by
  simp only [blk4, List.length_append, bytesLE_length]

theorem pad64_blk4 (a b c d : BitVec 128) : pad64 (blk4 a b c d) = blk4 a b c d :=
  pad64_of_aligned _ (by rw [blk4_length])

theorem wordsOf_blk4 (a b c d : BitVec 128) :
    wordsOf (blk4 a b c d) = [dlo a, dhi a, dlo b, dhi b, dlo c, dhi c, dlo d, dhi d] := by
  unfold blk4
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl

theorem aligned_blk4 (a b c d : BitVec 128) : Aligned (blk4 a b c d) := by
  rw [Aligned, blk4_length]; omega

theorem blocks_blk4 (a b c d : BitVec 128) : (toQ (pad64 (blk4 a b c d))).blocks = 1 := by
  rw [pad64_blk4, blocks_toQ (aligned_blk4 a b c d), blk4_length]

/-- `bytesLE 16 0` is Core's `zero16`. -/
theorem bytesLE16_zero : bytesLE 16 (0 : BitVec 128) = zero16 := by decide

/-! ## Formats as blocks -/

theorem ftsLeafP_eq (index coord leaf : Nat) (pad0 secret pad1 : Digest) :
    T3M.ftsLeafP index coord leaf pad0 secret pad1 =
      T3.shortHash (blk4 pad0 (header 9 coord index 0 leaf) secret pad1) := rfl

theorem nodeHashP_eq (tag lay tree heap : Nat) (left pad right : Digest) :
    T3M.nodeHashP tag lay tree heap left pad right =
      T3.shortHash (blk4 left (header tag lay tree 0 heap) pad right) := rfl

theorem nodeHash_eq (tag lay tree heap : Nat) (left right : Digest) :
    T3.nodeHash tag lay tree heap left right =
      T3.shortHash (blk4 left (header tag lay tree 0 heap) 0 right) := by
  unfold T3.nodeHash blk4
  rw [bytesLE16_zero]

theorem ftsLeaf_eq (index coord leaf : Nat) (secret : Digest) :
    T3.ftsLeaf index coord leaf secret = T3.shortHash (blk4 0 (header 9 coord index 0 leaf) secret 0) := by
  unfold T3.ftsLeaf blk4
  rw [bytesLE16_zero]

theorem chainInputP_eq (lay : Layer) (tree leaf i step : Nat) (pad0 pad1 value : Digest) :
    T3M.chainInputP lay tree leaf i step pad0 pad1 value =
      blk4 pad0 (header 1 lay.val tree (step + 256 * i) leaf) pad1 value := rfl

/-! ## Other inputs -/

/-- The digest block `[rho | T(12, dc) | m]`. -/
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, bytesLE_length]

theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.digestInput rho m c) =
      [dlo rho, dhi rho, BitVec.ofNat 64 (hdr0 12 0 0 0), BitVec.ofNat 64 (hdr1 0 c.toNat),
        m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64, m.extractLsb' 192 64] := by
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_bytesLE32]
  rfl

theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    pad64 (T3.digestInput rho m c) = T3.digestInput rho m c :=
  pad64_of_aligned _ (by rw [digestInput_length])

theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]

/-- The encoding block `[L | T(4) | LE32 c | pad | R]` (E8: one full block, `pad64` is the identity). -/
theorem encodingInput_length' (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    (T3.encodingInput lay tree leaf msg c).length = 64 := by
  simp only [T3.encodingInput, List.length_append, bytesLE_length]

theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    pad64 (T3.encodingInput lay tree leaf msg c) = T3.encodingInput lay tree leaf msg c :=
  pad64_of_aligned _ (by rw [encodingInput_length'])

theorem readLE_bytesLE4_pad (c : BitVec 32) : T3.readLE (bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
  simp

theorem readLE_ctr_pad (c : BitVec 32) (p : BitVec 96) :
    T3.readLE (bytesLE 4 c ++ bytesLE 12 p) = c.toNat + 4294967296 * p.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_bytesLE, bytesLE_length]
  norm_num

theorem wordsOf_ctr_pad (c : BitVec 32) (p : BitVec 96) :
    wordsOf (bytesLE 4 c ++ bytesLE 12 p) =
      [BitVec.ofNat 64 (c.toNat + 2 ^ 32 * (p.toNat % 2 ^ 32)), BitVec.ofNat 64 (p.toNat / 2 ^ 32)] := by
  rw [wordsOf_eq_range 2 _ (by simp only [List.length_append, bytesLE_length]), readLE_ctr_pad]
  have hc := c.isLt
  have hp := p.isLt
  simp only [show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  norm_num at hc hp ⊢
  constructor <;> apply BitVec.eq_of_toNat_eq <;> simp only [BitVec.toNat_ofNat] <;> omega

theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    wordsOf (pad64 (T3.encodingInput lay tree leaf msg c)) =
      [dlo msg.1, dhi msg.1, BitVec.ofNat 64 (hdr0 4 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf),
        BitVec.ofNat 64 (c.toNat + 2 ^ 32 * (msg.2.1.toNat % 2 ^ 32)), BitVec.ofNat 64 (msg.2.1.toNat / 2 ^ 32),
        dlo msg.2.2, dhi msg.2.2] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : bytesLE 16 msg.1 ++ bytesLE 16 (header 4 lay.val tree 0 leaf) ++ bytesLE 4 c ++ bytesLE 12 msg.2.1 ++
      bytesLE 16 msg.2.2 = bytesLE 16 msg.1 ++ (bytesLE 16 (header 4 lay.val tree 0 leaf) ++
        ((bytesLE 4 c ++ bytesLE 12 msg.2.1) ++ bytesLE 16 msg.2.2)) := by
    simp only [List.append_assoc]
  rw [e, wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_ctr_pad, wordsOf_bytesLE16]
  rfl

theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : T3.LayerMessage) (c : BitVec 32) :
    (toQ (pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl : (pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
    rw [pad64_encodingInput, encodingInput_length']
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]

/-- The forest-pk input `[root_0 | T(11) | root_1 .. root_6]` (two blocks). -/
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)

theorem forestPk_eq (index : Nat) (roots : List Digest) :
    T3.forestPk index roots = T3.shortHash (forestInput index roots) := rfl

theorem sum_map_16 : ∀ l : List Digest, (l.map fun _ => (16 : Nat)).sum = 16 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_16 l, List.length_cons]; ring

theorem forestInput_length (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (forestInput index roots).length = 128 := by
  unfold forestInput
  simp only [List.length_append, bytesLE_length, List.length_flatMap]
  rw [sum_map_16, List.length_drop, h]

theorem wordsOf_forestInput (index : Nat) (roots : List Digest) :
    wordsOf (forestInput index roots) =
      [dlo (roots.getD 0 0), dhi (roots.getD 0 0), BitVec.ofNat 64 (hdr0 11 0 index 0),
        BitVec.ofNat 64 (hdr1 index 0)] ++ (roots.drop 1).flatMap (fun d => [dlo d, dhi d]) := by
  unfold forestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl

theorem pad64_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    pad64 (forestInput index roots) = forestInput index roots :=
  pad64_of_aligned _ (by rw [forestInput_length index roots h])

theorem blocks_forestInput (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (toQ (pad64 (forestInput index roots))).blocks = 2 := by
  rw [pad64_forestInput index roots h,
    blocks_toQ (by rw [Aligned, forestInput_length index roots h]; omega), forestInput_length index roots h]

/-- `pad64` of an input of whole doublewords appends zero doublewords. -/
theorem wordsOf_pad64 (l : HashInput) (h : l.length % 8 = 0) :
    wordsOf (pad64 l) = wordsOf l ++ List.replicate ((64 - l.length % 64) % 64 / 8) 0 := by
  unfold pad64
  rw [wordsOf_append _ _ h]
  congr 1
  have : (64 - l.length % 64) % 64 = 8 * ((64 - l.length % 64) % 64 / 8) := by omega
  rw [this, wordsOf_replicate_zero]
  congr 1
  omega

/-! ## One-block HASH inputs from memory -/

theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, ofNat_add8, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega

theorem readWords_eight (t : MachineState) (A : Nat) (hA : A + 64 < 2 ^ 64) :
    t.readWords (BitVec.ofNat 64 A) 8 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] := by
  rw [readWords_ofNat t A 8 (by omega)]
  rfl

/-- A one-block HASH input at `A` whose eight doublewords are those of the 64-byte list `l`. -/
theorem hashInput_words8 (t : MachineState) (l : List UInt8) (A : Nat) (hl : l.length = 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw : [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] = wordsOf l) :
    hashInput t = toQ l :=
  hashInput_toQ t l 0 A hl h10 hA (by omega) h11 (by norm_num) (by rw [readWords_eight t A hA']; exact hw)

end SigGolfCandidate.T3M.Verify
