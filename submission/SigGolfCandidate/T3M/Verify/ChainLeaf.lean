import SigGolfCandidate.T3M.Verify.ChainLGood
import SigGolfCandidate.T3M.Verify.Words

/-! # V1: the leaf-pk HASH input

The leaf-pk block (`xlpk*`) hashes `[end_0 | T(2, lay, tree, 0, leaf) | end_1 .. end_{n-1}]` in place: the lower
block at `0x300` (`n = 43`, 704 bytes = 11 blocks), the top block at `0x200` (`n = 58`, 944 bytes and the two zero
words `0x5B0`, `0x5B8` = `pad64`'s padding, 960 bytes = 15 blocks). `leafInput` is the argument of Core's `leafHash`
(`leafHash_eq`, by `rfl`); `lowLeaf_hashInput` / `topLeaf_hashInput` state the machine's input. -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-- The input of Core's `leafHash`. -/
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  SphincsSecurity.bytesLE 16 (ends.getD 0 0) ++ SphincsSecurity.bytesLE 16 (header 2 lay.val tree 0 leaf) ++
    (ends.drop 1).flatMap (SphincsSecurity.bytesLE 16)

theorem leafHash_eq (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl

/-- The two doublewords of a digest. -/
def dw (e : Digest) : List (BitVec 64) := [e.extractLsb' 0 64, e.extractLsb' 64 64]

theorem flatMap_length16 : ∀ (L : List Digest), (L.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * L.length
  | [] => rfl
  | e :: L => by
    rw [List.flatMap_cons, List.length_append, flatMap_length16 L, SphincsSecurity.bytesLE_length]; simp; ring

theorem leafInput_length (lay : Layer) (tree leaf : Nat) (ends : List Digest) (h : 1 ≤ ends.length) :
    (leafInput lay tree leaf ends).length = 16 * (ends.length + 1) := by
  unfold leafInput
  rw [List.length_append, List.length_append, flatMap_length16, SphincsSecurity.bytesLE_length,
    SphincsSecurity.bytesLE_length, List.length_drop]
  omega

theorem wordsOf_leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    wordsOf (leafInput lay tree leaf ends) =
      dw (ends.getD 0 0) ++ [BitVec.ofNat 64 (hdr0 2 lay.val tree 0), BitVec.ofNat 64 (hdr1 tree leaf)] ++
        (ends.drop 1).flatMap dw := by
  unfold leafInput
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_flatMap16]
  rfl

/-- Consecutive 16-byte slots read as doublewords. -/
theorem readWords_digs (t : MachineState) : ∀ (L : List Digest) (A : Nat),
    (∀ j < L.length, DigAt t (A + 16 * j) (L.getD j 0)) →
      t.readWords (BitVec.ofNat 64 A) (2 * L.length) = L.flatMap dw
  | [], _, _ => rfl
  | e :: L, A, h => by
    rw [List.length_cons, show 2 * (L.length + 1) = 2 + 2 * L.length by ring, readWords_add, readWords_two,
      show A + 8 * 2 = A + 16 by ring, readWords_digs t L (A + 16) (fun j hj => by
        have := h (j + 1) (by simp; omega)
        rwa [show A + 16 * (j + 1) = A + 16 + 16 * j by ring, List.getD_cons_succ] at this),
      List.flatMap_cons]
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0.1, h0.2]; rfl

theorem getD_drop1 (L : List Digest) (j : Nat) : (L.drop 1).getD j 0 = L.getD (j + 1) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  congr 2; omega

/-- **The lower leaf-pk HASH input** (`a0 = 0x300`, `a1 = 704`): the 43 ends in `slotL`, `T` at `0x310`. -/
theorem lowLeaf_hashInput (t : MachineState) (lay : Layer) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 43) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x300)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 704) (hS : ∀ j < 43, DigAt t (slotL j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x310) = BitVec.ofNat 64 (hdr0 2 lay.val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x318) = BitVec.ofNat 64 (hdr1 tree leaf)) :
    hashInput t = toQ (pad64 (leafInput lay tree leaf ends)) ∧ (toQ (pad64 (leafInput lay tree leaf ends))).blocks = 11 := by
  have hl : (leafInput lay tree leaf ends).length = 64 * (10 + 1) := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  rw [pad64_of_aligned _ (by simp [hl])]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 10 0x300 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [wordsOf_leafInput, show 8 * (10 + 1) = 2 + (2 + 2 * (ends.drop 1).length) by simp [hn],
    readWords_add, readWords_add, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotL 0 = 0x300 from rfl] at e0
  rw [show 0x300 + 8 * 2 = 0x310 by rfl, show 0x310 + 8 = 0x318 by rfl, show 0x310 + 8 * 2 = 0x320 by rfl,
    e0.1, show 0x300 + 8 = (0x300 : Nat) + 8 from rfl, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x320 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotL (j + 1) = 0x320 + 16 * j by unfold slotL; simp; omega] at this)]
  rfl

/-- **The top leaf-pk HASH input** (`a0 = 0x200`, `a1 = 960`): the 58 ends in `slotT`, `T` at `0x210`, the zero
words at `0x5B0`, `0x5B8`. -/
theorem topLeaf_hashInput (t : MachineState) (tree leaf : Nat) (ends : List Digest)
    (hn : ends.length = 58) (h10 : t.getReg .x10 = BitVec.ofNat 64 0x200)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 960) (hS : ∀ j < 58, DigAt t (slotT j) (ends.getD j 0))
    (hT0 : t.getMem (BitVec.ofNat 64 0x210) = BitVec.ofNat 64 (hdr0 2 (0 : Layer).val tree 0))
    (hT1 : t.getMem (BitVec.ofNat 64 0x218) = BitVec.ofNat 64 (hdr1 tree leaf))
    (hZ0 : t.getMem (BitVec.ofNat 64 0x5B0) = 0) (hZ1 : t.getMem (BitVec.ofNat 64 0x5B8) = 0) :
    hashInput t = toQ (pad64 (leafInput 0 tree leaf ends)) ∧ (toQ (pad64 (leafInput 0 tree leaf ends))).blocks = 15 := by
  have hl0 : (leafInput 0 tree leaf ends).length = 944 := by
    rw [leafInput_length _ _ _ _ (by omega), hn]
  have hl : (pad64 (leafInput 0 tree leaf ends)).length = 64 * (14 + 1) := by
    unfold pad64; rw [List.length_append, List.length_replicate, hl0]
  refine ⟨?_, by rw [blocks_toQ ⟨by simp [hl], by simp [hl]⟩, hl]⟩
  apply hashInput_toQ t _ 14 0x200 hl h10 (by norm_num) (by norm_num) (by simpa using h11) (by norm_num)
  rw [Verify.wordsOf_pad64 _ (by rw [hl0]), hl0, wordsOf_leafInput,
    show 8 * (14 + 1) = 2 + (2 + (2 * (ends.drop 1).length + 2)) by simp [hn],
    readWords_add, readWords_add, readWords_add, readWords_two, readWords_two, readWords_two]
  have e0 := hS 0 (by omega)
  rw [show slotT 0 = 0x200 from rfl] at e0
  have hd : (ends.drop 1).length = 57 := by simp [hn]
  rw [show 0x200 + 8 * 2 = 0x210 by rfl, show 0x210 + 8 = 0x218 by rfl, show 0x210 + 8 * 2 = 0x220 by rfl,
    e0.1, e0.2, hT0, hT1,
    readWords_digs t (ends.drop 1) 0x220 (fun j hj => by
      rw [getD_drop1]
      have := hS (j + 1) (by simp at hj; omega)
      rwa [show slotT (j + 1) = 0x220 + 16 * j by unfold slotT; simp; omega] at this),
    hd, show 0x220 + 8 * (2 * 57) = 0x5B0 by rfl, show 0x5B0 + 8 = 0x5B8 by rfl, hZ0, hZ1]
  simp [List.append_assoc, dw]

end SigGolfCandidate.T3M
