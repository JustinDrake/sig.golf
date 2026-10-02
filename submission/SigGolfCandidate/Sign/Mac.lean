import SigGolfCandidate.Sign.Init

/-!
# The cache MAC: key input and tag comparison (byte ↔ dword lemmas)

* `words_macKeyInput` : the padded key-derivation input as dwords (`tw_mackey(i) | P | S`).
* `macTag_eq_iff` : the 48 tag bytes equal the cached ones iff the six dwords agree.
* `answerBytes_32` / `toList_tag` : a 256-bit answer as four dwords.
* `tag_eq_iff` : a 32-byte tag equals the answer iff the four dwords agree.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem words_macKeyInput (S : List Byte) (hS : S.length = 32) (i : Nat) :
    padBlocks (macKeyInput S i).length = 0 ∧
    wordsOf (padTo64 (macKeyInput S i)) = twWords 14 0 0 0 i ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (macKeyInput S i) 0 (by simp [macKeyInput, hS])
    (by simp [macKeyInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, macKeyInput, wordsOf_thInput_pad]
  simp [hS, zeros]

theorem answerBytes_32 (a : BitVec 256) :
    answerBytes 32 a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) := by
  unfold answerBytes bytesOfWord
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.map_append, List.append_assoc]
  simp only [extractLsb'_extractLsb' _ _ _ (by norm_num : (0 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (1 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (2 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (3 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (4 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (5 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (6 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (7 : Nat) < 8)]

theorem toList_tag (a : BitVec 256) :
    toList (n := 32) a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) :=
  answerBytes_32 a

theorem bytesOfWord_inj {w w' : Word} (h : bytesOfWord w = bytesOfWord w') : w = w' := by
  apply BitVec.eq_of_toNat_eq
  rw [← leNat_bytesOfWord, ← leNat_bytesOfWord, h]

/-- An 8-byte list is the bytes of its dword. -/
theorem bytesOfWord_leNat (l : List Byte) (hl : l.length = 8) :
    bytesOfWord (BitVec.ofNat 64 (leNat l)) = l := by
  apply List.ext_getElem (by simp [hl])
  intro j hj1 hj2
  simp only [bytesOfWord, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp at hj1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]; rfl

/-- A 32-byte list from its four dwords. -/
theorem eq_of_words4 (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    l = bytesOfWord c0 ++ bytesOfWord c1 ++ bytesOfWord c2 ++ bytesOfWord c3 := by
  have e : l = l.take 8 ++ (l.drop 8).take 8 ++ ((l.drop 8).drop 8).take 8 ++ ((l.drop 8).drop 8).drop 8 := by
    simp only [List.append_assoc, List.take_append_drop]
  rw [e, wordsOf_append _ _ (by simp; omega), wordsOf_append _ _ (by simp; omega),
    wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  obtain ⟨h0, h1, h2, h3⟩ := hw
  rw [e, ← h0, ← h1, ← h2, ← h3, bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega),
    bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega)]

theorem append4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : bytesOfWord a0 ++ bytesOfWord a1 ++ bytesOfWord a2 ++ bytesOfWord a3 =
      bytesOfWord b0 ++ bytesOfWord b1 ++ bytesOfWord b2 ++ bytesOfWord b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  simp only [List.append_assoc] at h
  obtain ⟨h0, h⟩ := List.append_inj h (by simp)
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  exact ⟨bytesOfWord_inj h0, bytesOfWord_inj h1, bytesOfWord_inj h2, bytesOfWord_inj h3⟩

/-- The tag comparison, dword by dword. -/
theorem tag_eq_iff (a : BitVec 256) (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    toList (n := 32) a = l ↔ a.extractLsb' 0 64 = c0 ∧ a.extractLsb' 64 64 = c1 ∧
      a.extractLsb' 128 64 = c2 ∧ a.extractLsb' 192 64 = c3 := by
  rw [toList_tag, eq_of_words4 l hl c0 c1 c2 c3 hw]
  constructor
  · exact append4_inj
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

/-- Doubleword `j` of a word list, from its number. -/
theorem wordsToNat_digit : ∀ (R : List Word) (j : Nat), j < R.length →
    wordsToNat R / 2 ^ (64 * j) % 2 ^ 64 = (R.getD j 0).toNat
  | [], j, h => by simp at h
  | w :: R, 0, _ => by
      have hw := w.isLt
      simp only [wordsToNat, Nat.mul_zero, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]
      omega
  | w :: R, j + 1, h => by
      have hw := w.isLt
      have ih := wordsToNat_digit R j (by simpa using h)
      simp only [wordsToNat, List.getD_cons_succ]
      rw [← ih, show 64 * (j + 1) = 64 + 64 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
      congr 2
      omega

/-- The tag comparison, doubleword by doubleword. -/
theorem macTag_eq_iff (a0 a1 a2 : BitVec 256) (region ctag : List Byte) (hc : ctag.length = 48)
    (hw : (wordsOf ctag).length = 6) :
    macTag a0 a1 a2 region = ctag ↔ ∀ j < 6,
      BitVec.ofNat 64 ((macWords a0 (chunks32 region) ++ macWords a1 (chunks32 region) ++
        macWords a2 (chunks32 region)).getD j 0) = (wordsOf ctag).getD j 0 := by
  have key : ∀ j < 6, (BitVec.ofNat 64 ((macWords a0 (chunks32 region) ++ macWords a1 (chunks32 region) ++
        macWords a2 (chunks32 region)).getD j 0) = (wordsOf ctag).getD j 0) ↔
      leNat (macTag a0 a1 a2 region) / 2 ^ (64 * j) % 2 ^ 64 = leNat ctag / 2 ^ (64 * j) % 2 ^ 64 := by
    intro j hj
    rw [← MacPass.macTag_word a0 a1 a2 region j hj, ← wordsToNat_wordsOf ctag,
      wordsToNat_digit _ j (by omega)]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rwa [BitVec.toNat_ofNat, Nat.mod_mod] at this
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_mod]; exact h
  constructor
  · intro h j hj
    exact (key j hj).mpr (by rw [h])
  · intro h
    exact MacPass.eq_of_words48 _ _ (MacPass.length_macTag _ _ _ _) hc (fun j hj => (key j hj).mp (h j hj))

end SigGolfCandidate.Sign
