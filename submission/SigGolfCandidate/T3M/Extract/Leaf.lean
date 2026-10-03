import SigGolfCandidate.T3M.Extract.Basic

namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem flatMap_bytes_injective : ∀ {xs ys : List Digest}, xs.length = ys.length →
    xs.flatMap (bytesLE 16) = ys.flatMap (bytesLE 16) → xs = ys
  | [], [], _, _ => rfl
  | x :: xs, y :: ys, hlen, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hxy, hrest⟩ := List.append_inj h (by simp only [bytesLE_length])
      rw [bytesLE_injective hxy, flatMap_bytes_injective (by simpa using hlen) hrest]
theorem listInput_length (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    (listInput first hdr rest).length = 32 + 16 * rest.length := by
  simp only [listInput, List.length_append, bytesLE_length, digest_list_bytes_length]
theorem listInput_injective {first first' : Digest} {hdr hdr' : BitVec 128} {rest rest' : List Digest}
    (hlen : rest.length = rest'.length) (h : listInput first hdr rest = listInput first' hdr' rest') :
    first = first' ∧ hdr = hdr' ∧ rest = rest' := by
  unfold listInput at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hf, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hf, bytesLE_injective hh, flatMap_bytes_injective hlen hr⟩
theorem list_head_drop : ∀ (xs : List Digest), 0 < xs.length → xs.getD 0 0 :: xs.drop 1 = xs
  | _ :: _, _ => rfl
theorem listInput_lists {xs ys : List Digest} {hdr hdr' : BitVec 128} (hlen : xs.length = ys.length)
    (hpos : 0 < ys.length)
    (h : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr' (ys.drop 1))) :
    xs = ys ∧ hdr = hdr' := by
  have hl : (listInput (xs.getD 0 0) hdr (xs.drop 1)).length = (listInput (ys.getD 0 0) hdr' (ys.drop 1)).length := by
    rw [listInput_length, listInput_length, List.length_drop, List.length_drop, hlen]
  obtain ⟨hf, hh, hr⟩ := listInput_injective (by rw [List.length_drop, List.length_drop, hlen])
    (Sampling.pad64_inj_of_length hl h)
  refine ⟨?_, hh⟩
  rw [← list_head_drop xs (by omega), ← list_head_drop ys hpos, hf, hr]
theorem hdrBlock_prefix (a h : Digest) (rest : HashInput) :
    hdrBlock (bytesLE 16 a ++ bytesLE 16 h ++ rest) = bytesLE 16 h := by
  unfold hdrBlock
  rw [List.append_assoc, List.drop_left' (bytesLE_length 16 a), List.take_left' (bytesLE_length 16 h)]
theorem hdrBlock_pad64 (input : HashInput) (h : 32 ≤ input.length) : hdrBlock (pad64 input) = hdrBlock input := by
  unfold hdrBlock pad64
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
theorem hdrBlock_block4 (a b c d : Digest) : hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc]
  exact hdrBlock_prefix a b _
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    hdrBlock (pad64 (listInput first hdr rest)) = bytesLE 16 hdr := by
  rw [hdrBlock_pad64 _ (by rw [listInput_length]; omega)]
  exact hdrBlock_prefix first hdr _
theorem leafHash_eq_shortHash (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    leafHash lay tree leaf ends = shortHash (leafInput lay tree leaf ends) := rfl
theorem forestPk_eq_shortHash (index : Nat) (roots : List Digest) :
    forestPk index roots = shortHash (forestInput index roots) := rfl
theorem listHash_extract (answers : Answers) (hdr : BitVec 128) (xs ys : List Digest)
    (hlen : xs.length = ys.length) (hpos : 0 < ys.length)
    (reaches : evalWithAnswerFn answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1))) =
      evalWithAnswerFn answers (shortHash (listInput (ys.getD 0 0) hdr (ys.drop 1)))) :
    xs = ys ∨
      (HashHit answers (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1)))
          (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1))) ∧
        SameHeader (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))
          (pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))) ∧
        .inl (.inr (pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)))) ∈
          queried answers (shortHash (listInput (xs.getD 0 0) hdr (xs.drop 1)))) := by
  by_cases heq : pad64 (listInput (xs.getD 0 0) hdr (xs.drop 1)) = pad64 (listInput (ys.getD 0 0) hdr (ys.drop 1))
  · exact Or.inl (listInput_lists hlen hpos heq).1
  · refine Or.inr ⟨⟨heq, ?_⟩, ?_, ?_⟩
    · rw [eval_shortHash, eval_shortHash] at reaches
      exact reaches
    · unfold SameHeader
      rw [hdrBlock_listInput, hdrBlock_listInput]
    · rw [queried_shortHash]
      exact List.mem_singleton_self _
theorem leafHash_extract (answers : Answers) (lay : Layer) (tree leaf : Nat) (ends honest : List Digest)
    (hlen : ends.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (leafHash lay tree leaf ends) =
      evalWithAnswerFn answers (leafHash lay tree leaf honest)) :
    ends = honest ∨
      (HashHit answers (pad64 (leafInput lay tree leaf honest)) (pad64 (leafInput lay tree leaf ends)) ∧
        SameHeader (pad64 (leafInput lay tree leaf ends)) (pad64 (leafInput lay tree leaf honest)) ∧
        .inl (.inr (pad64 (leafInput lay tree leaf ends))) ∈ queried answers (leafHash lay tree leaf ends)) :=
  listHash_extract answers _ ends honest hlen hpos reaches
theorem forestPk_extract (answers : Answers) (index : Nat) (roots honest : List Digest)
    (hlen : roots.length = honest.length) (hpos : 0 < honest.length)
    (reaches : evalWithAnswerFn answers (forestPk index roots) =
      evalWithAnswerFn answers (forestPk index honest)) :
    roots = honest ∨
      (HashHit answers (pad64 (forestInput index honest)) (pad64 (forestInput index roots)) ∧
        SameHeader (pad64 (forestInput index roots)) (pad64 (forestInput index honest)) ∧
        .inl (.inr (pad64 (forestInput index roots))) ∈ queried answers (forestPk index roots)) :=
  listHash_extract answers _ roots honest hlen hpos reaches
theorem ftsRootsHonest_length (answers : Answers) (index : Nat) : (ftsRootsHonest answers index).length = 7 := by
  simp [ftsRootsHonest]
theorem forestPk_honest_extract (answers : Answers) (index : Nat) (hidx : index < 2 ^ 40) (roots : List Digest)
    (hlen : roots.length = 7)
    (reaches : evalWithAnswerFn answers (forestPk index roots) = honestForest answers index) :
    roots = ftsRootsHonest answers index ∨ HitIn answers (queried answers (forestPk index roots)) := by
  rcases forestPk_extract answers index roots (ftsRootsHonest answers index)
      (by rw [hlen, ftsRootsHonest_length]) (by rw [ftsRootsHonest_length]; omega) reaches with h | ⟨hh, hs, hq⟩
  · exact Or.inl h
  · exact Or.inr ⟨.forest index, _, hidx, hq, hh, hs⟩
theorem queried_mapM_mem {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ (l : List α), ∀ a ∈ l, ∀ q ∈ queried answers (f a), q ∈ queried answers (l.mapM f)
  | [], _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, a, ha, q, hq => by
      rw [List.mapM_cons, queried_bind, queried_bind]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (List.mem_append_left _ (queried_mapM_mem answers f xs a ha q hq))
end SigGolfCandidate.T3M.Extract
