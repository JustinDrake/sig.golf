import SigGolfCandidate.T3.Secc.WotsExtractChain

namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def dummyDigest0 : Digest := BitVec.ofNat 128 17680986319720600780412
def dummyDigestLow : Digest := BitVec.ofNat 128 48611766702991209076737369103800916845
def dummyDigest (lay : Layer) : Digest := if lay.val = 0 then dummyDigest0 else dummyDigestLow
theorem dummyDigest_decode (lay : Layer) : decode lay (dummyDigest lay) = some (dummyDigits lay) := by
  fin_cases lay
  · show decode 0 dummyDigest0 = some (dummyDigits 0)
    decide +kernel
  · show decode 1 dummyDigestLow = some (dummyDigits 1)
    decide +kernel
  · show decode 2 dummyDigestLow = some (dummyDigits 2)
    decide +kernel
  · show decode 3 dummyDigestLow = some (dummyDigits 3)
    decide +kernel
end SigGolfCandidate.T3.Security.WotsExtract
namespace SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security.WotsExtract
theorem dummyDigits_valid (lay : Layer) : ∃ value : Digest, decode lay value = some (dummyDigits lay) :=
  ⟨dummyDigest lay, dummyDigest_decode lay⟩
theorem dummyWord_valid (lay : Layer) : MixedCode.Valid (decodedWord (dummyDigest_decode lay)) :=
  decodedWord_valid _
theorem word_cases {lay : Layer} {refDigest candDigest : Digest} {refDigits candDigits : List Nat}
    (hr : decode lay refDigest = some refDigits) (hc : decode lay candDigest = some candDigits) :
    candDigits = refDigits ∨
      (∃ i, MixedCode.UnitNeighborAt (decodedWord hr) (decodedWord hc) i) ∨
      (∃ i, (decodedWord hc i).val + 2 ≤ (decodedWord hr i).val) ∨
      (∃ i j, i ≠ j ∧ (decodedWord hc i).val < (decodedWord hr i).val ∧
        (decodedWord hc j).val < (decodedWord hr j).val) := by
  by_cases he : candDigits = refDigits
  · exact Or.inl he
  right
  have hne : decodedWord hc ≠ decodedWord hr := by
    intro hw
    apply he
    rw [← decodedWord_list hc, ← decodedWord_list hr, hw]
  rcases MixedCode.backwardWork_trichotomy (decodedWord_valid hr) (decodedWord_valid hc) with h | h | h
  · exact (hne h).elim
  · exact Or.inl h
  · exact Or.inr (MixedCode.two_backward_steps h)
end SigGolfCandidate.T3.Security.Wots
namespace SigGolfCandidate.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem referenceSearch_decode (answers : Answers) (L : LeafAddr) {c : BitVec 32} {digits : List Nat}
    (h : referenceSearch answers L = some (c, digits)) :
    decode L.lay (low (answers (.inl (.inr (encodingRow L (leafMsg answers L) c))))) = some digits :=
  (Correctness.counterSearch_some answers L.lay L.tree L.leaf (leafMsg answers L) counterLimit 0 c digits
    (by norm_num [counterLimit]) h).2.2
theorem referenceDigits_decode (answers : Answers) (L : LeafAddr) :
    ∃ value : Digest, decode L.lay value = some (referenceDigits answers L) := by
  unfold referenceDigits
  cases hs : referenceSearch answers L with
  | none => exact dummyDigits_valid L.lay
  | some s =>
      obtain ⟨c, digits⟩ := s
      exact ⟨_, referenceSearch_decode answers L hs⟩
theorem depth_le (answers : Answers) (a : ChainAddr) (ha : a.chain < chainCount a.key.lay) :
    depth answers a ≤ maxDigit a.key.lay a.chain := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers a.key
  have := decode_digit_max hv a.chain ha
  unfold depth
  omega
theorem referenceDigits_length (answers : Answers) (L : LeafAddr) :
    (referenceDigits answers L).length = chainCount L.lay := by
  obtain ⟨value, hv⟩ := referenceDigits_decode answers L
  exact (decode_length_sum hv).1
theorem encodingRow_injective {L : LeafAddr} {m m' : Digest} {c c' : BitVec 32}
    (h : encodingRow L m c = encodingRow L m' c') : m = m' ∧ c = c' := by
  unfold encodingRow at h
  have h' := Sampling.pad64_inj_of_length (by simp only [encodingInput, List.length_append, bytesLE_length]) h
  unfold encodingInput at h'
  obtain ⟨hh, hc⟩ := List.append_inj h' (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hm, -⟩ := List.append_inj hh (by simp only [bytesLE_length])
  exact ⟨bytesLE_injective hm, bytesLE_injective hc⟩
theorem referenceInput_ne (answers : Answers) (L : LeafAddr) (msg : Digest) (ctr : BitVec 32)
    {digits : List Nat} (hd : decode L.lay (low (answers (.inl (.inr (encodingRow L msg ctr))))) = some digits)
    (hne : msg ≠ leafMsg answers L ∨ digits ≠ referenceDigits answers L) :
    referenceInput answers L ≠ some (encodingRow L msg ctr) := by
  intro h
  unfold referenceInput at h
  cases hs : referenceSearch answers L with
  | none => rw [hs] at h; simp at h
  | some s =>
      obtain ⟨c, w'⟩ := s
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hm, hc⟩ := encodingRow_injective h
      subst hm hc
      have hdec := referenceSearch_decode answers L hs
      have hw : referenceDigits answers L = w' := by unfold referenceDigits; rw [hs]; rfl
      have hdw : digits = w' := Option.some.inj (hd.symm.trans hdec)
      rcases hne with hne | hne
      · exact hne rfl
      · exact hne (hdw.trans hw.symm)
def routeLeaf (index : Nat) (lay : Layer) : LeafAddr := ⟨lay, (route index lay).2, (route index lay).1⟩
theorem route_split (index b h : Nat) : index / 2 ^ (b + h) * 2 ^ h + index / 2 ^ b % 2 ^ h = index / 2 ^ b := by
  rw [pow_add, ← Nat.div_div_eq_div_mul]
  exact Nat.div_add_mod' (index / 2 ^ b) (2 ^ h)
theorem route_tree_succ (index : Nat) (lay : Layer) (h : lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = (route index ⟨lay.val + 1, by omega⟩).2 := by
  fin_cases lay
  · show index / 2 ^ (19 + 12) * 2 ^ 12 + index / 2 ^ 19 % 2 ^ 12 = index / 2 ^ 19
    exact route_split index 19 12
  · show index / 2 ^ (12 + 7) * 2 ^ 7 + index / 2 ^ 12 % 2 ^ 7 = index / 2 ^ 12
    exact route_split index 12 7
  · show index / 2 ^ (6 + 6) * 2 ^ 6 + index / 2 ^ 6 % 2 ^ 6 = index / 2 ^ 6
    exact route_split index 6 6
  · exact absurd h (by decide)
theorem route_forest (index : Nat) (lay : Layer) (h : ¬lay.val < 3) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 = index := by
  fin_cases lay
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · show index / 2 ^ (0 + 6) * 2 ^ 6 + index / 2 ^ 0 % 2 ^ 6 = index
    have := route_split index 0 6
    simpa using this
theorem leafMsg_route (answers : Answers) (index : Nat) (lay : Layer) :
    leafMsg answers (routeLeaf index lay) = Extract.honestMsg answers index lay := by
  unfold leafMsg Extract.honestMsg
  simp only [routeLeaf]
  by_cases h : lay.val < 3
  · rw [dif_pos h, dif_pos h, route_tree_succ index lay h]
  · rw [dif_neg h, dif_neg h, route_forest index lay h]
theorem routeLeaf_source (index : Nat) (lay : Layer) (hidx : index < 2 ^ 31) :
    (routeLeaf index lay).tree < 2 ^ 31 ∧ (routeLeaf index lay).leaf < 2 ^ height (routeLeaf index lay).lay :=
  ⟨lt_of_le_of_lt (Nat.div_le_self _ _) hidx, route_leaf_bound index lay⟩
end SigGolfCandidate.T3.Security.WotsExtract
