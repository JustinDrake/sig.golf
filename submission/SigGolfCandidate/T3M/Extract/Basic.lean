import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Bytes

namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
def canonicalHeader (hdr : HashInput) : HashInput :=
  if 128 ≤ (hdr.getD 0 0).toNat then hdr.take 8 ++ List.replicate 8 0 else hdr
@[simp] theorem canonicalHeader_unmarked (hdr : HashInput) (h : ¬128 ≤ (hdr.getD 0 0).toNat) :
    canonicalHeader hdr = hdr := by
  unfold canonicalHeader
  rw [if_neg h]
theorem canonicalHeader_marked (low pad : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = low ++ List.replicate 8 0 := by
  have hm : 128 ≤ ((low ++ pad).getD 0 0).toNat := by
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hmark
  unfold canonicalHeader
  rw [if_pos hm]
  simp [List.take_append, hlen]
theorem canonicalHeader_pad_irrelevant (low pad pad' : HashInput) (hlen : low.length = 8)
    (hmark : 128 ≤ (low.getD 0 0).toNat) :
    canonicalHeader (low ++ pad) = canonicalHeader (low ++ pad') := by
  rw [canonicalHeader_marked low pad hlen hmark, canonicalHeader_marked low pad' hlen hmark]
theorem canonicalHeader_zero_pad (low : HashInput) (hlen : low.length = 8) :
    canonicalHeader (low ++ List.replicate 8 0) = low ++ List.replicate 8 0 := by
  by_cases hm : 128 ≤ (low.getD 0 0).toNat
  · exact canonicalHeader_marked low _ hlen hm
  · apply canonicalHeader_unmarked
    simpa only [List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show 0 < low.length by omega)] using hm
end SigGolfCandidate.T3M.Extract

namespace SigGolfCandidate.T3M.Extract
open SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
theorem bytesLE_header_words (high low : BitVec 64) :
    bytesLE 16 (high ++ low) = bytesLE 8 low ++ bytesLE 8 high := by
  apply readLE_inj (by simp [bytesLE_length])
  rw [readLE_bytesLE, readLE_append, readLE_bytesLE, readLE_bytesLE, bytesLE_length]
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, Nat.shiftLeft_eq]
  omega
theorem bytesLE8_marker (low : BitVec 64) :
    ((bytesLE 8 low).getD 0 0).toNat = low.toNat % 256 := by
  simp [bytesLE, List.getD_eq_getElem?_getD, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem bytesLE16_marker (hdr : BitVec 128) :
    ((bytesLE 16 hdr).getD 0 0).toNat = hdr.toNat % 256 := by
  simp [bytesLE, List.getD_eq_getElem?_getD, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem canonicalHeader_words (high low : BitVec 64)
    (hm : 128 ≤ low.toNat % 256) :
    canonicalHeader (bytesLE 16 (high ++ low)) = bytesLE 8 low ++ List.replicate 8 0 := by
  rw [bytesLE_header_words]
  apply canonicalHeader_marked _ _ (bytesLE_length _ _)
  simpa only [bytesLE8_marker] using hm
theorem canonicalHeader_high_irrelevant (high high' low : BitVec 64)
    (hm : 128 ≤ low.toNat % 256) :
    canonicalHeader (bytesLE 16 (high ++ low)) =
      canonicalHeader (bytesLE 16 (high' ++ low)) := by
  rw [canonicalHeader_words high low hm, canonicalHeader_words high' low hm]
theorem canonicalHeader_high_zero (hdr : BitVec 128) (hz : hdr.extractLsb' 64 64 = 0) :
    canonicalHeader (bytesLE 16 hdr) = bytesLE 16 hdr := by
  have he : hdr = (0#64 ++ hdr.extractLsb' 0 64) := by
    have h := (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
    rw [hz] at h
    exact h
  rw [he, bytesLE_header_words]
  have hzero : bytesLE 8 (0#64) = List.replicate 8 0 := by decide +kernel
  rw [hzero]
  exact canonicalHeader_zero_pad _ (bytesLE_length _ _)
theorem canonicalHeader_marker_ne (hdr : BitVec 128)
    (hm : hdr.toNat % 256 < 128) :
    canonicalHeader (bytesLE 16 hdr) = bytesLE 16 hdr := by
  apply canonicalHeader_unmarked
  rw [bytesLE16_marker]
  omega
end SigGolfCandidate.T3M.Extract

namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree leafSeed leafEnd)
open SphincsSecurity (bytesLE)
noncomputable def honestRoot (answers : Answers) (lay : Layer) (tree : Nat) : Digest :=
  treeValue (builtTree answers lay tree) (height lay) 0
def ftsLevels (answers : Answers) (index coord : Nat) : List (List Digest) :=
  (evalWithAnswerFn answers (buildFts index coord)).1
def ftsSecret (answers : Answers) (index coord leaf : Nat) : Digest :=
  (evalWithAnswerFn answers (buildFts index coord)).2.getD leaf 0
def ftsRoot (answers : Answers) (index coord : Nat) : Digest := treeValue (ftsLevels answers index coord) 11 0
def ftsRootsHonest (answers : Answers) (index : Nat) : List Digest := (List.range 7).map (ftsRoot answers index)
def listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) : HashInput :=
  bytesLE 16 first ++ bytesLE 16 hdr ++ rest.flatMap (bytesLE 16)
def leafInput (lay : Layer) (tree leaf : Nat) (ends : List Digest) : HashInput :=
  listInput (ends.getD 0 0) (header 2 lay.val tree 0 leaf) (ends.drop 1)
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  listInput (roots.getD 0 0) (header 11 0 index 0 0) (roots.drop 1)
def honestForest (answers : Answers) (index : Nat) : Digest :=
  evalWithAnswerFn answers (forestPk index (ftsRootsHonest answers index))
noncomputable def honestMsg (answers : Answers) (index : Nat) (lay : Layer) : Digest :=
  if h : lay.val < 3 then honestRoot answers ⟨lay.val + 1, by omega⟩ (route index ⟨lay.val + 1, by omega⟩).2
  else honestForest answers index
inductive Pos where
  | chain (lay : Layer) (tree leaf i step : Nat)
  | leaf (lay : Layer) (tree leaf : Nat)
  | node (lay : Layer) (tree level node : Nat)
  | forest (index : Nat)
  | ftsLeaf (index coord leaf : Nat)
  | ftsNode (index coord level node : Nat)
noncomputable def honestInput (answers : Answers) : Pos → HashInput
  | .chain lay tree leaf i step => pad64 (chainInput lay tree leaf i step
      (honestChainValue answers lay tree leaf i (leafSeed answers lay tree leaf i) step))
  | .leaf lay tree leaf => pad64 (leafInput lay tree leaf
      ((List.range (chainCount lay)).map (leafEnd answers lay tree leaf)))
  | .node lay tree level node => pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node)
      (treeValue (builtTree answers lay tree) level (2 * node)) 0
      (treeValue (builtTree answers lay tree) level (2 * node + 1)))
  | .forest index => pad64 (forestInput index (ftsRootsHonest answers index))
  | .ftsLeaf index coord leaf => pad64 (ftsLeafInputP index coord leaf 0 (ftsSecret answers index coord leaf) 0)
  | .ftsNode index coord level node => pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + node)
      (treeValue (ftsLevels answers index coord) level (2 * node)) 0
      (treeValue (ftsLevels answers index coord) level (2 * node + 1)))
def Pos.hdr : Pos → BitVec 128
  | .chain lay tree lf i step => chainHeader lay tree lf i step
  | .leaf lay tree lf => header 2 lay.val tree 0 lf
  | .node lay tree level nd => header 3 lay.val tree 0 (2 ^ (height lay - level - 1) + nd)
  | .forest index => header 11 0 index 0 0
  | .ftsLeaf index coord lf => header 9 coord index 0 lf
  | .ftsNode index coord level nd => header 10 coord index 0 (2 ^ (11 - level - 1) + nd)
def Pos.Bounded : Pos → Prop
  | .chain _ tree lf i step => tree < 2 ^ 31 ∧ lf < 4096 ∧ i < 64 ∧ step < 8
  | .leaf _ tree lf => tree < 2 ^ 40 ∧ lf < 2 ^ 32
  | .node lay tree level nd => tree < 2 ^ 40 ∧ level < height lay ∧ nd < 2 ^ (height lay - level - 1)
  | .forest index => index < 2 ^ 40
  | .ftsLeaf index coord lf => coord < 256 ∧ index < 2 ^ 40 ∧ lf < 2 ^ 32
  | .ftsNode index coord level nd => coord < 256 ∧ index < 2 ^ 40 ∧ level < 11 ∧ nd < 2 ^ (11 - level - 1)
def hdrBlock (input : HashInput) : HashInput := (input.drop 16).take 16
def SameHeader (actual honest : HashInput) : Prop :=
  canonicalHeader (hdrBlock actual) = canonicalHeader (hdrBlock honest)
def HitIn (answers : Answers) (qs : List Spec.Domain) : Prop :=
  ∃ pos actual, pos.Bounded ∧ .inl (.inr actual) ∈ qs ∧ HashHit answers (honestInput answers pos) actual ∧
    SameHeader actual (honestInput answers pos)
theorem HitIn.mono {answers : Answers} {qs qs' : List Spec.Domain} (h : HitIn answers qs)
    (hsub : ∀ q ∈ qs, q ∈ qs') : HitIn answers qs' := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  exact ⟨pos, actual, hb, hsub _ hq, hh, hs⟩
theorem HitIn.append_left {answers : Answers} {qs : List Spec.Domain} (qs' : List Spec.Domain)
    (h : HitIn answers qs) : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_left _ hq
theorem HitIn.append_right {answers : Answers} {qs' : List Spec.Domain} (qs : List Spec.Domain)
    (h : HitIn answers qs') : HitIn answers (qs ++ qs') :=
  h.mono fun _ hq => List.mem_append_right _ hq
def ftsRoots (w : WBytes) (index : Nat) (chosen : List Selection) : M (Option (List Digest × Nat)) :=
  (List.range 7).foldlM
    (fun (state : Option (List Digest × Nat)) coord => do
      let some (roots, ptr) := state | pure none
      let some (root, ptr) ← ftsCoordP w index coord (chosen.getD coord ⟨0, []⟩) ptr | pure none
      pure (some (roots ++ [root], ptr))) (some ([], streamBase))
theorem ftsP_eq (w : WBytes) (index : Nat) (chosen : List Selection) :
    ftsP w index chosen = (do
      let state ← ftsRoots w index chosen
      let some (roots, ptr) := state | pure none
      if streamEnd < ptr then return none
      pure (some (← forestPk index roots))) := rfl
end SigGolfCandidate.T3M.Extract
