import SigGolfCandidate.T3.Secc.CaseCScore
import SigGolfCandidate.T3.Secc.PairGuessWorld

/-!
# Stream CC: opened positions versus the raw coordinates of a digest output

* `selection_getD`: the `c`-th selection of an output is its raw bucket with its sorted raw leaves;
* `outLeaves_injective`: an admissible output has three distinct raw leaves in every coordinate;
* `mem_openedPositions` / `opened_mem`: the opened positions (B-PAIR's `openedPositions`) are exactly
  `(index, c, 128·bucket_c + leaf)` for the raw leaves;
* `coordCovered_of_opened`: if every opened position of `N` is opened by some exposure, `N` is covered.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3.DigestSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem selection_getD (x : HashOutput) (c : Fin 7) :
    (selections x).getD c.val ⟨0, []⟩ =
      ⟨(outBucket x c).val, (List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·)⟩ := by
  rw [← rawSelections_eq_selections, rawSelections, List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]
  rfl

theorem mem_selection_leaves (x : HashOutput) (c : Fin 7) (leaf : Nat) :
    leaf ∈ ((selections x).getD c.val ⟨0, []⟩).leaves ↔ ∃ j, (outLeaves x c j).val = leaf := by
  rw [selection_getD]
  change leaf ∈ (List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·) ↔ _
  rw [(List.mergeSort_perm _ _).mem_iff, List.mem_ofFn]

theorem outLeaves_injective (x : HashOutput) (h : admissible (selections x) = true) (c : Fin 7) :
    Function.Injective (outLeaves x c) := by
  unfold admissible at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have hlen : c.val < (selections x).length := by simp [selections]
  have hc := h.1 ((selections x).getD c.val ⟨0, []⟩) (by
    rw [List.getD_eq_getElem _ _ hlen]; exact List.getElem_mem hlen)
  rw [decide_eq_true_eq, selection_getD] at hc
  change ((List.ofFn fun j : Fin 3 => (outLeaves x c j).val).mergeSort (· ≤ ·)).Nodup at hc
  rw [(List.mergeSort_perm _ _).nodup_iff, List.nodup_ofFn] at hc
  intro j j' hjj
  exact hc (congrArg Fin.val hjj)

theorem outputIndex_eq (x : HashOutput) : BPair.outputIndex x = outIdx x := by
  apply Fin.ext
  rw [show (BPair.outputIndex x).val = x.toNat % 2 ^ 31 from rfl, ← rawView_index]
  rfl

theorem leafIndex_val (b : Fin 16) (leaf : Fin 128) : (BPair.leafIndex b.val leaf.val).val = b.val * 128 + leaf.val := by
  unfold BPair.leafIndex
  simp only
  apply Nat.mod_eq_of_lt
  omega

theorem leafIndex_inj {b b' : Fin 16} {leaf leaf' : Fin 128}
    (h : BPair.leafIndex b.val leaf.val = BPair.leafIndex b'.val leaf'.val) : b = b' ∧ leaf = leaf' := by
  have hv := congrArg Fin.val h
  rw [leafIndex_val, leafIndex_val] at hv
  constructor
  · apply Fin.ext; omega
  · apply Fin.ext; omega

theorem mem_openedPositions (x : HashOutput) (f : BPair.FtsCoord) (h : f ∈ BPair.openedPositions x) :
    f.1 = outIdx x ∧ ∃ j, f.2.2 = BPair.leafIndex (outBucket x f.2.1).val (outLeaves x f.2.1 j).val := by
  unfold BPair.openedPositions at h
  rw [List.mem_flatMap] at h
  obtain ⟨c, -, hc⟩ := h
  rw [List.mem_map] at hc
  obtain ⟨leaf, hleaf, rfl⟩ := hc
  rw [mem_selection_leaves] at hleaf
  obtain ⟨j, rfl⟩ := hleaf
  refine ⟨outputIndex_eq x, j, ?_⟩
  rw [selection_getD]

theorem opened_mem (x : HashOutput) (c : Fin 7) (j : Fin 3) :
    ((outIdx x, c, BPair.leafIndex (outBucket x c).val (outLeaves x c j).val) : BPair.FtsCoord) ∈
      BPair.openedPositions x := by
  unfold BPair.openedPositions
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_finRange c, ?_⟩
  rw [List.mem_map]
  refine ⟨(outLeaves x c j).val, (mem_selection_leaves x c _).mpr ⟨j, rfl⟩, ?_⟩
  rw [selection_getD, outputIndex_eq]

/-- **Coverage from openings.** -/
theorem coordCovered_of_opened (X : List HashOutput) (N : HashOutput) (c : Fin 7)
    (h : ∀ j : Fin 3, ∃ out ∈ X,
      ((outIdx N, c, BPair.leafIndex (outBucket N c).val (outLeaves N c j).val) : BPair.FtsCoord) ∈
        BPair.openedPositions out) : CoordCovered X N c := by
  intro j
  obtain ⟨out, hout, hopen⟩ := h j
  obtain ⟨hidx, j', hj'⟩ := mem_openedPositions out _ hopen
  obtain ⟨hb, hl⟩ := leafIndex_inj hj'
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hout
  refine ⟨⟨(k, j'), ?_, ?_⟩, ?_⟩
  · rw [hk]; exact hidx.symm
  · rw [hk]; exact hb.symm
  · simp only [slotValue]
    rw [hk]
    exact hl.symm

end SigGolfCandidate.T3.Security.CaseC
