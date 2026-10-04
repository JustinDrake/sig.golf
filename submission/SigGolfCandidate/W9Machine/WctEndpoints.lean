import SigGolfCandidate.W9Machine.WctChainSplit
import SigGolfCandidate.W9Machine.WctWitnessBridge

namespace W9Machine.V3Endpoints
open W9Machine W9Machine.Chain
open SigGolfCandidate.T3M SigGolfCandidate.Rv RiscvZkvm.Rv64
theorem extract_lo (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 0 64 = X.extractLsb' 0 64 := by
  ext i hi
  have h : i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', Nat.zero_add, h,
    decide_true, Bool.true_and]
theorem extract_hi (X : BitVec 256) :
    (X.extractLsb' 0 128).extractLsb' 64 64 = X.extractLsb' 64 64 := by
  ext i hi
  have h : 64 + i < 128 := by omega
  simp only [BitVec.getElem_extractLsb', BitVec.getLsbD_extractLsb', h, decide_true,
    Bool.true_and, Nat.zero_add]
theorem traceLeafSlot_bound (t : Nat) (ht : t < 7) :
    traceLeafSlot t + 16 ≤ 1008 ∧ traceLeafSlot t % 8 = 0 := by
  unfold traceLeafSlot; split <;> omega
theorem sourceEnds_getD (w : WBytes) (k : Fin 9) (rank : Fin 728)
    (answers : List (BitVec 256)) (t : Nat) (ht : t < 7) :
    (sourceEnds w k rank answers).getD t 0 =
      if (ClaudeWCT.WCT9.codeword rank).getD t 0 = 0 then wdig w (V3.regionOffset k.val + V3.leafSlot t)
      else (answers.getD (((ClaudeWCT.WCT9.codeword rank).take (t + 1)).sum - 1) 0).extractLsb'
        0 128 := by
  unfold sourceEnds
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by simpa only [List.length_finRange] using ht)]
  simp only [Option.map_some, Option.getD_some, List.getElem_finRange, Fin.cast_mk]
theorem endpointsCorrect : W9Machine.Chain.EndpointsCorrect := by
  intro L w index k j rank u s tr answers hu hs hend t ht
  have hb := traceLeafSlot_bound t ht
  have hmem : ∀ word, word < 2 →
      s.getMem (BitVec.ofNat 64 (base k + traceLeafSlot t + 8 * word)) =
        chainValue (originalValue u index k j) answers
          (expectedEndpoint (ClaudeWCT.WCT9.codeword rank) t word) := by
    intro word hw
    rw [Nat.add_assoc, hs.memory _ (by omega), hend t ht word hw]
  have h0 := hmem 0 (by decide)
  have h1 := hmem 1 (by decide)
  rw [sourceEnds_getD w k rank answers t ht]
  unfold expectedEndpoint at h0 h1
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  split_ifs at h0 h1 ⊢ with hd
  · simp only [chainValue, originalValue] at h0 h1
    have hw0 : OrigW w s (base k + traceLeafSlot t) :=
      h0.trans (hu.origW _ (by omega) hb.2)
    have hw1 : OrigW w s (base k + traceLeafSlot t + 8) := by
      have := hu.origW (traceLeafSlot t + 8) (by omega) (by omega)
      rw [← Nat.add_assoc] at this
      exact h1.trans this
    have hdig := DigAt_origW hw0 hw1 (by unfold base coordinateBase; omega)
    have he : base k + traceLeafSlot t - 0x800 = V3.regionOffset k.val + V3.leafSlot t := by
      unfold base coordinateBase traceLeafSlot V3.leafSlot V3.regionOffset
      split <;> omega
    rw [he] at hdig
    exact hdig
  · simp only [chainValue, Nat.mul_zero, Nat.mul_one] at h0 h1
    exact ⟨h0.trans (extract_lo _).symm, h1.trans (extract_hi _).symm⟩
end W9Machine.V3Endpoints
