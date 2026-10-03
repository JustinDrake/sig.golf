import SigGolfCandidate.T3.Secc.WotsEncodingMarker
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingE1
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingMatch
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingResample
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEncodingCongr
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonEncoding
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraph
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGame
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRest
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
def chainAt (p : CanonGraph.LeafPos × Fin 58) : ChainAddr := ⟨leafOf p.1, p.2.val⟩
def MarkEntry (T : Answers) (a : ChainAddr) (entry : Entry) : Prop :=
  ∃ (message : Digest) (counter : BitVec 32) (digits : List Nat),
    entry.1 = encodingRow a.key message counter ∧
      referenceInput T a.key ≠ some (encodingRow a.key message counter) ∧
      decode a.key.lay (low entry.2) = some digits ∧
      digits.getD a.chain 0 + 1 = (referenceDigits T a.key).getD a.chain 0 ∧
      ∀ i, i ≠ a.chain → (referenceDigits T a.key).getD i 0 ≤ digits.getD i 0
theorem markerAt_iff (T : Answers) (trace : List Entry) (a : ChainAddr) :
    MarkerAt T trace a ↔ ∃ entry ∈ trace, MarkEntry T a entry := by
  constructor
  · rintro ⟨message, counter, answer, digits, hmem, hne, hd, hlow, hrest⟩
    exact ⟨_, hmem, message, counter, digits, rfl, hne, hd, hlow, hrest⟩
  · rintro ⟨⟨input, answer⟩, hmem, message, counter, digits, rfl, hne, hd, hlow, hrest⟩
    exact ⟨message, counter, answer, digits, hmem, hne, hd, hlow, hrest⟩
theorem markerAt_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry)
    (p : CanonGraph.LeafPos × Fin 58) : MarkerAt T' trace (chainAt p) ↔ MarkerAt T trace (chainAt p) := by
  unfold MarkerAt chainAt
  simp only
  rw [referenceInput_congr_honest h, referenceDigits_congr_honest h]
theorem markEntry_cell_le (T : Answers) (x : HashInput) (a : ChainAddr) :
    Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 57 / (2 : ENNReal) ^ 128 := by
  classical
  obtain ⟨v, hv⟩ := WotsExtract.referenceDigits_decode T a.key
  by_cases hc : a.chain < chainCount a.key.lay
  · let W := decodedWord hv
    let i : Fin (MixedCode.Code.n (code a.key.lay)) := ⟨a.chain, hc⟩
    let targets := EncodingTargets.targets a.key.lay (MixedCode.unitNeighbors W i)
    calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
          apply probEvent_mono
          rintro ans - ⟨message, counter, digits, -, -, hd, hlow, hrest⟩
          refine (EncodingTargets.source_decoded_target hd _).mpr ?_
          rw [MixedCode.mem_unitNeighbors]
          refine ⟨decodedWord_valid hv, decodedWord_valid hd, ?_, ?_⟩
          · exact hlow
          · intro j hj
            exact hrest j.val (fun he => hj (Fin.ext he))
      _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
      _ ≤ 57 / (2 : ENNReal) ^ 128 := by
          apply ENNReal.div_le_div_right
          exact_mod_cast (EncodingTargets.targets_card _ _).trans (unit_neighbors_bound _ W i)
  · have hz : Pr[fun ans => MarkEntry T a (x, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro ans - ⟨message, counter, digits, -, -, -, hlow, -⟩
      have hlen := WotsExtract.referenceDigits_length T a.key
      rw [List.getD_eq_default (referenceDigits T a.key) 0 (by omega)] at hlow
      omega
    rw [hz]
    exact zero_le
theorem markEntry_sum_cell_le (T : Answers) (e : EncIndex) :
    ∑ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ 3306 / (2 : ENNReal) ^ 128 := by
  classical
  have hb : ∀ p : CanonGraph.LeafPos × Fin 58,
      Pr[fun ans => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) (encInput e, ans) |
        ($ᵗ HashOutput : ProbComp HashOutput)] ≤ if p.1 = e.1 then 57 / (2 : ENNReal) ^ 128 else 0 := by
    intro p
    split_ifs with hp
    · exact (probEvent_mono fun ans _ h => h.2).trans (markEntry_cell_le T _ _)
    · apply le_of_eq
      apply probEvent_eq_zero
      rintro ans - ⟨-, message, counter, digits, he, -⟩
      have := encInput_injective (he.trans rfl : encInput e = encInput (p.1, message, counter))
      exact hp (congrArg Prod.fst this).symm
  refine (Finset.sum_le_sum fun p _ => hb p).trans (le_of_eq ?_)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single e.1 (fun L _ hL => by simp [hL]) (by simp)]
  simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_div_assoc]
  norm_num
theorem markEntry_other (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x)
    (p : CanonGraph.LeafPos × Fin 58) :
    ¬ (WotsExtract.SourceChain (chainAt p) ∧
      MarkEntry (eagerAnswers U privateTable pub) (chainAt p) (x, eagerAnswers U privateTable pub (.inl (.inr x)))) := by
  rintro ⟨-, message, counter, digits, he, hne, hdec, -⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf p.1) x := by
    by_contra hfree
    exact hx ⟨(p.1, message, counter), by
      change ¬ Reached _ _ (encInput (p.1, message, counter))
      rw [show encInput (p.1, message, counter) = x from he.symm]
      exact hfree, he.symm⟩
  have href := reached_valid_reference hreached hdec
  exact hne (he ▸ href)
noncomputable def markerCount (s : RefSample) : Nat :=
  (Finset.univ.filter fun p : CanonGraph.LeafPos × Fin 58 =>
    WotsExtract.SourceChain (chainAt p) ∧ MarkerAt s.answers s.trace (chainAt p)).card
theorem markerCount_marks (T : Answers) (trace : List Entry) (pk : Digest) :
    markerCount ⟨T, pk, trace⟩ =
      Lazy.marks (fun p entry => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry) trace := by
  unfold markerCount Lazy.marks
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : (WotsExtract.SourceChain (chainAt p) ∧ MarkerAt T trace (chainAt p)) ↔
      ∃ entry ∈ trace, WotsExtract.SourceChain (chainAt p) ∧ MarkEntry T (chainAt p) entry := by
    rw [markerAt_iff]
    constructor
    · rintro ⟨hs, entry, hmem, hm⟩
      exact ⟨entry, hmem, hs, hm⟩
    · rintro ⟨entry, hmem, hs, hm⟩
      exact ⟨hs, entry, hmem, hm⟩
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.mp h1) h2
  · exact absurd (hiff.mpr h2) h1
  · rfl
theorem markerCount_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry)
    (pk : Digest) : markerCount ⟨T', pk, trace⟩ = markerCount ⟨T, pk, trace⟩ := by
  unfold markerCount
  rw [Finset.card_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff := markerAt_congr h trace p
  simp only at hiff ⊢
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.1, hiff.mp h1.2⟩ h2
  · exact absurd ⟨h2.1, hiff.mpr h2.2⟩ h1
  · rfl
theorem free_marker_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (adversary : AdversaryP) (q : Nat) (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput)
    (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable) (pub : U → HashOutput) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          (markerCount (mkSample (eagerAnswers U privateTable
            (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) : ENNReal) ≤
      (3306 / (2 : ENNReal) ^ 128) * ∑' y,
        @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) : ENNReal) := by
  rw [free_transfer adversary q iX U hU privateTable pub (fun s => (markerCount s : ENNReal))
      (fun tr => (Lazy.marks (fun p entry => WotsExtract.SourceChain (chainAt p) ∧
        MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry) tr : ENNReal))
      (fun y r => by
        unfold mkSample
        rw [markerCount_congr (honest_ov U privateTable pub y), markerCount_marks]),
    free_transfer adversary q iX U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_le encInput (freeSet (eagerAnswers U privateTable pub)) encInput_injective
    (eagerAnswers U privateTable pub)
    (fun p entry => WotsExtract.SourceChain (chainAt p) ∧ MarkEntry (eagerAnswers U privateTable pub) (chainAt p) entry)
    _ (fun e => markEntry_sum_cell_le (eagerAnswers U privateTable pub) e.val)
    (fun x hx p => markEntry_other U privateTable pub x hx p) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Enc
open Enc in
theorem reference_markerCount_le (adversary : AdversaryP) (q : Nat) :
    ∑' s, referenceExperiment adversary q s * (Enc.markerCount s : ENNReal) ≤
      (3306 / (2 : ENNReal) ^ 128) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set Enc.EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set Enc.EncIndex, DecidableEq k := fun k => Classical.decEq k
  exact Enc.reference_free_le adversary q (fun k => Pi.instFintype) (fun s => (Enc.markerCount s : ENNReal))
    (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => Enc.free_marker_le adversary q (fun k => Pi.instFintype) (referenceInputs adversary)
      (Enc.publicUniverse_sub adversary) privateTable pub)
open Enc in
theorem reference_marker_sum_le (adversary : AdversaryP) (q : Nat) :
    ∑ a : CanonGraph.LeafPos × Fin 58,
      Pr[fun s => WotsExtract.SourceChain ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ ∧
        MarkerAt s.answers s.trace ⟨⟨a.1.lay, a.1.tree.val, a.1.leaf.val⟩, a.2.val⟩ | referenceExperiment adversary q] ≤
      (3306 / 2 ^ 128 : ENNReal) * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  refine le_trans (le_of_eq ?_) (reference_markerCount_le adversary q)
  simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine tsum_congr fun s => ?_
  unfold Enc.markerCount
  rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold Enc.chainAt Enc.leafOf
  split_ifs <;> simp
end ClaudeWCT.W9.T3.Security.Wots
