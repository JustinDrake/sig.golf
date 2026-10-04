import SigGolfCandidate.T3.Secc.WotsEncodingMatch
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
namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.UniformTableCompletion
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
theorem reached_valid_reference {T : Answers} {L : LeafAddr} {input : HashInput} (hr : Reached T L input)
    {w : List Nat} (hw : decode L.lay (low (T (.inl (.inr input)))) = some w) :
    referenceInput T L = some input := by
  obtain ⟨c, hc, rfl, hprev⟩ := hr
  have hs : referenceSearch T L = some (BitVec.ofNat 32 c, w) := by
    unfold referenceSearch
    have := counterSearch_first T L.lay L.tree L.leaf (leafMsg T L) counterLimit 0 c w hc
      (fun i hi => by rw [Nat.zero_add]; exact hprev i hi)
      (by rw [Nat.zero_add]; exact hw)
    rw [Nat.zero_add] at this
    exact this
  unfold referenceInput
  rw [hs]
  rfl
def MatchEntry (T : Answers) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : Digest × BitVec 96 × Digest) (counter : BitVec 32),
    entry.1 = encodingRow (leafOf L) message counter ∧
      referenceInput T (leafOf L) ≠ some (encodingRow (leafOf L) message counter) ∧
      decode L.lay (low entry.2) = some (referenceDigits T (leafOf L))
theorem matchAt_iff (T : Answers) (trace : List Entry) :
    (∃ L : CanonGraph.LeafPos, EncodingMatchAt T trace (leafOf L)) ↔ ∃ entry ∈ trace, MatchEntry T entry := by
  constructor
  · rintro ⟨L, message, counter, answer, hmem, hne, hdec⟩
    exact ⟨_, hmem, L, message, counter, rfl, hne, hdec⟩
  · rintro ⟨⟨input, answer⟩, hmem, L, message, counter, rfl, hne, hdec⟩
    exact ⟨L, message, counter, answer, hmem, hne, hdec⟩
theorem matchEntry_cell_le (T : Answers) (e : EncIndex) :
    Pr[fun ans => MatchEntry T (encInput e, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (2 ^ 128 : ENNReal)⁻¹ := by
  classical
  let targets : Finset Digest := Finset.univ.filter fun d => decode e.1.lay d = some (referenceDigits T (leafOf e.1))
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact decode_some_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_mono
        rintro ans - ⟨L, message, counter, he, -, hdec⟩
        have hL : e = (L, message, counter) := encInput_injective he
        subst hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdec⟩
    _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
    _ ≤ 1 / (2 : ENNReal) ^ 128 := ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = (2 ^ 128 : ENNReal)⁻¹ := one_div _
theorem matchEntry_other (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x) :
    ¬ MatchEntry (eagerAnswers U privateTable pub) (x, eagerAnswers U privateTable pub (.inl (.inr x))) := by
  rintro ⟨L, message, counter, he, hne, hdec⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf L) x := by
    by_contra hfree
    exact hx ⟨(L, message, counter), by
      change ¬ Reached _ _ (encInput (L, message, counter))
      rw [show encInput (L, message, counter) = x from he.symm]
      exact hfree, he.symm⟩
  have href := reached_valid_reference hreached hdec
  exact hne (he ▸ href)
section Table
variable (adversary : AdversaryP) (q : Nat)
theorem publicUniverse_sub (adversary : AdversaryP) : SeccLaw.publicUniverse ⊆ referenceInputs adversary :=
  Finset.subset_union_left
theorem eager_ov_eq (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (y : freeSet (eagerAnswers U privateTable pub) → HashOutput) :
    eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y) =
      Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub)) (eagerAnswers U privateTable pub) y := by
  funext query
  rcases query with (n | x) | c
  · simp only [eagerAnswers, Lazy.overwrite]
  · by_cases hx : Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x
    · have hxU : x ∈ U := by
        obtain ⟨e, -, rfl⟩ := hx
        exact hU (encInput_short e)
      rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
      simp only [Lazy.overwrite, dif_pos hx]
      unfold ov
      have hx' : ∃ e, e ∈ freeSet (eagerAnswers U privateTable pub) ∧ encInput e = (⟨x, hxU⟩ : U).val := hx
      rw [dif_pos hx']
      rfl
    · simp only [Lazy.overwrite, dif_neg hx]
      by_cases hxU : x ∈ U
      · rw [eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩, eagerAnswers_public_mem U privateTable _ ⟨x, hxU⟩]
        exact ov_other _ _ _ _ (fun e he heq => hx ⟨e, he, heq⟩)
      · rw [eagerAnswers_public_not_mem U _ _ x hxU, eagerAnswers_public_not_mem U _ _ x hxU]
  · simp only [eagerAnswers, Lazy.overwrite]
theorem free_transfer [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) (h : RefSample → ENNReal) (φ : List Entry → ENNReal)
    (hφ : ∀ y r, h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      φ (traceOf (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
      ∑' z, Pr[= z | (simulateQ (Lazy.lazyImpl encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))).run
          (fun _ => Finset.univ)] * φ z.1.2.toList := by
  have hinner : ∀ y : freeSet (eagerAnswers U privateTable pub) → HashOutput,
      ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          h (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) =
        ∑' r, Pr[= r | 𝒮[simulateQ (refImpl (Lazy.overwrite encInput (freeSet (eagerAnswers U privateTable pub))
          (eagerAnswers U privateTable pub) y))
          (SphincsSecurity.QueryPause.traced Lazy.obs (referenceGame (eagerAnswers U privateTable pub) adversary q))]] *
            φ r.2.toList := by
    intro y
    have hgame : referenceGame (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
        adversary q = referenceGame (eagerAnswers U privateTable pub) adversary q :=
      referenceGame_congr_honest (honest_ov U privateTable pub y) adversary q
    simp only [PrefixGame.liftM_apply, hφ, probOutput_evalSPMF]
    unfold offlineRun
    rw [hgame, ← eager_ov_eq U hU privateTable pub y]
    have hmap := Lazy.recorded_traced (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
      (referenceGame (eagerAnswers U privateTable pub) adversary q)
    rw [← tsum_probOutput_map_mul _ (fun r : SeedResult => (r.1, traceOf (eagerAnswers U privateTable
      (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r.2)) (fun z : Option (Bool × Nat) × List Entry => φ z.2),
      hmap, tsum_probOutput_map_mul]
  simp only [hinner]
  rw [← Lazy.lazyRun_eq_simulate,
    ← tsum_probOutput_map_mul _ Prod.fst (fun r : Option (Bool × Nat) × FreeMonoid Entry => φ r.2.toList),
    ← Lazy.eager_lazy, tsum_probOutput_bind_mul]
  simp only [probOutput_complete_univ (iX (freeSet (eagerAnswers U privateTable pub)))]
noncomputable def matchInd (s : RefSample) : ENNReal :=
  if ∃ L : CanonGraph.LeafPos, EncodingMatchAt s.answers s.trace (leafOf L) then 1 else 0
theorem encodingMatchAt_congr {T T' : Answers} (h : ∀ q, HonestQ T q → T' q = T q) (trace : List Entry)
    (L : CanonGraph.LeafPos) : EncodingMatchAt T' trace (leafOf L) ↔ EncodingMatchAt T trace (leafOf L) := by
  unfold EncodingMatchAt
  rw [referenceInput_congr_honest h, referenceDigits_congr_honest h]
theorem cellCount_le_encoding (F : Set EncIndex) (tr : List Entry) :
    Lazy.cellCount encInput F tr ≤ (tr.filter fun e => decide (EncodingInput e.1)).length := by
  unfold Lazy.cellCount
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro e he
  simp only [decide_eq_true_eq] at he ⊢
  obtain ⟨x, -, hx⟩ := he
  exact ⟨_, _, _, hx.symm⟩
theorem free_match_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (U : Finset HashInput) (hU : SeccLaw.publicUniverse ⊆ U) (privateTable : FullGame.FullTable)
    (pub : U → HashOutput) :
    ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          matchInd (mkSample (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers U privateTable pub) → HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers U privateTable (ov (freeSet (eagerAnswers U privateTable pub)) pub y))
          adversary q) : PMF SeedResult) r *
          (encodingCount (mkSample (eagerAnswers U privateTable
            (ov (freeSet (eagerAnswers U privateTable pub)) pub y)) r) : ENNReal) := by
  rw [free_transfer adversary q iX U hU privateTable pub matchInd
      (fun tr => (Lazy.marks (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) tr : ENNReal))
      (fun y r => by
        unfold matchInd mkSample
        rw [marks_unit]
        dsimp only
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ((matchAt_iff _ _).mp
            (by simpa only [encodingMatchAt_congr (honest_ov U privateTable pub y)] using h1)) h2
        · exact absurd (by simpa only [encodingMatchAt_congr (honest_ov U privateTable pub y)] using
            (matchAt_iff _ _).mpr h2) h1
        · rfl),
    free_transfer adversary q iX U hU privateTable pub (fun s => (encodingCount s : ENNReal))
      (fun tr => (((tr.filter fun e => decide (EncodingInput e.1)).length : Nat) : ENNReal))
      (fun y r => encodingCount_mkSample _ r)]
  refine (Lazy.lazy_marks_le encInput (freeSet (eagerAnswers U privateTable pub)) encInput_injective
    (eagerAnswers U privateTable pub) (fun (_ : Unit) => MatchEntry (eagerAnswers U privateTable pub)) _
    (fun e => by simpa only [Finset.univ_unique, Finset.sum_singleton] using
      matchEntry_cell_le (eagerAnswers U privateTable pub) e.val)
    (fun x hx _ => matchEntry_other U privateTable pub x hx) _).trans ?_
  refine mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun z => mul_le_mul' le_rfl ?_)
  exact_mod_cast cellCount_le_encoding _ _
end Table
end Enc
end ClaudeWCT.W9.T3.Security.Wots
