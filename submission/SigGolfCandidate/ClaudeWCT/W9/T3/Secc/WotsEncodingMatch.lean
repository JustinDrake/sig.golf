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
def EncodingInput (input : HashInput) : Prop :=
  ∃ (L : LeafAddr) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96),
    Extract.msgFits L.lay message ∧ input = encRow L message counter pad
def EncodingRow : Answers → SigGolfCandidate.T3.Spec.Domain → Prop
  | _, .inl (.inr input) => EncodingInput input
  | _, _ => False
noncomputable def encodingCount (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (EncodingRow s.answers (.inl (.inr e.1)))).length
theorem encodingCount_mkSample (T : Answers) (r : SeedResult) :
    (encodingCount (mkSample T r) : ENNReal) =
      (((traceOf T r.2).filter fun e => decide (EncodingInput e.1)).length : ENNReal) := rfl
namespace Enc
open SigGolfCandidate.T3.Security.Wots.Enc
theorem layerCounterSearch_first (T : Answers) (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) :
    ∀ fuel start k digits, k < fuel →
      (∀ i < k, decode lay ((T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
        (BitVec.ofNat 32 (start + i))))))).extractLsb' 0 128) = none) →
      decode lay ((T (.inl (.inr (pad64 (WCT9.layerEncodingInput lay tree leaf msg
        (BitVec.ofNat 32 (start + k))))))).extractLsb' 0 128) = some digits →
      evalWithAnswerFn T (WCT9.layerCounterSearch lay tree leaf msg start fuel) =
        some (BitVec.ofNat 32 (start + k), digits) := by
  intro fuel
  induction fuel with
  | zero => intro _ k _ hk; omega
  | succ fuel ih =>
      intro start k digits hk hprev hvalid
      simp only [WCT9.layerCounterSearch, evalWithAnswerFn_bind, eval_shortHash]
      rcases k with _ | k
      · simp only [Nat.add_zero] at hvalid ⊢
        rw [hvalid]
        rfl
      · have h0 := hprev 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [h0]
        have := ih (start + 1) k digits (by omega)
          (fun i hi => by rw [show start + 1 + i = start + (i + 1) by omega]; exact hprev (i + 1) (by omega))
          (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hvalid)
        rw [show start + (k + 1) = start + 1 + k by omega]
        exact this
theorem reached_valid_reference {T : Answers} {L : LeafAddr} {input : HashInput} (hr : Reached T L input)
    {w : List Nat} (hw : decode L.lay (low (T (.inl (.inr input)))) = some w) :
    referenceInput T L = some input := by
  obtain ⟨c, hc, rfl, hprev⟩ := hr
  have hs : referenceSearch T L = some (BitVec.ofNat 32 c, w) := by
    unfold referenceSearch
    have := layerCounterSearch_first T L.lay L.tree L.leaf (leafMsg T L) counterLimit 0 c w hc
      (fun i hi => by rw [Nat.zero_add, ← encRow_zero]; exact hprev i hi)
      (by rw [Nat.zero_add, ← encRow_zero]; exact hw)
    rw [Nat.zero_add] at this
    exact this
  unfold referenceInput
  rw [hs]
  rfl
def MatchEntry (T : Answers) (entry : Entry) : Prop :=
  ∃ (L : CanonGraph.LeafPos) (message : WCT9.LayerMsg) (counter : BitVec 32) (pad : BitVec 96),
    Extract.msgFits L.lay message ∧ entry.1 = encRow (leafOf L) message counter pad ∧
      referenceInput T (leafOf L) ≠ some (encRow (leafOf L) message counter pad) ∧
      decode L.lay (low entry.2) = some (referenceDigits T (leafOf L))
theorem matchAt_iff (T : Answers) (trace : List Entry) :
    (∃ L : CanonGraph.LeafPos, EncodingMatchAt T trace (leafOf L)) ↔ ∃ entry ∈ trace, MatchEntry T entry := by
  constructor
  · rintro ⟨L, message, counter, pad, answer, hfit, hmem, hne, hdec⟩
    exact ⟨_, hmem, L, message, counter, pad, hfit, rfl, hne, hdec⟩
  · rintro ⟨⟨input, answer⟩, hmem, L, message, counter, pad, hfit, rfl, hne, hdec⟩
    exact ⟨L, message, counter, pad, answer, hfit, hmem, hne, hdec⟩
theorem encInput_leaf {e : EncIndex} {L : CanonGraph.LeafPos} {message : WCT9.LayerMsg} {counter : BitVec 32}
    {pad : BitVec 96} (he : encInput e = encRow (leafOf L) message counter pad) : e.1.1 = L := by
  obtain ⟨⟨⟨lay, tree, leaf⟩, m, c, p⟩, hok⟩ := e
  obtain ⟨lay', tree', leaf'⟩ := L
  have ht : tree.val < 2 ^ 40 := lt_of_lt_of_le tree.isLt (by norm_num)
  have ht' : tree'.val < 2 ^ 40 := lt_of_lt_of_le tree'.isLt (by norm_num)
  have hl : leaf.val < 2 ^ 32 := lt_of_lt_of_le leaf.isLt (by norm_num)
  have hl' : leaf'.val < 2 ^ 32 := lt_of_lt_of_le leaf'.isLt (by norm_num)
  obtain ⟨h1, h2, h3, -⟩ := ClaudeWCT.W9.T3M.BC.layerEncodingRow_coords ht hl ht' hl' he
  subst h1
  dsimp only
  rw [Fin.ext h2, Fin.ext h3]
  rfl
theorem matchEntry_cell_le (T : Answers) (e : EncIndex) :
    Pr[fun ans => MatchEntry T (encInput e, ans) | ($ᵗ HashOutput : ProbComp HashOutput)] ≤ (2 ^ 128 : ENNReal)⁻¹ := by
  classical
  let targets : Finset Digest :=
    Finset.univ.filter fun d => decode e.1.1.lay d = some (referenceDigits T (leafOf e.1.1))
  have hcard : targets.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact decode_some_injective (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  calc _ ≤ Pr[fun output => output.extractLsb' 0 128 ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)] := by
        apply probEvent_mono
        rintro ans - ⟨L, message, counter, pad, -, he, -, hdec⟩
        have hL : e.1.1 = L := encInput_leaf he
        subst hL
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdec⟩
    _ = targets.card / (2 : ENNReal) ^ 128 := FirstHit.uniform_low_mem targets
    _ ≤ 1 / (2 : ENNReal) ^ 128 := ENNReal.div_le_div_right (by exact_mod_cast hcard) _
    _ = (2 ^ 128 : ENNReal)⁻¹ := one_div _
theorem matchEntry_other (U : Finset HashInput) (privateTable : FullGame.FullTable) (pub : U → HashOutput)
    (x : HashInput) (hx : ¬ Lazy.IsCell encInput (freeSet (eagerAnswers U privateTable pub)) x) :
    ¬ MatchEntry (eagerAnswers U privateTable pub) (x, eagerAnswers U privateTable pub (.inl (.inr x))) := by
  rintro ⟨L, message, counter, pad, hfit, he, hne, hdec⟩
  have hreached : Reached (eagerAnswers U privateTable pub) (leafOf L) x := by
    by_contra hfree
    have hx' : encInput (encIdx L message counter pad hfit) = x := (encInput_encIdx L message counter pad hfit).trans he.symm
    exact hx ⟨encIdx L message counter pad hfit, by
      change ¬ Reached _ _ (encInput (encIdx L message counter pad hfit))
      rw [hx']
      exact hfree, hx'⟩
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
  exact ⟨_, _, _, _, x.2.1, hx.symm⟩
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
