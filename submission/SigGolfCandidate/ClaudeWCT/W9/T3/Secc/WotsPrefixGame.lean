import SigGolfCandidate.T3.Secc.WotsPrefixGame
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsPrefixGameBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl record realRun lazyRun TwoEdgeEvent Contact)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
noncomputable local instance instFintypeCoordinate_wotsPrefixGame : Fintype Coordinate := coordinateFintype
noncomputable local instance instSampleableTypeFullTable_wotsPrefixGame : SampleableType FullGame.FullTable := Derivation.outputSampler Coordinate
noncomputable local instance instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_wotsPrefixGame (inputs : Finset HashInput) : SampleableType (inputs → HashOutput) :=
  SampleableType.ofFintype _
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
theorem restLaw_eq_prod (adversary : AdversaryP) :
    restLaw adversary = (PMF.uniformOfFintype FullGame.FullTable).bind
      (fun priv => (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)).map (fun pub => (priv, pub))) := by
  unfold restLaw
  rw [← PrefixGame.uniform_prod]
open PrefixGame in
theorem reference_eq_bind (adversary : AdversaryP) (q : Nat) :
    referenceExperiment adversary q = (restLaw adversary).bind
      (fun R => (liftM (offlineRun (restTable R) adversary q) : PMF SeedResult).map (mkSample (restTable R))) := by
  unfold referenceExperiment referenceComp
  rw [liftM_bind, liftM_uniform]
  simp only [liftM_bind, liftM_uniform, liftM_map]
  rw [restLaw_eq_prod, PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype FullGame.FullTable).bind
  funext priv
  rw [PMF.bind_map]
  rfl
open PrefixGame in
theorem restLaw_resample (adversary : AdversaryP) (a : ChainAddr) {β : Type} (F : RefTables adversary → PMF β) :
    (restLaw adversary).bind F = (restLaw adversary).bind (fun R =>
      (PMF.uniformOfFintype (Hidden (restDepth a R))).bind (fun x => F (PrefixGame.ov a (restDepth a R) R x))) := by
  have h := uniform_resample (Ω := RefTables adversary) (X := Hidden) (restDepth a) (fun k R x => PrefixGame.ov a k R x)
    (fun k R => PrefixGame.rd a k R)
    (fun R x => PrefixGame.rd_ov a (by have := PrefixGame.restDepth_le a R; omega) R x)
    (fun R x => PrefixGame.ov_ov_rd a (by have := PrefixGame.restDepth_le a R; omega) R x)
    (fun R x => PrefixGame.restDepth_ov a R x)
  unfold restLaw
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (RefTables adversary)).bind
  funext R
  rw [PMF.bind_map]
  rfl
open PrefixGame in
theorem reference_map_eq_mixture (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) {β : Type} (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (seedGame adversary q a R (evaluate x.1 x.2)) (fun _ _ => none)).support →
      f (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1) = g R (evaluate x.1 x.2, res)) :
    (referenceExperiment adversary q).map f =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)).map (g R)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 32 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by
      generalize a.key.lay = l; unfold height; fin_cases l <;> decide)
    omega
  rw [reference_eq_bind, PMF.map_bind, restLaw_resample adversary a]
  apply congrArg (restLaw adversary).bind
  funext R
  rw [uniform_prod, PMF.bind_bind]
  simp only [PMF.bind_map]
  simp only [realRun, SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
    SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind
  funext t
  apply congrArg (PMF.uniformOfFintype Digest).bind
  funext s
  have hfix := PrefixGame.fixed_seedGame (adversary := adversary) q a htree hleaf R (t, s)
  dsimp only at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R (t, s) res hres
def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < depth answers a ∧ input = chainRow a step value
noncomputable def sampleRows (a : ChainAddr) (s : RefSample) (step : Nat) (value : Digest) : Option Digest :=
  if step < depth s.answers a then
    (s.trace.find? fun e => decide (e.1 = chainRow a step value)).map fun e => low e.2
  else none
noncomputable def prefixCount (a : ChainAddr) (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRowAt s.answers a e.1)).length
noncomputable def sampleView (a : ChainAddr) (s : RefSample) : PrefixView :=
  ⟨depth s.answers a, frontierValue s.answers a, sampleRows a s, prefixCount a s⟩
noncomputable def runView {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) : PrefixView :=
  ⟨restDepth a R, r.1, fun step value => if h : step < restDepth a R then r.2.2 ⟨step, h⟩ value else none,
    seedCost a R r.2.1⟩
open PrefixGame in
theorem sampleView_coupled (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 x.2)) (fun _ _ => none)).support) :
    sampleView a (mkSample (restTable (PrefixGame.ov a (restDepth a R) R x)) res.1) = runView a R (evaluate x.1 x.2, res) := by
  have hd : restDepth a R ≤ 256 := by have := PrefixGame.restDepth_le a R; omega
  have hdepth : depth (restTable (PrefixGame.ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (PrefixGame.ov a (restDepth a R) R x)).symm.trans (PrefixGame.restDepth_ov a R x)
  have hrows : ∀ (i : Fin (restDepth a R)) (v : Digest), res.2 i v =
      if (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ res.1.2 then some (x.1 i v) else none := by
    unfold seedGame at hres
    revert hres
    intro hres i v
    exact PrefixGame.observed_rows a hd R x.1 _ (fun _ _ => none) res hres i v
  unfold sampleView runView mkSample
  simp only
  rw [PrefixView.mk.injEq]
  refine ⟨hdepth, PrefixGame.frontierValue_ov a R x, ?_, ?_⟩
  · funext step value
    unfold sampleRows
    simp only
    rw [hdepth]
    by_cases hs : step < restDepth a R
    · rw [if_pos hs, dif_pos hs, traceOf_find, hrows ⟨step, hs⟩ value]
      by_cases hm : (.inl (.inr (chainRow a step value)) : RefWorld.Domain) ∈ res.1.2
      · rw [if_pos hm, if_pos hm]
        simp only [Option.map_some]
        rw [low, PrefixGame.restTable_ov_prefix a hd R x ⟨step, hs⟩ value, ChainGraph.joinOutput_low]
      · rw [if_neg hm, if_neg hm]
        rfl
    · rw [if_neg hs, dif_neg hs]
  · unfold prefixCount seedCost
    simp only
    rw [traceOf_filter_length]
    congr 1
    funext query
    apply propext
    constructor
    · rintro ⟨y, rfl, step, value, hs, rfl⟩
      rw [hdepth] at hs
      exact ⟨⟨step, hs⟩, value, rfl⟩
    · rintro ⟨i, v, rfl⟩
      exact ⟨_, rfl, i, v, by rw [hdepth]; exact i.isLt, rfl⟩
theorem reference_eq_mixture (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    (referenceExperiment adversary q).map (sampleView a) =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)).map (runView a R)) :=
  reference_map_eq_mixture adversary q a ha (sampleView a) (runView a)
    (sampleView_coupled adversary q a)
theorem reference_support_trace (adversary : AdversaryP) (q : Nat) (s : RefSample)
    (hs : s ∈ (referenceExperiment adversary q).support) : ∃ qs, s.trace = traceOf s.answers qs := by
  rw [reference_eq_bind, PMF.mem_support_bind_iff] at hs
  obtain ⟨R, -, hs⟩ := hs
  rw [PMF.mem_support_map_iff] at hs
  obtain ⟨run, -, rfl⟩ := hs
  exact ⟨run.2, rfl⟩
theorem sampleRows_eq_some (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) (step : Nat) (value out : Digest) :
    sampleRows a s step value = some out ↔ step < depth s.answers a ∧ SeenRow s.trace a step value out := by
  unfold sampleRows SeenRow
  rw [hs, traceOf_find]
  by_cases hstep : step < depth s.answers a
  · rw [if_pos hstep]
    by_cases hm : (.inl (.inr (chainRow a step value)) : RefWorld.Domain) ∈ qs
    · rw [if_pos hm]
      simp only [Option.map_some, Option.some.injEq, hstep, true_and]
      constructor
      · rintro rfl
        exact ⟨_, (mem_traceOf _ _ _ _).mpr ⟨hm, rfl⟩, rfl⟩
      · rintro ⟨answer, hmem, rfl⟩
        rw [((mem_traceOf _ _ _ _).mp hmem).2]
    · rw [if_neg hm]
      simp only [Option.map_none, reduceCtorEq, false_iff, not_and, not_exists]
      intro _ answer hmem
      exact absurd ((mem_traceOf _ _ _ _).mp hmem).1 hm
  · rw [if_neg hstep]
    simp only [reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h hstep
theorem twoEdgeAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    TwoEdgeAt s.answers s.trace a ↔ (sampleView a s).TwoEdge := by
  unfold TwoEdgeAt PrefixView.TwoEdge sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    exact ⟨hd, start, middle, ⟨by omega, h1⟩, ⟨by omega, h2⟩⟩
  · rintro ⟨hd, start, middle, ⟨-, h1⟩, ⟨-, h2⟩⟩
    exact ⟨hd, start, middle, h1, h2⟩
theorem contactAt_iff_view (a : ChainAddr) (s : RefSample) (qs : List RefWorld.Domain)
    (hs : s.trace = traceOf s.answers qs) :
    ContactAt s.answers s.trace a ↔ (sampleView a s).Contact := by
  unfold ContactAt PrefixView.Contact sampleView
  simp only [sampleRows_eq_some a s qs hs]
  constructor
  · rintro ⟨hd, value, h⟩
    exact ⟨hd, value, ⟨by omega, h⟩⟩
  · rintro ⟨hd, value, ⟨-, h⟩⟩
    exact ⟨hd, value, h⟩
theorem runView_twoEdge {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) :
    (runView a R r).TwoEdge ↔ TwoEdgeEvent r.2.2 r.1 := by
  rw [SphincsSecurity.Concrete.PartialChainEndpoint.twoEdgeEvent_iff_rows]
  unfold PrefixView.TwoEdge runView
  simp only
  constructor
  · rintro ⟨hd, start, middle, h1, h2⟩
    rw [dif_pos (by omega)] at h1 h2
    exact ⟨(⟨restDepth a R - 2, by omega⟩, start), (⟨restDepth a R - 1, by omega⟩, middle),
      by simp only; omega, by simp only; omega, h1, h2⟩
  · rintro ⟨⟨i, start⟩, ⟨j, middle⟩, hi, hj, h1, h2⟩
    simp only at hi hj h1 h2
    refine ⟨by omega, start, middle, ?_, ?_⟩
    · rw [dif_pos (by omega)]
      have : (⟨restDepth a R - 2, by omega⟩ : Fin (restDepth a R)) = i := Fin.ext (by simp only; omega)
      rw [this]; exact h1
    · rw [dif_pos (by omega)]
      have : (⟨restDepth a R - 1, by omega⟩ : Fin (restDepth a R)) = j := Fin.ext (by simp only; omega)
      rw [this]; exact h2
theorem runView_contact {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) :
    (runView a R r).Contact ↔ Contact r.2.2 r.1 := by
  unfold PrefixView.Contact runView Contact
  simp only
  constructor
  · rintro ⟨hd, value, h⟩
    rw [dif_pos (by omega)] at h
    exact ⟨⟨restDepth a R - 1, by omega⟩, by simp only; omega, value, h⟩
  · rintro ⟨i, hi, value, h⟩
    refine ⟨by omega, value, ?_⟩
    rw [dif_pos (by omega)]
    have : (⟨restDepth a R - 1, by omega⟩ : Fin (restDepth a R)) = i := Fin.ext (by simp only; omega)
    rw [this]; exact h
theorem reference_view_prob (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a)
    (E : PrefixView → Prop) :
    Pr[fun s => E (sampleView a s) | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[fun r => E (runView a R r) |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF PrefixView => Pr[E | law]) (reference_eq_mixture adversary q a ha)
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply] at h
  exact h
theorem reference_view_expectation (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (f : PrefixView → ENNReal) :
    ∑' s, referenceExperiment adversary q s * f (sampleView a s) =
      ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none) r * f (runView a R r) := by
  have h := congrArg (fun law : PMF PrefixView => ∑' v, law v * f v) (reference_eq_mixture adversary q a ha)
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind] at h
  exact h
theorem reference_twoEdgeAt_eq (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[fun r => TwoEdgeEvent r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] := by
  have h1 : Pr[fun s => TwoEdgeAt s.answers s.trace a | referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).TwoEdge | referenceExperiment adversary q] := by
    apply pmf_probEvent_congr
    intro s hs
    obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
    exact twoEdgeAt_iff_view a s qs hqs
  rw [h1, reference_view_prob adversary q a ha PrefixView.TwoEdge]
  simp only [runView_twoEdge]
theorem reference_contactAt_eq (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[fun r => Contact r.2.2 r.1 |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)] := by
  have h1 : Pr[fun s => ContactAt s.answers s.trace a | referenceExperiment adversary q] =
      Pr[fun s => (sampleView a s).Contact | referenceExperiment adversary q] := by
    apply pmf_probEvent_congr
    intro s hs
    obtain ⟨qs, hqs⟩ := reference_support_trace adversary q s hs
    exact contactAt_iff_view a s qs hqs
  rw [h1, reference_view_prob adversary q a ha PrefixView.Contact]
  simp only [runView_contact]
theorem reference_prefixCount_eq (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) =
      ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
  reference_view_expectation adversary q a ha (fun v => (v.count : ENNReal))
end ClaudeWCT.W9.T3.Security.Wots
