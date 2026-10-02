import SigGolfCandidate.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapCost
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsTwoEdgeTrace

/-!
# Stream C: the per-address mixture identity of R3 (record `prefixInstrumentedObservedGame_original`)

For a source chain `a`, R3's law, projected to what the chain events of `a` read, is a mixture over the rest
`R ∼ restLaw` of the generic real run `realRun (fun _ => uniformImpl) (seedGame adversary q a R) (fun _ _ => none)`:

* `reference_map_eq_mixture` (general form): any projection `f` of R3 equals the mixture of any projection `g` of the
  generic run, provided `f` and `g` agree on the coupled samples (`hfg`);
* `reference_eq_mixture` (view form): `(referenceExperiment adversary q).map (sampleView a) =
  (restLaw adversary).bind fun R => (realRun … (seedGame adversary q a R) …).map (runView a R)`, where the view
  holds `a`'s depth, frontier value, the low answers of `a`'s prefix rows seen in the trace, and their number
  (= `seedCost`). On the run side the view is `(restDepth a R, endpoint, observed, seedCost)`, i.e. the observed
  table is exactly `a`'s prefix rows of R3's trace (record `instrumentedContact_rows`).
* `twoEdgeAt_iff_view`, `contactAt_iff_view` (R3 side, on the support) and `twoEdge_runView`, `contact_runView`
  (generic side): `TwoEdgeAt ↔ TwoEdgeEvent observed endpoint`, `ContactAt ↔ Contact observed endpoint`.

The proof: R3 is a bind over its tables (`reference_eq_bind`); the tables' law is invariant under resampling `a`'s
hidden part (`restLaw_resample`, from `PrefixGame.uniform_resample`); on an overwritten table R3's offline run is the
generic `fixedImpl` run of `seedGame` (`PrefixGame.fixed_seedGame`), i.e. the forgetful image of the generic
`observedRun`; the generic `realRun` from the empty observation is exactly this bind.
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
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

/-! ## Probabilistic computations as PMFs -/

theorem liftM_bind {α β : Type} (c : ProbComp α) (f : α → ProbComp β) :
    (liftM (c >>= f) : PMF β) = (liftM c : PMF α).bind (fun x => (liftM (f x) : PMF β)) := by
  show simulateQ _ (c >>= f) = _
  rw [simulateQ_bind]
  rfl

theorem liftM_map {α β : Type} (c : ProbComp α) (f : α → β) :
    (liftM (f <$> c) : PMF β) = (liftM c : PMF α).map f := by
  show simulateQ _ (f <$> c) = _
  rw [simulateQ_map]
  rfl

theorem liftM_apply {α : Type} (c : ProbComp α) (x : α) : (liftM c : PMF α) x = Pr[= x | c] := by
  rw [← PMF.probOutput_eq_apply]
  have h1 : 𝒮[(liftM c : PMF α)] = 𝒮[c] := by
    rw [evalSPMF_eq_simulateQ, PMF.evalSPMF_eq]
    rfl
  unfold probOutput
  rw [h1]

theorem liftM_uniform (α : Type) [Fintype α] [Nonempty α] [SampleableType α] :
    (liftM ($ᵗ α : ProbComp α) : PMF α) = PMF.uniformOfFintype α := by
  apply PMF.ext
  intro x
  rw [liftM_apply, probOutput_uniformSample, PMF.uniformOfFintype_apply]

/-- Maps agreeing on the support are equal. -/
theorem map_congr_support {α β : Type} (p : PMF α) (f g : α → β) (h : ∀ x ∈ p.support, f x = g x) :
    p.map f = p.map g := by
  apply PMF.ext
  intro y
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · rw [h x hx]
  · rw [PMF.apply_eq_zero_iff p x |>.mpr hx]
    simp only [ite_self]

theorem uniform_prod (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind (fun x => (PMF.uniformOfFintype β).map (fun y => (x, y))) :=
  SphincsSecurity.Concrete.UniformTableSplit.uniform_product

end PrefixGame

/-! ## R3 as a bind over its tables -/

/-- The R3 sample of a table and a recorded run. -/
noncomputable def mkSample (T : Answers) (run : SeedResult) : RefSample :=
  ⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩

theorem restLaw_eq_prod (adversary : AdversaryP) :
    restLaw adversary = (PMF.uniformOfFintype FullGame.FullTable).bind
      (fun priv => (PMF.uniformOfFintype (referenceInputs adversary → HashOutput)).map (fun pub => (priv, pub))) := by
  unfold restLaw
  rw [← PrefixGame.uniform_prod]

open PrefixGame in
/-- **R3 is a bind over its tables.** -/
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

/-! ## Resampling `a`'s hidden part of the rest -/

open PrefixGame in
/-- The law of the rest is invariant under resampling `a`'s hidden part. -/
theorem restLaw_resample (adversary : AdversaryP) (a : ChainAddr) {β : Type} (F : RefTables adversary → PMF β) :
    (restLaw adversary).bind F = (restLaw adversary).bind (fun R =>
      (PMF.uniformOfFintype (Hidden (restDepth a R))).bind (fun x => F (ov a (restDepth a R) R x))) := by
  have h := uniform_resample (Ω := RefTables adversary) (X := Hidden) (restDepth a) (fun k R x => ov a k R x)
    (fun k R => rd a k R)
    (fun R x => rd_ov a (by have := restDepth_le a R; omega) R x)
    (fun R x => ov_ov_rd a (by have := restDepth_le a R; omega) R x)
    (fun R x => restDepth_ov a R x)
  unfold restLaw
  conv_lhs => rw [← h]
  rw [PMF.bind_bind]
  apply congrArg (PMF.uniformOfFintype (RefTables adversary)).bind
  funext R
  rw [PMF.bind_map]
  rfl

/-! ## The general mixture identity -/

open PrefixGame in
/-- **Per-address mixture identity (general form).** Any projection `f` of R3 equals the mixture over the rest of
the projection `g` of the generic real run of `seedGame`, provided they agree on every coupled sample: an overwrite
`x` of `a`'s hidden part of the rest and an observed run of `seedGame` with the tables `x.1`. -/
theorem reference_map_eq_mixture (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) {β : Type} (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
        (seedGame adversary q a R (evaluate x.1 x.2)) (fun _ _ => none)).support →
      f (mkSample (restTable (ov a (restDepth a R) R x)) res.1) = g R (evaluate x.1 x.2, res)) :
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
  -- the generic real run from the empty observation
  simp only [realRun, SphincsSecurity.Concrete.PartialChainEndpoint.completeTables_empty,
    SphincsSecurity.Concrete.EndpointPreimageDensity.real, PMF.map_bind, PMF.bind_bind, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  apply congrArg (PMF.uniformOfFintype (Fin (restDepth a R) → Digest → Digest)).bind
  funext t
  apply congrArg (PMF.uniformOfFintype Digest).bind
  funext s
  have hfix := fixed_seedGame (adversary := adversary) q a htree hleaf R (t, s)
  dsimp only at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R (t, s) res hres

/-! ## Traces of recorded query lists -/

theorem mem_traceOf (T : Answers) (qs : List RefWorld.Domain) (input : HashInput) (answer : HashOutput) :
    (input, answer) ∈ traceOf T qs ↔
      (.inl (.inr input) : RefWorld.Domain) ∈ qs ∧ answer = T (.inl (.inr input)) := by
  unfold traceOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨query, hq, he⟩
    rcases query with (n | x) | u
    · cases he
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨hq, rfl⟩
    · cases he
  · rintro ⟨hq, rfl⟩
    exact ⟨_, hq, rfl⟩

theorem traceOf_find (T : Answers) (x : HashInput) :
    ∀ qs : List RefWorld.Domain, (traceOf T qs).find? (fun e => decide (e.1 = x)) =
      if (.inl (.inr x) : RefWorld.Domain) ∈ qs then some (x, T (.inl (.inr x))) else none
  | [] => by simp [traceOf]
  | query :: qs => by
      rcases query with (n | input) | u
      · have h : traceOf T (.inl (.inl n) :: qs) = traceOf T qs := rfl
        rw [h, traceOf_find T x qs]
        simp
      · have h : traceOf T (.inl (.inr input) :: qs) = (input, T (.inl (.inr input))) :: traceOf T qs := rfl
        rw [h, List.find?_cons]
        by_cases hx : input = x
        · subst hx
          simp only [decide_true, List.mem_cons, true_or, if_true]
        · rw [show decide ((input, T (.inl (.inr input))).1 = x) = false from decide_eq_false hx]
          simp only
          rw [traceOf_find T x qs]
          have hne : (.inl (.inr x) : RefWorld.Domain) ≠ .inl (.inr input) := fun he => hx (by cases he; rfl)
          simp only [List.mem_cons, hne, false_or]
      · have h : traceOf T (.inr u :: qs) = traceOf T qs := rfl
        rw [h, traceOf_find T x qs]
        simp

theorem traceOf_filter_length (T : Answers) (P : HashInput → Prop) :
    ∀ qs : List RefWorld.Domain, ((traceOf T qs).filter fun e => decide (P e.1)).length =
      SphincsSecurity.QueryCap.calls (fun query : RefWorld.Domain => ∃ x, query = .inl (.inr x) ∧ P x) qs
  | [] => rfl
  | query :: qs => by
      rw [SphincsSecurity.QueryCap.calls_cons, ← traceOf_filter_length T P qs]
      rcases query with (n | input) | u
      · have h : traceOf T (.inl (.inl n) :: qs) = traceOf T qs := rfl
        rw [h, if_neg]
        · simp only [Nat.zero_add]
        · rintro ⟨x, hx, -⟩
          cases hx
      · have h : traceOf T (.inl (.inr input) :: qs) = (input, T (.inl (.inr input))) :: traceOf T qs := rfl
        rw [h, List.filter_cons]
        by_cases hp : P input
        · rw [if_pos (decide_eq_true hp), if_pos ⟨input, rfl, hp⟩, List.length_cons]
          omega
        · rw [if_neg (by simpa using hp), if_neg]
          · simp only [Nat.zero_add]
          · rintro ⟨x, hx, hpx⟩
            cases hx
            exact hp hpx
      · have h : traceOf T (.inr u :: qs) = traceOf T qs := rfl
        rw [h, if_neg]
        · simp only [Nat.zero_add]
        · rintro ⟨x, hx, -⟩
          cases hx

/-! ## The per-address view -/

/-- `input` is a canonical prefix row of `a` (step below the frontier). -/
def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < depth answers a ∧ input = chainRow a step value

/-- What the chain events of one address read: its depth, its frontier value, the low answers of its prefix rows
(`none`: not seen, or not a prefix step) and the number of its prefix rows. -/
structure PrefixView where
  depth : Nat
  frontier : Digest
  rows : Nat → Digest → Option Digest
  count : Nat

/-- The low answer of `a`'s prefix row `(step, value)` in the trace, if seen. -/
noncomputable def sampleRows (a : ChainAddr) (s : RefSample) (step : Nat) (value : Digest) : Option Digest :=
  if step < depth s.answers a then
    (s.trace.find? fun e => decide (e.1 = chainRow a step value)).map fun e => low e.2
  else none

/-- The number of `a`'s prefix-row entries in the trace. -/
noncomputable def prefixCount (a : ChainAddr) (s : RefSample) : Nat :=
  (s.trace.filter fun e => decide (PrefixRowAt s.answers a e.1)).length

/-- The view of an R3 sample at address `a`. -/
noncomputable def sampleView (a : ChainAddr) (s : RefSample) : PrefixView :=
  ⟨depth s.answers a, frontierValue s.answers a, sampleRows a s, prefixCount a s⟩

/-- The view of a generic real-run result: `(restDepth, endpoint, observed, seedCost)`. -/
noncomputable def runView {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary)
    (r : Digest × (SeedResult × (Fin (restDepth a R) → Digest → Option Digest))) : PrefixView :=
  ⟨restDepth a R, r.1, fun step value => if h : step < restDepth a R then r.2.2 ⟨step, h⟩ value else none,
    seedCost a R r.2.1⟩

open PrefixGame in
/-- **On a coupled sample, the two views agree** (the observed table is `a`'s prefix rows of R3's trace). -/
theorem sampleView_coupled (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (res : SeedResult × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 x.2)) (fun _ _ => none)).support) :
    sampleView a (mkSample (restTable (ov a (restDepth a R) R x)) res.1) = runView a R (evaluate x.1 x.2, res) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  have hrows : ∀ (i : Fin (restDepth a R)) (v : Digest), res.2 i v =
      if (.inl (.inr (chainRow a i v)) : RefWorld.Domain) ∈ res.1.2 then some (x.1 i v) else none := by
    unfold seedGame at hres
    revert hres
    intro hres i v
    exact observed_rows a hd R x.1 _ (fun _ _ => none) res hres i v
  unfold sampleView runView mkSample
  simp only
  rw [PrefixView.mk.injEq]
  refine ⟨hdepth, frontierValue_ov a R x, ?_, ?_⟩
  · funext step value
    unfold sampleRows
    simp only
    rw [hdepth]
    by_cases hs : step < restDepth a R
    · rw [if_pos hs, dif_pos hs, traceOf_find, hrows ⟨step, hs⟩ value]
      by_cases hm : (.inl (.inr (chainRow a step value)) : RefWorld.Domain) ∈ res.1.2
      · rw [if_pos hm, if_pos hm]
        simp only [Option.map_some]
        rw [low, restTable_ov_prefix a hd R x ⟨step, hs⟩ value, ChainGraph.joinOutput_low]
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

/-- **Per-address mixture identity (view form).** -/
theorem reference_eq_mixture (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    (referenceExperiment adversary q).map (sampleView a) =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)).map (runView a R)) :=
  reference_map_eq_mixture adversary q a ha (sampleView a) (runView a)
    (sampleView_coupled adversary q a)

/-! ## Events through the view -/

/-- Two-edge event read off a view. -/
def PrefixView.TwoEdge (v : PrefixView) : Prop :=
  2 ≤ v.depth ∧ ∃ start middle, v.rows (v.depth - 2) start = some middle ∧ v.rows (v.depth - 1) middle = some v.frontier

/-- Contact event read off a view. -/
def PrefixView.Contact (v : PrefixView) : Prop :=
  1 ≤ v.depth ∧ ∃ value, v.rows (v.depth - 1) value = some v.frontier

/-- Every R3 sample's trace is the trace of a recorded query list under the sample's table. -/
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

/-- On R3's support, `TwoEdgeAt` is the view's two-edge event. -/
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

/-- On R3's support, `ContactAt` is the view's contact event. -/
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

/-- On the generic side, the view's two-edge event is the generic `TwoEdgeEvent`. -/
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

/-- On the generic side, the view's contact event is the generic `Contact`. -/
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

/-! ## Probabilities and expectations through the mixture -/

/-- Events equivalent on the support of a PMF have equal probability. -/
theorem pmf_probEvent_congr {α : Type} (p : PMF α) (E F : α → Prop) (h : ∀ x ∈ p.support, E x ↔ F x) :
    Pr[E | p] = Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ p.support
  · by_cases he : E x
    · rw [if_pos he, if_pos ((h x hx).mp he)]
    · rw [if_neg he, if_neg (fun hf => he ((h x hx).mpr hf))]
  · rw [PMF.probOutput_eq_apply, (PMF.apply_eq_zero_iff p x).mpr hx]
    simp only [ite_self]

/-- Monotonicity of event probabilities on the support of a PMF. -/
theorem pmf_probEvent_mono {α : Type} (p : PMF α) (E F : α → Prop) (h : ∀ x ∈ p.support, E x → F x) :
    Pr[E | p] ≤ Pr[F | p] := by
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro x
  by_cases he : E x
  · by_cases hx : x ∈ p.support
    · rw [if_pos he, if_pos (h x hx he)]
    · rw [if_pos he, PMF.probOutput_eq_apply, (PMF.apply_eq_zero_iff p x).mpr hx]
      exact bot_le
  · rw [if_neg he]
    exact bot_le

/-- Event probabilities of the view transfer through the mixture identity. -/
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

/-- Expectations of view functions transfer through the mixture identity. -/
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

/-- **Two-edge at `a` in R3 = mixture of the generic two-edge event.** -/
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

/-- **Contact at `a` in R3 = mixture of the generic contact event.** -/
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

/-- **The expected number of `a`'s prefix entries in R3 = mixture of the expected generic cost.** -/
theorem reference_prefixCount_eq (adversary : AdversaryP) (q : Nat) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    ∑' s, referenceExperiment adversary q s * (prefixCount a s : ENNReal) =
      ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none) r * (seedCost a R r.2.1 : ENNReal) :=
  reference_view_expectation adversary q a ha (fun v => (v.count : ENNReal))

end SigGolfCandidate.T3.Security.Wots
