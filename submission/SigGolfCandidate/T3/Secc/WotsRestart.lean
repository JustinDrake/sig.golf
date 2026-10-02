import SigGolfCandidate.T3.Secc.WotsRestartBase

/-!
# Stream C (restart): a contact of `a` after the first stop of the trace (G4 on R3)

For a source chain `a` and a stop predicate on trace prefixes that depends on the table only through `maskAt · a`
(i.e. not on `a`'s hidden part beyond its frontier value; every honest object qualifies):
```
ContactAfterStop Stop T trace a := ∃ k, Stop T (trace.take k) ∧ ¬ContactAt T (trace.take k) a ∧ ContactAt T trace a
reference_contactAfterStop_le :
  (1 − x) · (2^128 · Pr_R3[ContactAfterStop Stop · a]) ≤ (2q) · Pr_R3[∃ k, Stop (trace.take k)]
```
(flat G4 `realCheckpointRun_contact_le_mark`; the checkpoint is R3 paused at the first stop, `PrefixGame.seedBefore`,
the restart its remainder, `PrefixGame.seedAfter`). Stream E instantiates `Stop := MarkerAt · · a` (marker-first);
stream C instantiates "a contact at another source chain" (two contacts).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity.Concrete.PartialChainEndpoint (PrefixSpec fixedImpl evaluate IsPrefixQuery observedRun
  observedImpl lazyImpl record realRun idealRun lazyRun TwoEdgeEvent Contact queryCount realCheckpointRun)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame

namespace PrefixGame

variable {adversary : AdversaryP}

/-! ## The general mixture identity for a game refining `seedGame` -/

/-- **Mixture identity for any per-address game whose output projects to `seedGame`.** -/
theorem reference_map_eq_mixture_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) {Res β : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (f : RefSample → β)
    (g : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → β)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      f (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) = g R (evaluate x.1 x.2, res)) :
    (referenceExperiment adversary q).map f =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)).map (g R)) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 32 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
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
  have hfix := fixed_seedGame (adversary := adversary) q a htree hleaf R (t, s)
  dsimp only at hfix
  rw [← hgame, simulateQ_map, PMF.monad_map_eq_map] at hfix
  rw [← hfix, ← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
    PMF.map_comp, PMF.map_comp]
  exact map_congr_support _ _ _ fun res hres => hfg R (t, s) res hres

/-- Probability form of `reference_map_eq_mixture_of`. -/
theorem reference_prob_eq_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) {Res : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (E : RefSample → Prop)
    (F : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → Prop)
    (hEF : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      (E (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) ↔ F R (evaluate x.1 x.2, res))) :
    Pr[E | referenceExperiment adversary q] =
      ∑' R, restLaw adversary R * Pr[F R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)] := by
  have h := congrArg (fun law : PMF Prop => Pr[fun p => p | law])
    (reference_map_eq_mixture_of q a ha game out hgame E F (fun R x res hres => propext (hEF R x res hres)))
  simp only [← PMF.monad_map_eq_map, probEvent_map, ← PMF.monad_bind_eq_bind, probEvent_bind_eq_tsum,
    PMF.probOutput_eq_apply, Function.comp_def] at h
  exact h

/-- Expectation form of `reference_map_eq_mixture_of`. -/
theorem reference_expectation_eq_of (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) {Res : Type}
    (game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) Res)
    (out : Res → SeedResult) (hgame : ∀ R endpoint, out <$> game R endpoint = seedGame adversary q a R endpoint)
    (f : RefSample → ENNReal)
    (g : (R : RefTables adversary) → Digest × (Res × (Fin (restDepth a R) → Digest → Option Digest)) → ENNReal)
    (hfg : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R))
      (res : Res × (Fin (restDepth a R) → Digest → Option Digest)),
      res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1 (game R (evaluate x.1 x.2))
        (fun _ _ => none)).support →
      f (mkSample (restTable (ov a (restDepth a R) R x)) (out res.1)) = g R (evaluate x.1 x.2, res)) :
    ∑' s, referenceExperiment adversary q s * f s =
      ∑' R, restLaw adversary R * ∑' r,
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none) r * g R r := by
  have h := congrArg (fun law : PMF ENNReal => ∑' v, law v * v)
    (reference_map_eq_mixture_of q a ha game out hgame f g hfg)
  simp only [SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map,
    SphincsSecurity.Concrete.PartialChainEndpoint.expectation_bind] at h
  exact h

/-! ## Coupled samples of the paused game -/

/-- Answering the paused game's prefix queries by the tables of an overwrite is the paused R3 run on the overwritten
table. -/
theorem fixed_pausedSeed (q : Nat) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32)
    (R : RefTables adversary) (x : Hidden (restDepth a R)) (stop : List Entry → Prop) :
    simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
        (pausedSeed adversary q a R stop (evaluate x.1 x.2)) =
      (liftM (simulateQ (refImpl (restTable (ov a (restDepth a R) R x)))
        (pausedFull stop (referenceGame (restTable (ov a (restDepth a R) R x)) adversary q) [])) :
          PMF (List Entry × SeedResult)) := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  unfold pausedSeed
  rw [← QueryImpl.simulateQ_compose, fixed_route a hd R x, ← referenceGame_fill a htree hleaf R x q,
    QueryImpl.simulateQ_compose]
  rfl

/-- On a coupled sample, the pause memory has the structure of `paused_structure` w.r.t. the full trace. -/
theorem coupled_paused (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) (R : RefTables adversary)
    (x : Hidden (restDepth a R)) (stop : List Entry → Prop)
    (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 x.2)) (fun _ _ => none)).support) :
    res.1.1 = (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take res.1.1.length ∧
      (∀ j, j < res.1.1.length → ¬stop ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take j)) ∧
      (stop res.1.1 ∨ res.1.1 = traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) := by
  have htree : a.key.tree < 2 ^ 40 := by have := ha.1.1; omega
  have hleaf : a.key.leaf < 2 ^ 32 := by
    have h1 := ha.1.2
    have h2 : 2 ^ height a.key.lay ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) (by
      have := height_le a.key.lay; omega)
    omega
  have hfst : res.1 ∈ (simulateQ (fixedImpl SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1)
      (pausedSeed adversary q a R stop (evaluate x.1 x.2))).support := by
    rw [← SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_forget _ _ _ (fun _ _ => none),
      PMF.mem_support_map_iff]
    exact ⟨res, hres, rfl⟩
  rw [fixed_pausedSeed q a htree hleaf R x stop] at hfst
  have hmem := SphincsSecurity.QueryCap.simulate_mem_support SphincsSecurity.Concrete.OtsPrefix.uniformImpl _ _ hfst
  obtain ⟨-, h2, h3, h4⟩ := paused_structure _ stop _ [] res.1 hmem
  simp only [List.nil_append, List.length_nil, Nat.zero_le, true_implies] at h2 h3 h4
  exact ⟨h2, h3, h4⟩

/-- On a coupled sample of the paused game, the final observed table is `a`'s prefix rows of the full trace. -/
theorem coupled_paused_rows (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 x.2)) (fun _ _ => none)).support) :
    (res.1.2, res.2) ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (seedGame adversary q a R (evaluate x.1 x.2)) (fun _ _ => none)).support := by
  rw [← pausedSeed_snd q a R stop, SphincsSecurity.Concrete.PartialChainEndpoint.observedRun_map,
    PMF.mem_support_map_iff]
  exact ⟨res, hres, rfl⟩


/-! ## Events -/

theorem contactAt_take_mono (T : Answers) (trace : List Entry) (a : ChainAddr) {j k : Nat} (hjk : j ≤ k)
    (h : ContactAt T (trace.take j) a) : ContactAt T (trace.take k) a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, (List.take_prefix_take_left hjk).subset hm, hl⟩

theorem contactAt_take_full (T : Answers) (trace : List Entry) (a : ChainAddr) {k : Nat}
    (h : ContactAt T (trace.take k) a) : ContactAt T trace a := by
  obtain ⟨hd, value, answer, hm, hl⟩ := h
  exact ⟨hd, value, answer, List.mem_of_mem_take hm, hl⟩

theorem contactAt_congr {T T' : Answers} (trace : List Entry) (a : ChainAddr) (hd : depth T a = depth T' a)
    (hf : frontierValue T a = frontierValue T' a) : ContactAt T trace a ↔ ContactAt T' trace a := by
  unfold ContactAt
  rw [hd, hf]

/-- The first stop of a trace decides "a stop with no contact yet, then a contact". -/
theorem first_stop_iff {trace memory : List Entry} (S C : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) (hC : ∀ j k, j ≤ k → C (trace.take j) → C (trace.take k)) :
    (∃ k, S (trace.take k) ∧ ¬C (trace.take k) ∧ C trace) ↔ (S memory ∧ ¬C memory ∧ C trace) := by
  constructor
  · rintro ⟨k, hs, hnc, hct⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    have hnm : ¬C memory := fun hcm => hnc (hC _ _ hk (hm ▸ hcm))
    refine ⟨?_, hnm, hct⟩
    rcases hc with hc | hc
    · exact hc
    · exact absurd (hc ▸ hct) hnm
  · rintro ⟨hs, hnc, hct⟩
    exact ⟨memory.length, hm ▸ hs, hm ▸ hnc, hct⟩

/-- The first stop of a trace decides "some prefix stops". -/
theorem first_stop_exists_iff {trace memory : List Entry} (S : List Entry → Prop)
    (hm : memory = trace.take memory.length) (hb : ∀ j, j < memory.length → ¬S (trace.take j))
    (hc : S memory ∨ memory = trace) : (∃ k, S (trace.take k)) ↔ S memory := by
  constructor
  · rintro ⟨k, hs⟩
    have hk : memory.length ≤ k := by
      by_contra h
      exact hb k (by omega) hs
    rcases hc with hc | hc
    · exact hc
    · have : trace.take k = memory := by
        rw [hc]; exact List.take_of_length_le (by rw [← hc]; exact hk)
      exact this ▸ hs
  · intro hs
    exact ⟨memory.length, hm ▸ hs⟩

theorem fillTable_depth (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) :
    depth (fillTable a R endpoint) a = restDepth a R :=
  (restDepth_eq a (ov a (restDepth a R) R _)).symm.trans (restDepth_ov a R _)

theorem fillTable_frontier (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) :
    frontierValue (fillTable a R endpoint) a = endpoint := by
  unfold fillTable
  rw [frontierValue_ov]
  exact evaluate_const _ endpoint

/-- With `RowsInv`, the generic contact on the observed table is `ContactAt` on the memory. -/
theorem contact_iff_rowsInv (a : ChainAddr) (R : RefTables adversary) (endpoint : Digest) (memory : List Entry)
    (observed : Fin (restDepth a R) → Digest → Option Digest) (hinv : RowsInv a memory observed) :
    Contact observed endpoint ↔ ContactAt (fillTable a R endpoint) memory a := by
  unfold Contact ContactAt SeenRow
  rw [fillTable_depth, fillTable_frontier]
  constructor
  · rintro ⟨i, hi, value, h⟩
    obtain ⟨answer, hm, hl⟩ := (hinv i value endpoint).mp h
    refine ⟨by omega, value, answer, ?_, hl⟩
    rw [show restDepth a R - 1 = i.val by omega]
    exact hm
  · rintro ⟨hd, value, answer, hm, hl⟩
    refine ⟨⟨restDepth a R - 1, by omega⟩, by simp only; omega, value, (hinv _ value endpoint).mpr ⟨answer, hm, hl⟩⟩

end PrefixGame

open PrefixGame in
/-- A contact of `a` after the first stop of the trace (with no contact of `a` at the stop). -/
def ContactAfterStop (Stop : Answers → List Entry → Prop) (T : Answers) (trace : List Entry) (a : ChainAddr) : Prop :=
  ∃ k, Stop T (trace.take k) ∧ ¬ContactAt T (trace.take k) a ∧ ContactAt T trace a

namespace PrefixGame

variable {adversary : AdversaryP}

/-- On a coupled sample, the final generic contact is R3's `ContactAt` on the full trace. -/
theorem coupled_contact (q : Nat) (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R))
    (stop : List Entry → Prop) (res : (List Entry × SeedResult) × (Fin (restDepth a R) → Digest → Option Digest))
    (hres : res ∈ (observedRun SphincsSecurity.Concrete.OtsPrefix.uniformImpl x.1
      (pausedSeed adversary q a R stop (evaluate x.1 x.2)) (fun _ _ => none)).support) :
    ContactAt (restTable (ov a (restDepth a R) R x)) (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
      Contact res.2 (evaluate x.1 x.2) := by
  have hview := sampleView_coupled adversary q a R x (res.1.2, res.2) (coupled_paused_rows q a R x stop res hres)
  have h1 := contactAt_iff_view a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) res.1.2.2 rfl
  rw [hview, runView_contact] at h1
  exact h1

end PrefixGame

open PrefixGame in
/-- **Contact after the first stop (G4, flat form).** For a source chain `a` and a stop predicate reading the table
only through `maskAt · a`:
`(1 − x) · (2^128 · Pr_R3[ContactAfterStop Stop · a]) ≤ 2q · Pr_R3[some prefix of the trace stops]`. -/
theorem reference_contactAfterStop_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (Stop : Answers → List Entry → Prop)
    (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => ∃ k, Stop s.answers (s.trace.take k) | referenceExperiment adversary q] := by
  -- the per-address paused game with the endpoint-dependent stop
  let stopAt : (R : RefTables adversary) → Digest → List Entry → Prop := fun R e trace => Stop (fillTable a R e) trace
  let game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
    fun R e => pausedSeed adversary q a R (stopAt R e) e
  have hgame : ∀ R e, Prod.snd <$> game R e = seedGame adversary q a R e := fun R e => pausedSeed_snd q a R _ e
  have hblind : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R)) trace,
      Stop (restTable (ov a (restDepth a R) R x)) trace ↔ stopAt R (evaluate x.1 x.2) trace := by
    intro R x trace
    show _ ↔ Stop (fillTable a R (evaluate x.1 x.2)) trace
    rw [← hmask, maskAt_ov_fill, hmask]
  -- the two R3 events through the mixture
  let genCAS : (R : RefTables adversary) → Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest →
      Option Digest)) → Prop := fun R r =>
    stopAt R r.1 r.2.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1 a ∧ Contact r.2.2 r.1
  let genStop : (R : RefTables adversary) → Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest →
      Option Digest)) → Prop := fun R r => stopAt R r.1 r.2.1.1
  have hCAS := reference_prob_eq_of q a ha game Prod.snd hgame (fun s => ContactAfterStop Stop s.answers s.trace a)
    genCAS (by
      intro R x res hres
      obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt R (evaluate x.1 x.2)) res hres
      have hc := coupled_contact q a R x (stopAt R (evaluate x.1 x.2)) res hres
      have hd : depth (restTable (ov a (restDepth a R) R x)) a = depth (fillTable a R (evaluate x.1 x.2)) a := by
        rw [fillTable_depth]; exact (restDepth_eq a _).symm.trans (restDepth_ov a R x)
      have hf : frontierValue (restTable (ov a (restDepth a R) R x)) a =
          frontierValue (fillTable a R (evaluate x.1 x.2)) a := by
        rw [fillTable_frontier, frontierValue_ov]
      show ContactAfterStop Stop (restTable (ov a (restDepth a R) R x))
        (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
        stopAt R (evaluate x.1 x.2) res.1.1 ∧ ¬ContactAt (fillTable a R (evaluate x.1 x.2)) res.1.1 a ∧
          Contact res.2 (evaluate x.1 x.2)
      unfold ContactAfterStop
      have e1 : ∀ trace, ContactAt (restTable (ov a (restDepth a R) R x)) trace a ↔
          ContactAt (fillTable a R (evaluate x.1 x.2)) trace a := fun trace => contactAt_congr trace a hd hf
      simp only [hblind R x, e1]
      rw [first_stop_iff (stopAt R (evaluate x.1 x.2)) (fun trace => ContactAt (fillTable a R (evaluate x.1 x.2)) trace a)
        h1 h2 h3 (fun j k hjk h => contactAt_take_mono _ _ a hjk h)]
      rw [← e1 (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2), hc])
  have hSTOP := reference_prob_eq_of q a ha game Prod.snd hgame (fun s => ∃ k, Stop s.answers (s.trace.take k))
    genStop (by
      intro R x res hres
      obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt R (evaluate x.1 x.2)) res hres
      show (∃ k, Stop (restTable (ov a (restDepth a R) R x))
        ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k)) ↔ _
      simp only [hblind R x]
      exact first_stop_exists_iff _ h1 h2 h3)
  -- the per-rest bound (G4 on the checkpoint run)
  have hR : ∀ R : RefTables adversary,
      (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[genStop R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)] := by
    intro R
    let aux : Digest → QueryImpl unifSpec PMF := fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl
    let before := fun e => seedBefore adversary q a R (stopAt R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun aux before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun aux (game R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project aux before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support aux before
      after (fun _ _ => none) r hr
    -- the contact event on the checkpoint run
    have hc : Pr[genCAS R | realRun aux (game R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun aux before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    -- the stop event
    have hs : Pr[fun r => marked r.1 r.2 | realRun aux before (fun _ _ => none)] ≤
        Pr[genStop R | realRun aux (game R) (fun _ _ => none)] := by
      rw [← SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_mark_probability aux before after
        (fun _ _ => none) marked, ← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_mono
      intro r _ hm
      exact hm.1
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_le_mark aux before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt R e) e middle hmiddle result hresult).2)
      (fun r hr _ => (checkpoint_budget q a R (stopAt R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2).1)
    rw [card_digest] at hkernel
    rw [hc]
    exact hkernel.trans (mul_le_mul' le_rfl hs)
  rw [hCAS, hSTOP, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  calc (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (restLaw adversary R * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]))
      = restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)])) := by ring
    _ ≤ restLaw adversary R * (((2 * q : ℕ) : ENNReal) * Pr[genStop R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]) :=
        mul_le_mul' le_rfl (hR R)
    _ = ((2 * q : ℕ) : ENNReal) * (restLaw adversary R * Pr[genStop R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]) := by ring

/-- `MarkerAt · τ a` reads the table only through `maskAt · a` (F1: reference word and input of `a`'s leaf). -/
theorem markerAt_maskAt (T : Answers) (trace : List Entry) (a : ChainAddr) :
    MarkerAt (maskAt T a) trace a ↔ MarkerAt T trace a := by
  unfold MarkerAt
  rw [referenceInput_maskAt, referenceDigits_maskAt]

theorem markerAt_take_exists (T : Answers) (trace : List Entry) (a : ChainAddr) :
    (∃ k, MarkerAt T (trace.take k) a) ↔ MarkerAt T trace a := by
  constructor
  · rintro ⟨k, message, counter, answer, digits, hm, h⟩
    exact ⟨message, counter, answer, digits, List.mem_of_mem_take hm, h⟩
  · intro h
    exact ⟨trace.length, by rw [List.take_length]; exact h⟩

/-- **Marker first, then a contact (stream E's MarkerFirst at `a`), chain side** (G4 flat):
`(1 − x) · (2^128 · Pr_R3[marker of a with no contact yet, then a contact of a]) ≤ 2q · Pr_R3[MarkerAt a]`. -/
theorem reference_markerFirst_at_le (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop (fun T trace => MarkerAt T trace a) s.answers s.trace a |
          referenceExperiment adversary q]) ≤
      ((2 * q : ℕ) : ENNReal) * Pr[fun s => MarkerAt s.answers s.trace a | referenceExperiment adversary q] := by
  have h := reference_contactAfterStop_le adversary q hq a ha (fun T trace => MarkerAt T trace a)
    (fun T trace => markerAt_maskAt T trace a)
  simpa only [markerAt_take_exists] using h

open PrefixGame in
/-- **Contact after the first stop (G4, charge form).** The restart is charged at twice `a`'s prefix count, on the
samples where the trace stops: `(1 − x) · (2^128 · Pr_R3[ContactAfterStop Stop · a]) ≤
E_R3[2 · prefixCount a · 1[some prefix stops]]`. -/
theorem reference_contactAfterStop_charge (adversary : AdversaryP) (q : Nat) (hq : q < 2 ^ 128) (a : ChainAddr)
    (ha : WotsExtract.SourceChain a) (Stop : Answers → List Entry → Prop)
    (hmask : ∀ T trace, Stop (maskAt T a) trace ↔ Stop T trace) :
    (1 - (q : ENNReal) / 2 ^ 128) *
        ((2 ^ 128 : ENNReal) * Pr[fun s => ContactAfterStop Stop s.answers s.trace a | referenceExperiment adversary q]) ≤
      ∑' s, referenceExperiment adversary q s * (((2 * prefixCount a s : ℕ) : ENNReal) *
        (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0)) := by
  let stopAt : (R : RefTables adversary) → Digest → List Entry → Prop := fun R e trace => Stop (fillTable a R e) trace
  let game : (R : RefTables adversary) → Digest → OracleComp (SeedSpec (restDepth a R)) (List Entry × SeedResult) :=
    fun R e => pausedSeed adversary q a R (stopAt R e) e
  have hgame : ∀ R e, Prod.snd <$> game R e = seedGame adversary q a R e := fun R e => pausedSeed_snd q a R _ e
  have hblind : ∀ (R : RefTables adversary) (x : Hidden (restDepth a R)) trace,
      Stop (restTable (ov a (restDepth a R) R x)) trace ↔ stopAt R (evaluate x.1 x.2) trace := by
    intro R x trace
    show _ ↔ Stop (fillTable a R (evaluate x.1 x.2)) trace
    rw [← hmask, maskAt_ov_fill, hmask]
  let genCAS : (R : RefTables adversary) → Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest →
      Option Digest)) → Prop := fun R r =>
    stopAt R r.1 r.2.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1 a ∧ Contact r.2.2 r.1
  let genCharge : (R : RefTables adversary) → Digest × ((List Entry × SeedResult) × (Fin (restDepth a R) → Digest →
      Option Digest)) → ENNReal := fun R r =>
    ((2 * seedCost a R r.2.1.2 : ℕ) : ENNReal) * (if stopAt R r.1 r.2.1.1 then 1 else 0)
  have hCAS := reference_prob_eq_of q a ha game Prod.snd hgame (fun s => ContactAfterStop Stop s.answers s.trace a)
    genCAS (by
      intro R x res hres
      obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt R (evaluate x.1 x.2)) res hres
      have hc := coupled_contact q a R x (stopAt R (evaluate x.1 x.2)) res hres
      have hd : depth (restTable (ov a (restDepth a R) R x)) a = depth (fillTable a R (evaluate x.1 x.2)) a := by
        rw [fillTable_depth]; exact (restDepth_eq a _).symm.trans (restDepth_ov a R x)
      have hf : frontierValue (restTable (ov a (restDepth a R) R x)) a =
          frontierValue (fillTable a R (evaluate x.1 x.2)) a := by
        rw [fillTable_frontier, frontierValue_ov]
      show ContactAfterStop Stop (restTable (ov a (restDepth a R) R x))
        (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2) a ↔
        stopAt R (evaluate x.1 x.2) res.1.1 ∧ ¬ContactAt (fillTable a R (evaluate x.1 x.2)) res.1.1 a ∧
          Contact res.2 (evaluate x.1 x.2)
      unfold ContactAfterStop
      have e1 : ∀ trace, ContactAt (restTable (ov a (restDepth a R) R x)) trace a ↔
          ContactAt (fillTable a R (evaluate x.1 x.2)) trace a := fun trace => contactAt_congr trace a hd hf
      simp only [hblind R x, e1]
      rw [first_stop_iff (stopAt R (evaluate x.1 x.2)) (fun trace => ContactAt (fillTable a R (evaluate x.1 x.2)) trace a)
        h1 h2 h3 (fun j k hjk h => contactAt_take_mono _ _ a hjk h)]
      rw [← e1 (traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2), hc])
  have hCHARGE := reference_expectation_eq_of q a ha game Prod.snd hgame
    (fun s => ((2 * prefixCount a s : ℕ) : ENNReal) * (if ∃ k, Stop s.answers (s.trace.take k) then 1 else 0))
    genCharge (by
      intro R x res hres
      obtain ⟨h1, h2, h3⟩ := coupled_paused q a ha R x (stopAt R (evaluate x.1 x.2)) res hres
      have hview := sampleView_coupled adversary q a R x (res.1.2, res.2)
        (coupled_paused_rows q a R x (stopAt R (evaluate x.1 x.2)) res hres)
      have hcount : prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) = seedCost a R res.1.2 :=
        congrArg PrefixView.count hview
      have hstop : (∃ k, Stop (restTable (ov a (restDepth a R) R x))
          ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k)) ↔ stopAt R (evaluate x.1 x.2) res.1.1 := by
        simp only [hblind R x]
        exact first_stop_exists_iff _ h1 h2 h3
      show ((2 * prefixCount a (mkSample (restTable (ov a (restDepth a R) R x)) res.1.2) : ℕ) : ENNReal) *
          (if ∃ k, Stop (restTable (ov a (restDepth a R) R x))
            ((traceOf (restTable (ov a (restDepth a R) R x)) res.1.2.2).take k) then 1 else 0) =
        ((2 * seedCost a R res.1.2 : ℕ) : ENNReal) * (if stopAt R (evaluate x.1 x.2) res.1.1 then 1 else 0)
      rw [hcount]
      by_cases hs : stopAt R (evaluate x.1 x.2) res.1.1
      · rw [if_pos (hstop.mpr hs), if_pos hs]
      · rw [if_neg (fun h => hs (hstop.mp h)), if_neg hs])
  have hR : ∀ R : RefTables adversary,
      (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]) ≤
      ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none) r *
        genCharge R r := by
    intro R
    let before := fun e => seedBefore adversary q a R (stopAt R e) e
    let after := fun (_ : Digest) (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => seedAfter a R middle.1
    let marked := fun e (middle : ((List Entry × OracleComp RefWorld SeedResult) × Nat) ×
      (Fin (restDepth a R) → Digest → Option Digest)) => stopAt R e middle.1.1.1 ∧ ¬Contact middle.2 e
    have hproj : (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).map
        (fun r => (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2)) =
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none) := by
      have h := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_project (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
        (fun _ middle => seedAfter a R middle) (fun _ _ => none) (fun _ middle result => (middle.1.1, result))
      rw [h]
      congr 1
      funext e
      exact seedBefore_after q a R (stopAt R e) e
    have hsupp := fun r hr => SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_support (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before
      after (fun _ _ => none) r hr
    have hc : Pr[genCAS R | realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)] =
        Pr[fun r => marked r.1 r.2.1 ∧ Contact r.2.2.2 r.1 | realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)] := by
      rw [← hproj, ← PMF.monad_map_eq_map, probEvent_map]
      apply pmf_probEvent_congr
      intro r hr
      have hinv := checkpoint_rows q a R (stopAt R r.1) r.1 r.2.1 (hsupp r hr).1
      show (stopAt R r.1 r.2.1.1.1.1 ∧ ¬ContactAt (fillTable a R r.1) r.2.1.1.1.1 a ∧ Contact r.2.2.2 r.1) ↔
        ((stopAt R r.1 r.2.1.1.1.1 ∧ ¬Contact r.2.1.2 r.1) ∧ Contact r.2.2.2 r.1)
      rw [contact_iff_rowsInv a R r.1 _ _ hinv]
      exact ⟨fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩, fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
    have hsmall : q < Fintype.card Digest := by simpa using hq
    have hkernel := SphincsSecurity.Concrete.PartialChainEndpoint.realCheckpointRun_contact_charge (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
      (fun _ _ => none) marked q (fun _ _ h => h.2)
      (fun e middle hmiddle _ result hresult =>
        (checkpoint_budget q a R (stopAt R e) e middle hmiddle result hresult).2)
    rw [card_digest] at hkernel
    rw [hc]
    refine hkernel.trans ?_
    have hexp : (∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R)
        (fun _ _ => none) r * genCharge R r) =
        ∑' r, realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after
          (fun _ _ => none) r * genCharge R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) := by
      rw [← hproj, SphincsSecurity.Concrete.PartialChainEndpoint.expectation_map]
    refine le_of_le_of_eq ?_ hexp.symm
    apply ENNReal.tsum_le_tsum
    intro r
    by_cases hr : r ∈ (realCheckpointRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) before after (fun _ _ => none)).support
    · apply mul_le_mul' le_rfl
      have hch := checkpoint_charge q a R (stopAt R r.1) r.1 r.2.1 (hsupp r hr).1 r.2.2 (hsupp r hr).2
      by_cases hm : marked r.1 r.2.1
      · rw [if_pos hm, mul_one]
        have hgc : genCharge R (r.1, (r.2.1.1.1.1, r.2.2.1.1), r.2.2.2) =
            ((2 * seedCost a R r.2.2.1.1 : ℕ) : ENNReal) := by
          simp only [genCharge]
          rw [if_pos hm.1, mul_one]
        rw [hgc]
        exact_mod_cast hch
      · rw [if_neg hm, mul_zero]
        exact bot_le
    · rw [(PMF.apply_eq_zero_iff _ r).mpr hr, zero_mul, zero_mul]
  rw [hCAS, hCHARGE, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro R
  calc (1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * (restLaw adversary R * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)]))
      = restLaw adversary R * ((1 - (q : ENNReal) / 2 ^ 128) * ((2 ^ 128 : ENNReal) * Pr[genCAS R |
        realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R) (fun _ _ => none)])) := by ring
    _ ≤ restLaw adversary R * ∑' r, realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (game R)
        (fun _ _ => none) r * genCharge R r := mul_le_mul' le_rfl (hR R)

end SigGolfCandidate.T3.Security.Wots
