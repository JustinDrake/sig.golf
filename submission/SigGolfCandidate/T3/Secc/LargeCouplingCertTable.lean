import SigGolfCandidate.T3.Secc.LargeCouplingCertInteraction
import SigGolfCandidate.T3.Secc.LargeCouplingTable
import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs

/-!
# LR-34 (certificate coupling, one table): real certificates are router certificates

**`table_cert_le`**: for a coherent eager table `T`, the probability that the fixed-world recorded padded game
satisfies the real certificate event (`CertR … T`) is at most the probability that the router (after the
presampled data `a`) finishes with an accepting verdict and a certificate (`CertOut`) in the eager observed world.

Route: as `table_contact_le` (`fixed_game_eq`, `taggedFixed_untag`, `canonical_split`, `rel_initial`), with
`interaction_le'` (a certificate run never contacts, so router stops do not count) and the verdict as continuation
(`routeVerdict_observed`: a finished verdict returns the honest verdict and the router fold of its events).
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen
noncomputable local instance instDecidableEqCache_largeCouplingCertTable : DecidableEq T3.Cache := Classical.decEq _

/-- The certificate event of a deterministic verdict continuation (`Final` of `interaction_le'`). -/
noncomputable def verdictCert (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (st : RouterState) (value : Option ForgeryP × QueryLog Requests) (state : LazyPrivate.State) : Prop :=
  evalWithAnswerFn T (GameWith.verdict PaddedGame.checker pk value) = true ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = false ∧
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).calls ≤ q ∧
  CertGhost ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (routerEvent U) st)

theorem honestNonce_coherent {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell U → HashOutput} {a : AuxData} (hcoh : Coherent U T vals nv τ a) : nv = honestNonce T := by
  funext m
  exact (hcoh.privateNonce m).symm

/-- **One table: real certificates are router certificates.** -/
theorem table_cert_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : Coherent (Wots.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => CertR adversary q rec T |
        Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[CertOut |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary := Wots.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  have hnv := honestNonce_coherent hcoh
  rw [hcoh.routerWith, Wots.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le' initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hpub
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon st value state => verdictCert (Wots.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon st
      value state)
    (verdictCont (Wots.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) CertOut
    ?_ ?_ ?_ Monitor.initial RouterState.initial (keyState (Wots.referenceInputs adversary) q vals nv) _ rel_initial
    (fun _ _ h => by simp [RouterState.initial] at h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    obtain ⟨h1, h2, h3, h4⟩ := hc _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h2 h3 h4
    have hv : (Wots.Ref.verdictRecord T t.untag).value =
        evalWithAnswerFn T (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) :=
      Wots.Ref.pureRecord_value _ _ _
    refine ⟨hv ▸ h1, h2, h3, ?_⟩
    unfold routerFold at h4
    rw [hnv]
    exact h4
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PaddedGame.verdict_public _ _) mon st ws state hrel
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.referenceInputs adversary) a q
        (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    obtain ⟨hval, hnc, hcalls, hcert⟩ := hf
    rcases hph with ⟨-, h2, -⟩ | ⟨-, h2, h3⟩ | ⟨h1, -⟩
    · rw [hnc] at h2; cases h2
    · omega
    · rw [if_pos ⟨_, by rw [h1, hval], hcert⟩]
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    have := hf.2.2.1
    omega
  · intro ws' _
    right
    intro m s v σ hf
    by_contra hcon
    have hc : m.contact = true := by simpa using hcon
    have h := hf.2.1
    rw [events_frozen (Wots.referenceInputs adversary) T q m hc] at h
    rw [hc] at h
    cases h

end SigGolfCandidate.T3.Security.LargeCoupling
