import SigGolfCandidate.T3.Secc.LargeCouplingShort

/-!
# LR-34 (coupling, one table): the router's stops dominate the contacts

**`table_contact_le`**: for a coherent eager table `T` (universe `U = Wots.referenceInputs adversary`), the probability
that the fixed-world recorded padded game (F2's `Ref.fixedRecord T (idealGame …)`) contacts (`ContactR … T`) is at
most the probability that the router (after the presampled data `a`) stops within the budget in the eager observed
world of `(vals, nv, τ)`.

Route: F2's `fixed_game_eq` (key generation ; logged interaction ; verdict, all deterministic but the coins),
`taggedFixed_untag` (the interaction is a fixed-world tagged record), the canonical split of the combined record
(`ContactR` quantifies over splits), the key disclosures (`Coherent.pk`, `Coherent.published`, `rel_initial`), then
`interaction_le` with the verdict as continuation (`routeVerdict_observed`).
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
noncomputable local instance instDecidableEqCache_largeCouplingTable : DecidableEq T3.Cache := Classical.decEq _

section Table
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData} {q : Nat}

/-- The world state after the key disclosures. -/
noncomputable def keyState (U : Finset HashInput) (q : Nat) (vals : Coord → Digest) (nv : Message → Digest) :
    LargeResidual.State WCoord (Cell U) :=
  discloseStates U q (Sum.elim vals nv) LargeResidual.initial keygenDisclosed

/-- **The initial relation** after the key disclosures. -/
theorem rel_initial :
    Rel U T vals nv τ a q Monitor.initial RouterState.initial (keyState U q vals nv) := by
  have hc := discloseStates_counters (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  have hr := discloseStates_rows (U := U) (q := q) (vals := vals) (nv := nv) keygenDisclosed
    (LargeResidual.initial : LargeResidual.State WCoord (Cell U))
  unfold keyState
  refine ⟨rfl, rfl, rfl, by rw [hc]; rfl, by rw [hc]; rfl, rfl, by rw [hc]; exact le_rfl, Nat.zero_le _, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro c
    rw [discloseStates_candidates]
    split_ifs
    · exact Finset.mem_singleton_self _
    · exact Finset.mem_univ _
  · intro c hck
    rw [discloseStates_candidates, if_neg, hc]
    · simp only [LargeResidual.initial, Finset.card_univ, Nat.sub_zero]
      simp [SphincsSecurity.digestBits]
    · intro hm
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      rw [Sum.inl.inj hdc] at hd
      exact hck (Known.base (Or.inl hd))
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro row v hv
    rw [hr] at hv
    cases hv
  · intro X hX
    cases hX
  · intro X hX
    cases hX

theorem keygen_record (T : Answers) :
    Wots.Ref.pureRecord T keygen (∅, ∅) ∈ support (FirstHit.record keygen (∅, ∅)) ∧
      Wots.Ref.Agrees T (Wots.Ref.pureRecord T keygen (∅, ∅)).state := by
  apply Wots.Ref.fixedRecord_mem_record T keygen (∅, ∅) (Wots.Ref.agrees_empty T)
  rw [Wots.Ref.fixedRecord_hashOnly T keygen SourceReplay.keygen_hashOnly, mem_support_pure_iff]

/-- The canonical split of the combined fixed-world record of a fixed-world tagged interaction. -/
theorem canonical_split (adversary : AdversaryP) (T : Answers)
    (t : Tagged (Option ForgeryP))
    (ht : t ∈ support (taggedFixed T (evalWithAnswerFn T keygen).2
      (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
      (Wots.Ref.pureRecord T keygen (∅, ∅)).state)) :
    TaggedSplit adversary (Wots.Ref.combine T t.untag) (Wots.Ref.pureRecord T keygen (∅, ∅)) t
      (Wots.Ref.verdictRecord T t.untag) := by
  obtain ⟨hk, hka⟩ := keygen_record T
  have hval : (Wots.Ref.pureRecord T keygen (∅, ∅)).value = evalWithAnswerFn T keygen :=
    Wots.Ref.pureRecord_value T keygen (∅, ∅)
  obtain ⟨ht1, ht2⟩ := taggedFixed_support T _ _ _ hka t ht
  refine ⟨hk, by rw [hval]; exact ht1, ?_, rfl⟩
  have hv := Wots.Ref.fixedRecord_mem_record T
    (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 t.value) t.state ht2
    (Wots.Ref.verdictRecord T t.untag)
    (by rw [Wots.Ref.fixedRecord_hashOnly T _ (Wots.Ref.verdict_hashOnly _ _), mem_support_pure_iff]; rfl)
  rw [hval]
  exact hv.1

/-- The contact event of a deterministic verdict continuation (`Final` of `interaction_le`). -/
noncomputable def verdictContact (U : Finset HashInput) (T : Answers) (q : Nat) (pk : Digest) (mon : Monitor)
    (value : Option ForgeryP × QueryLog Requests) (state : LazyPrivate.State) : Prop :=
  ((Wots.Ref.pureRecord T (GameWith.verdict PaddedGame.checker pk value) state).events.foldl
    (Monitor.event U T q) mon).contact = true

/-- The router's continuation after the interaction. -/
noncomputable def verdictCont (U : Finset HashInput) (a : AuxData) (q : Nat) (pk : Digest)
    (r : Option ((Option ForgeryP × QueryLog Requests) × RouterState)) :
    OracleComp (RWorld U) (Option (Bool × RouterState)) :=
  match r with
  | none => pure none
  | some (result, st) => routeVerdict U a q (GameWith.verdict PaddedGame.checker pk result) st

/-- The router after the presampled data, with the honest key. -/
theorem Coherent.routerWith (hcoh : Coherent U T vals nv τ a) (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input))
    (adversary : AdversaryP) :
    observedRun aux q (Sum.elim vals nv) τ (routerWith U adversary q a) LargeResidual.initial =
      observedRun aux q (Sum.elim vals nv) τ
        (routeInteraction U a (evalWithAnswerFn T keygen).2 q
          (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2) RouterState.initial >>=
            verdictCont U a q (evalWithAnswerFn T keygen).1) (keyState U q vals nv) := by
  unfold LargeResidual.routerWith
  rw [observed_discloseAll]
  have hkv : lookupVal (List.map (fun c => (c, Sum.elim vals nv (Sum.inl c))) keygenDisclosed) = keyValues vals :=
    rfl
  simp only [hkv]
  rw [hcoh.published, hcoh.pk]
  rfl


end Table

/-- **One table: contacts are router stops.** -/
theorem table_contact_le (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127) (initLaw : PMF AuxData)
    {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
    {τ : Cell (Wots.referenceInputs adversary) → HashOutput} {a : AuxData}
    (hcoh : Coherent (Wots.referenceInputs adversary) T vals nv τ a) :
    Pr[fun rec => ContactR adversary q rec T |
        Wots.Ref.fixedRecord T (GameWith.idealGame PaddedGame.checker adversary) (∅, ∅)] ≤
      Pr[fun r => r.1 = none ∧ r.2.counters.calls ≤ q |
        observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ (routerWith (Wots.referenceInputs adversary) adversary q a)
          LargeResidual.initial] := by
  have hUpub : SeccLaw.publicUniverse ⊆ Wots.referenceInputs adversary := Wots.Ref.referenceInputs_universe adversary
  obtain ⟨-, hpub, -⟩ := Correctness.keygen_correct T
  rw [hcoh.routerWith, Wots.Ref.fixed_game_eq, probEvent_map]
  unfold Wots.Ref.fixedInteraction
  rw [← taggedFixed_untag, probEvent_map]
  refine (probEvent_mono ?_).trans (interaction_le initLaw hcoh hq hUpub (evalWithAnswerFn T keygen).2 hpub
    (adversary (evalWithAnswerFn T keygen).1 (evalWithAnswerFn T keygen).2)
    (fun mon _ value state => verdictContact (Wots.referenceInputs adversary) T q (evalWithAnswerFn T keygen).1 mon value state)
    (verdictCont (Wots.referenceInputs adversary) a q (evalWithAnswerFn T keygen).1) (fun r => r.1 = none ∧ r.2.counters.calls ≤ q)
    ?_ ?_ ?_ Monitor.initial RouterState.initial (keyState (Wots.referenceInputs adversary) q vals nv) _ rel_initial (fun _ _ h => by cases h))
  · intro t ht hc
    have hsplit := canonical_split adversary T t ht
    have h := hc _ _ _ hsplit
    rw [Wots.Ref.pureRecord_value] at h
    exact h
  · intro mon st ws state v log hrel _ hf
    obtain ⟨out, ws', hrun, hph⟩ := routeVerdict_observed (auxLaw initLaw) hcoh hq
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log))
      (PaddedGame.verdict_public _ _) mon st ws state hrel
    change 1 ≤ Pr[_ | observedRun (auxLaw initLaw) q (Sum.elim vals nv) τ
      (routeVerdict (Wots.referenceInputs adversary) a q (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 (v, log)) st) ws]
    rw [hrun, probEvent_pure]
    unfold verdictContact at hf
    rcases hph with ⟨h1, -, h3⟩ | ⟨-, h2, -⟩ | ⟨-, h2⟩
    · rw [if_pos ⟨h1, h3⟩]
    · rw [hf] at h2; cases h2
    · have h4 := h2.contact
      rw [hf] at h4
      cases h4
  · intro m s v σ hf
    by_contra hcon
    simp only [not_or, not_le] at hcon
    have hc : m.contact = false := by simpa using hcon.1
    have h := events_over (Wots.referenceInputs adversary) T q m hc (by omega) (Wots.Ref.pureRecord T
      (GameWith.verdict PaddedGame.checker (evalWithAnswerFn T keygen).1 v) σ).events
    unfold verdictContact at hf
    rw [h.1] at hf
    cases hf
  · intro ws' hws
    exact ⟨rfl, hws⟩


end SigGolfCandidate.T3.Security.LargeCoupling
