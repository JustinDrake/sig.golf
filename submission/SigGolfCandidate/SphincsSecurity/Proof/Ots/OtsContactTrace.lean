import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainEndpoint
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCap
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedRun
import SigGolfCandidate.SphincsSecurity.Proof.Reference.CausalFrontierProgram
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPause
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixAllocation

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {State AuxIndex ExtraIndex : Type} {auxSpec : OracleSpec AuxIndex} {extraSpec : OracleSpec ExtraIndex} {n : Nat} {Result : Type}
noncomputable def extendAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id) : QueryImpl (auxSpec + extraSpec) PMF
  | .inl input => auxiliary input
  | .inr input => PMF.pure (extra input)
noncomputable def eraseAux (extra : QueryImpl extraSpec Id) :
    QueryImpl ((auxSpec + extraSpec) + PrefixSpec n State) (OracleComp (auxSpec + PrefixSpec n State))
  | .inl (.inl input) => liftM ((auxSpec + PrefixSpec n State).query (.inl input))
  | .inl (.inr input) => pure (extra input)
  | .inr query => liftM ((auxSpec + PrefixSpec n State).query (.inr query))
variable [Fintype State] [DecidableEq State] [Nonempty State]
omit [Fintype State] [Nonempty State] in
theorem observedRun_eraseAux (auxiliary : QueryImpl auxSpec PMF) (extra : QueryImpl extraSpec Id)
    (tables : Fin n → State → State) (computation : OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    observedRun auxiliary tables (simulateQ (eraseAux extra) computation) observed = observedRun (extendAux auxiliary extra) tables computation observed := by
  have himpl : (observedImpl auxiliary tables).compose (eraseAux extra) = observedImpl (extendAux auxiliary extra) tables := by
    funext input
    cases input with
    | inl input =>
        cases input with
        | inl input => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
        | inr input =>
            simp only [QueryImpl.apply_compose, eraseAux, simulateQ_pure, observedImpl, extendAux]
            ext observed
            simp only [StateT.run_pure, StateT.run_mk, PMF.map, PMF.pure_bind, Function.comp_def, PMF.monad_pure_eq_pure]
    | inr query => simp only [QueryImpl.apply_compose, eraseAux, simulateQ_spec_query]; rfl
  simp only [observedRun, ← QueryImpl.simulateQ_compose, himpl]
theorem realRun_eraseAux (auxiliary : State → QueryImpl auxSpec PMF) (extra : State → QueryImpl extraSpec Id)
    (computation : State → OracleComp ((auxSpec + extraSpec) + PrefixSpec n State) Result)
    (observed : Fin n → State → Option State) :
    realRun auxiliary (fun endpoint => simulateQ (eraseAux (extra endpoint)) (computation endpoint)) observed =
      realRun (fun endpoint => extendAux (auxiliary endpoint) (extra endpoint)) computation observed := by
  simp only [realRun, observedRun_eraseAux]
end SphincsSecurity.Concrete.PartialChainEndpoint
end

section



namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition
abbrev VisibleWorld (segment : OtsPrefix) := OracleWorld + PartialChainEndpoint.PrefixSpec segment.digit.val Digest
noncomputable def visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl HashSpec (OracleComp segment.VisibleWorld) := fun bytes =>
  match segment.parse bytes with
  | none => liftM (segment.VisibleWorld.query (.inl (.inr bytes)))
  | some query => (combine · (high query)) <$> liftM (segment.VisibleWorld.query (.inr query))
noncomputable def visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) :
    QueryImpl OracleWorld (OracleComp segment.VisibleWorld)
  | .inl input => liftM (segment.VisibleWorld.query (.inl (.inl input)))
  | .inr bytes => segment.visibleHashImpl high bytes
theorem erase_visibleHashImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) (bytes : HashInput) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleHashImpl high bytes) = segment.hashImpl high outside bytes := by
  cases hparse : segment.parse bytes <;>
    simp only [visibleHashImpl, hashImpl, hparse, simulateQ_spec_query, simulateQ_map, PartialChainEndpoint.eraseAux]
theorem erase_visibleWorldImpl (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id) :
    (PartialChainEndpoint.eraseAux outside).compose (segment.visibleWorldImpl high) = segment.worldImpl high outside := by
  funext input
  cases input with
  | inl input => simp only [QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query, PartialChainEndpoint.eraseAux, worldImpl]
  | inr bytes => exact segment.erase_visibleHashImpl high outside bytes
noncomputable def visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  simulateQ (segment.visibleWorldImpl high) (CausalFrontierProgram.game segment.parameter outside ftsSecret words frontier adversary)
theorem erase_visibleGame (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    simulateQ (PartialChainEndpoint.eraseAux outside) (segment.visibleGame high outside ftsSecret words frontier adversary) =
      segment.game high outside ftsSecret words frontier adversary := by
  rw [visibleGame, ← QueryImpl.simulateQ_compose, erase_visibleWorldImpl, CausalFrontierProgram.prefix_game]
variable (segment : OtsPrefix) (inputs : Finset HashInput)
  (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
  (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary)
noncomputable def visibleSeedGame (endpoint : Digest) : OracleComp segment.VisibleWorld (Bool × SigningBoundaryTrace) :=
  segment.visibleGame auxiliary.high (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint)
    ftsSecret words (segment.seedFrontier inputs hencoding hgraph auxiliary secrets words endpoint) adversary
theorem erase_visibleSeedGame (endpoint : Digest) :
    simulateQ (PartialChainEndpoint.eraseAux (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint) =
        segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary := by
  rw [visibleSeedGame, erase_visibleGame]
  rfl
theorem visibleSeedGame_real :
    PartialChainEndpoint.realRun (fun endpoint => PartialChainEndpoint.extendAux uniformImpl
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint))
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none) =
    PartialChainEndpoint.realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary) (fun _ _ => none) := by
  simpa only [erase_visibleSeedGame] using
    (PartialChainEndpoint.realRun_eraseAux (fun _ => uniformImpl)
      (segment.seedOracle inputs hencoding hgraph auxiliary secrets ftsSecret words)
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary) (fun _ _ => none)).symm
end SphincsSecurity.Concrete.OtsPrefix
end

section


namespace SphincsSecurity.QueryPause
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
variable {Source Target Memory Result : Type} {source : OracleSpec Source} {target : OracleSpec Target}
theorem run_translation (stop : Memory → Prop) [DecidablePred stop]
    (sourceStep : (input : source.Domain) → source.Range input → Memory → Memory)
    (targetStep : (input : target.Domain) → target.Range input → Memory → Memory)
    (queryMap : source.Domain → target.Domain)
    (answerMap : (input : source.Domain) → target.Range (queryMap input) → source.Range input)
    (impl : QueryImpl source (OracleComp target))
    (himpl : ∀ input, impl input = answerMap input <$> liftM (target.query (queryMap input)))
    (hstep : ∀ input answer memory, targetStep (queryMap input) answer memory = sourceStep input (answerMap input answer) memory)
    (computation : OracleComp source Result) (memory : Memory) :
    run stop targetStep (simulateQ impl computation) memory =
      (fun paused => (paused.1, simulateQ impl paused.2)) <$> simulateQ impl (run stop sourceStep computation memory) := by
  induction computation using OracleComp.inductionOn generalizing memory with
  | pure result => simp only [simulateQ_pure, run_pure, map_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, run_query_bind]
      by_cases hs : stop memory
      · simp only [if_pos hs, simulateQ_pure, map_pure, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left]
      · simp only [if_neg hs, simulateQ_bind, simulateQ_spec_query, himpl, bind_map_left, map_bind, hstep, ih]
end SphincsSecurity.QueryPause
namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def hashObservationTrace : (input : OracleWorld.Domain) → OracleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl _, _ => 1
  | .inr input, answer => FreeMonoid.of (input, answer)
namespace OtsPrefix
noncomputable def visibleObservationTrace (segment : OtsPrefix) (high : segment.Query → High) :
    (input : segment.VisibleWorld.Domain) → segment.VisibleWorld.Range input → FreeMonoid (HashInput × HashOutput)
  | .inl input, answer => hashObservationTrace input answer
  | .inr query, answer => FreeMonoid.of (segment.input query, combine answer (high query))
private theorem withTrace_run {Input Target Trace : Type} {spec : OracleSpec Input} {target : OracleSpec Target} [Monoid Trace]
    (impl : QueryImpl spec (OracleComp target)) (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    (impl.withTrace trace input).run = (fun answer => (answer, trace input answer)) <$> impl input := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]
theorem visible_observation_step (segment : OtsPrefix) (high : segment.Query → High) (input : OracleWorld.Domain) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (segment.visibleWorldImpl high input)).run =
        ((segment.visibleWorldImpl high).withTrace hashObservationTrace input).run := by
  cases input with
  | inl input =>
      simp only [visibleWorldImpl, simulateQ_spec_query, withTrace_run, visibleObservationTrace, hashObservationTrace]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleWorldImpl, visibleHashImpl, hparse, simulateQ_spec_query, withTrace_run,
            visibleObservationTrace, hashObservationTrace]
          rfl
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleWorldImpl, visibleHashImpl, parse_input, simulateQ_map, simulateQ_spec_query, WriterT.run_map,
            withTrace_run, visibleObservationTrace, hashObservationTrace, Functor.map_map]
          rfl
theorem visible_observation_program (segment : OtsPrefix) (high : segment.Query → High)
    {Result : Type} (computation : OracleComp OracleWorld Result) :
    (simulateQ ((QueryImpl.id' segment.VisibleWorld).withTrace (segment.visibleObservationTrace high))
      (simulateQ (segment.visibleWorldImpl high) computation)).run =
    simulateQ (segment.visibleWorldImpl high)
      ((simulateQ ((QueryImpl.id' OracleWorld).withTrace hashObservationTrace) computation).run) := by
  rw [← QueryImpl.simulateQ_compose]
  symm
  apply simulateQ_writer_compose
  intro input
  rw [QueryImpl.apply_compose, visible_observation_step, withTrace_run, withTrace_run, simulateQ_map]
  change (fun answer => (answer, hashObservationTrace input answer)) <$>
    simulateQ (segment.visibleWorldImpl high) (liftM (OracleWorld.query input)) = _
  rw [simulateQ_spec_query]
theorem visible_pause_program (segment : OtsPrefix) (high : segment.Query → High)
    (stop : FreeMonoid (HashInput × HashOutput) → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : FreeMonoid (HashInput × HashOutput)) :
    QueryPause.run stop (fun input answer history => history * segment.visibleObservationTrace high input answer)
      (simulateQ (segment.visibleWorldImpl high) computation) trace =
    (fun paused => (paused.1, simulateQ (segment.visibleWorldImpl high) paused.2)) <$>
      simulateQ (segment.visibleWorldImpl high)
        (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace) := by
  classical
  have htranslation (input : OracleWorld.Domain) : ∃ (query : segment.VisibleWorld.Domain)
      (decode : segment.VisibleWorld.Range query → OracleWorld.Range input),
      segment.visibleWorldImpl high input = decode <$> liftM (segment.VisibleWorld.query query) ∧
        ∀ answer (history : FreeMonoid (HashInput × HashOutput)),
          history * segment.visibleObservationTrace high query answer = history * hashObservationTrace input (decode answer) := by
    cases input with
    | inl input =>
        refine ⟨.inl (.inl input), id, ?_, ?_⟩
        · simp only [visibleWorldImpl, id_map]
        · intro answer history; rfl
    | inr bytes =>
        cases hparse : segment.parse bytes with
        | none =>
            refine ⟨.inl (.inr bytes), id, ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse, id_map]
            · intro answer history; rfl
        | some query =>
            refine ⟨.inr query, fun answer => combine answer (high query), ?_, ?_⟩
            · simp only [visibleWorldImpl, visibleHashImpl, hparse]
              rfl
            · intro answer history
              simp only [visibleObservationTrace, hashObservationTrace, (segment.parse_some_iff bytes query).mp hparse]
  exact QueryPause.run_translation stop _ _ (fun input => (htranslation input).choose)
    (fun input => (htranslation input).choose_spec.choose) (segment.visibleWorldImpl high)
    (fun input => (htranslation input).choose_spec.choose_spec.1)
    (fun input => (htranslation input).choose_spec.choose_spec.2) computation trace
end OtsPrefix
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev Trace := FreeMonoid (HashInput × HashOutput)
def EntryContact (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) : Prop :=
  ∃ query : segment.Query, segment.parse entry.1 = some query ∧ query.1.val + 1 = segment.digit.val ∧ truncateHash entry.2 = endpoint
def Seen (segment : OtsPrefix) (endpoint : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, EntryContact segment endpoint entry
theorem entryContact_selects (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput)
    (h : EntryContact segment endpoint entry) : segment.Selects (.inr entry.1) := by
  obtain ⟨query, hquery, _⟩ := h
  change segment.parse entry.1 ≠ none
  rw [hquery]
  exact Option.some_ne_none query
theorem entryContact_unique (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) (left right : OtsPrefix.ChainAddress)
    (hleft : EntryContact (OtsPrefix.atAddress parameter words left) (frontier left.1 left.2.1 left.2.2.1 left.2.2.2) entry)
    (hright : EntryContact (OtsPrefix.atAddress parameter words right) (frontier right.1 right.2.1 right.2.2.1 right.2.2.2) entry) : left = right :=
  OtsPrefix.atAddress_selects_unique parameter words left right (.inr entry.1)
    (entryContact_selects _ _ entry hleft) (entryContact_selects _ _ entry hright)
theorem seen_one (segment : OtsPrefix) (endpoint : Digest) : ¬Seen segment endpoint 1 := by
  simp [Seen]
theorem seen_of (segment : OtsPrefix) (endpoint : Digest) (entry : HashInput × HashOutput) :
    Seen segment endpoint (FreeMonoid.of entry) ↔ EntryContact segment endpoint entry := by
  simp [Seen]
theorem seen_mul (segment : OtsPrefix) (endpoint : Digest) (first second : Trace) :
    Seen segment endpoint (first * second) ↔ Seen segment endpoint first ∨ Seen segment endpoint second := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]
noncomputable def contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (trace : Trace) :
    Finset OtsPrefix.ChainAddress :=
  Finset.univ.filter fun address => Seen (OtsPrefix.atAddress parameter words address)
    (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace
theorem mem_contacts (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ contacts parameter words frontier trace ↔ Seen (OtsPrefix.atAddress parameter words address)
      (frontier address.1 address.2.1 address.2.2.1 address.2.2.2) trace := by simp only [contacts, Finset.mem_filter, Finset.mem_univ, true_and]
theorem contacts_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    contacts parameter words frontier 1 = ∅ := by
  ext address
  simp only [mem_contacts, seen_one, Finset.notMem_empty]
theorem contacts_mul (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues) (first second : Trace) :
    contacts parameter words frontier (first * second) = contacts parameter words frontier first ∪ contacts parameter words frontier second := by
  ext address
  simp only [mem_contacts, seen_mul, Finset.mem_union]
attribute [local irreducible] contacts
theorem contacts_of_card_le_one (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (entry : HashInput × HashOutput) : (contacts parameter words frontier (FreeMonoid.of entry)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro left hleft right hright
  rw [mem_contacts, seen_of] at hleft hright
  exact entryContact_unique parameter words frontier entry left right hleft hright
theorem contacts_step_card_le (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (trace : Trace) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) :
    (contacts parameter words frontier (trace * hashObservationTrace input answer)).card ≤
      (contacts parameter words frontier trace).card + 1 := by
  cases input with
  | inl input => simp only [hashObservationTrace, mul_one]; omega
  | inr input =>
      rw [hashObservationTrace, contacts_mul]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left (contacts_of_card_le_one parameter words frontier (input, answer)) _)
theorem new_contact_of_two (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (before after : Trace) (hbefore : (contacts parameter words frontier before).card ≤ 1)
    (hafter : 2 ≤ (contacts parameter words frontier (before * after)).card) :
    ∃ address, address ∉ contacts parameter words frontier before ∧ address ∈ contacts parameter words frontier after := by
  by_contra h
  push Not at h
  have hsub : contacts parameter words frontier after ⊆ contacts parameter words frontier before := by
    intro address ha
    by_contra hb
    exact h address hb ha
  rw [contacts_mul, Finset.union_eq_left.mpr hsub] at hafter
  omega
end SphincsSecurity.Concrete.OtsContactTrace
end
