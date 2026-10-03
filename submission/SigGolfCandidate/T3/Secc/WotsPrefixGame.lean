import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsContactTrace
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPauseInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryPauseTrace
import SigGolfCandidate.SphincsSecurity.Proof.Chains.PartialChainLastRow
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTraceInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapTwoEdge
import SigGolfCandidate.T3.Secc.WotsPrefixGameSim
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapObservation
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapCost

section


namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts
variable (parameter : PublicParameter) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
def Stopped (trace : Trace) : Prop := (contacts parameter words frontier trace).Nonempty
noncomputable def pause {Result : Type} (computation : OracleComp OracleWorld Result) :=
  QueryPause.run (Stopped parameter words frontier)
    (fun input answer history => history * hashObservationTrace input answer) computation 1
theorem pause_card_le_one {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation)) :
    (contacts parameter words frontier result.1).card ≤ 1 := by
  apply QueryPause.run_invariant (Stopped parameter words frontier) _
    (fun trace => (contacts parameter words frontier trace).card ≤ 1) _ computation 1 _ result hresult
  · intro trace _ hstop input answer
    have hempty : contacts parameter words frontier trace = ∅ := Finset.not_nonempty_iff_eq_empty.mp hstop
    have h := contacts_step_card_le parameter words frontier trace input answer
    simpa only [hempty, Finset.card_empty, Nat.zero_add] using h
  · simp only [contacts_one, Finset.card_empty, Nat.zero_le]
theorem pause_stopped_or_finished {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation)) :
    Stopped parameter words frontier result.1 ∨ ∃ value, result.2 = pure value :=
  QueryPause.run_stopped_or_finished (Stopped parameter words frontier) _ computation 1 result hresult
theorem pause_new_contact {Result : Type} (computation : OracleComp OracleWorld Result)
    (result : Trace × OracleComp OracleWorld Result) (hresult : result ∈ support (pause parameter words frontier computation))
    (after : Trace) (htwo : 2 ≤ (contacts parameter words frontier (result.1 * after)).card) :
    ∃ address, address ∉ contacts parameter words frontier result.1 ∧ address ∈ contacts parameter words frontier after :=
  new_contact_of_two parameter words frontier result.1 after
    (pause_card_le_one parameter words frontier computation result hresult) htwo
end SphincsSecurity.Concrete.OtsContactTrace
end

section


namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] contacts
noncomputable def prefixCalls (segment : OtsPrefix) (trace : Trace) : Nat :=
  QueryCap.calls segment.Selects (trace.toList.map fun entry => (.inr entry.1 : OracleWorld.Domain))
theorem prefixCalls_one (segment : OtsPrefix) : prefixCalls segment 1 = 0 := rfl
theorem prefixCalls_mul (segment : OtsPrefix) (first second : Trace) :
    prefixCalls segment (first * second) = prefixCalls segment first + prefixCalls segment second := by
  simp only [prefixCalls, FreeMonoid.toList_mul, List.map_append, QueryCap.calls, List.countP_append]
theorem prefixCalls_step (segment : OtsPrefix) (input : OracleWorld.Domain) (answer : OracleWorld.Range input) (trace : Trace) :
    prefixCalls segment (hashObservationTrace input answer * trace) = (if segment.Selects input then 1 else 0) + prefixCalls segment trace := by
  cases input with
  | inl input => simp only [hashObservationTrace, one_mul, OtsPrefix.Selects, if_false, Nat.zero_add]
  | inr bytes =>
      simp only [prefixCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.singleton_append,
        List.map_cons, QueryCap.calls_cons]
theorem traced_hash_counted {Result : Type} (computation : OracleComp OracleWorld Result) :
    (fun result => (result.1, result.2.toList.length)) <$> QueryPause.traced hashObservationTrace computation =
      QueryCap.counted CausalFrontierProgram.IsHash computation := by
  apply QueryPause.traced_counted hashObservationTrace CausalFrontierProgram.IsHash (fun trace => trace.toList.length) rfl
  intro input answer trace
  cases input <;> simp only [hashObservationTrace, one_mul, CausalFrontierProgram.IsHash, reduceCtorEq, ↓reduceIte,
    Nat.zero_add, FreeMonoid.toList_mul, FreeMonoid.toList_of, List.length_append, List.length_singleton]
private theorem hash_calls_map (entries : List (HashInput × HashOutput)) :
    QueryCap.calls CausalFrontierProgram.IsHash (entries.map fun entry => (.inr entry.1 : OracleWorld.Domain)) = entries.length := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, QueryCap.calls_cons, CausalFrontierProgram.IsHash, ↓reduceIte, ih, List.length_cons, Nat.add_comm]
theorem prefixCalls_allocation (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (trace : Trace) :
    (∑ address ∈ addresses, prefixCalls (OtsPrefix.atAddress parameter words address) trace) ≤ trace.toList.length := by
  simpa only [prefixCalls, hash_calls_map] using
    OtsPrefix.allocation_le parameter words addresses (trace.toList.map fun entry => (.inr entry.1 : OracleWorld.Domain))
theorem restartCharge_allocation (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (before after : Trace) :
    (∑ address ∈ addresses, (prefixCalls (OtsPrefix.atAddress parameter words address) before +
      2 * prefixCalls (OtsPrefix.atAddress parameter words address) after)) ≤ before.toList.length + 2 * after.toList.length := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact Nat.add_le_add (prefixCalls_allocation parameter words addresses before)
    (Nat.mul_le_mul_left 2 (prefixCalls_allocation parameter words addresses after))
theorem restartCharge_le_budget (parameter : PublicParameter) (words : OtsReferenceWords)
    (addresses : Finset OtsPrefix.ChainAddress) (before after : Trace) (budget : Nat)
    (hbudget : (before * after).toList.length ≤ budget) :
    (∑ address ∈ addresses, (prefixCalls (OtsPrefix.atAddress parameter words address) before +
      2 * prefixCalls (OtsPrefix.atAddress parameter words address) after)) ≤ 2 * budget := by
  apply (restartCharge_allocation parameter words addresses before after).trans
  simp only [FreeMonoid.toList_mul, List.length_append] at hbudget
  omega
theorem traced_game_cost (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Trace)
    (hresult : result ∈ support (QueryPause.traced hashObservationTrace
      (CausalFrontierProgram.game parameter external ftsSecret words frontier adversary))) : result.2.toList.length ≤ result.1.2.hashCalls := by
  apply CausalFrontierProgram.game_counted_le parameter external ftsSecret words frontier adversary
    (result.1, result.2.toList.length)
  rw [← traced_hash_counted, support_map]
  exact ⟨result, hresult, rfl⟩
end SphincsSecurity.Concrete.OtsContactTrace
end

section


namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem contact_record_consistent {State : Type} [DecidableEq State] {n : Nat}
    (observed : Fin n → State → Option State) (query : Fin n × State) (answer endpoint : State)
    (hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    Contact (record observed query answer) endpoint ↔ Contact observed endpoint ∨ query.1.val + 1 = n ∧ answer = endpoint := by
  by_cases hc : Contact observed endpoint
  · exact iff_of_true (contact_mono (record_extends observed query answer hconsistent) endpoint hc) (Or.inl hc)
  · simpa only [hc, false_or] using contact_record_iff observed query answer endpoint hc
noncomputable def visibleLazyImpl (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF) :
    QueryImpl OracleWorld (StateT (Fin segment.digit.val → Digest → Option Digest) PMF) :=
  (lazyImpl auxiliary).compose (segment.visibleWorldImpl high)
theorem visible_step_contact (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (endpoint : Digest) (trace : OtsContactTrace.Trace) (observed : Fin segment.digit.val → Digest → Option Digest)
    (hseen : OtsContactTrace.Seen segment endpoint trace ↔ Contact observed endpoint)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    OtsContactTrace.Seen segment endpoint (trace * hashObservationTrace input result.1) ↔ Contact result.2 endpoint := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simpa only [hashObservationTrace, mul_one] using hseen
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hparse,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          simpa only [hashObservationTrace, OtsContactTrace.seen_mul, OtsContactTrace.seen_of,
            OtsContactTrace.EntryContact, hparse, reduceCtorEq, false_and, exists_false, or_false] using hseen
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, hanswer, rfl⟩ := hresult
          have hconsistent : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer := by
            cases hrow : observed query.1 query.2 with
            | none => exact Or.inl rfl
            | some old =>
                rw [hrow, rowLaw, PMF.mem_support_pure_iff] at hanswer
                exact Or.inr (congrArg some hanswer.symm)
          rw [hashObservationTrace, OtsContactTrace.seen_mul, OtsContactTrace.seen_of, hseen,
            contact_record_consistent observed query answer endpoint hconsistent]
          simp only [OtsContactTrace.EntryContact, parse_input, Option.some.injEq, truncate_combine]
          apply or_congr Iff.rfl
          constructor
          · rintro ⟨other, rfl, h⟩; exact h
          · intro h; exact ⟨query, rfl, h⟩
theorem visible_pause_contact (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (endpoint : Digest) (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : OtsContactTrace.Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (hseen : OtsContactTrace.Seen segment endpoint trace ↔ Contact observed endpoint)
    (result : (OtsContactTrace.Trace × OracleComp OracleWorld Result) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((simulateQ (segment.visibleLazyImpl high auxiliary)
      (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace)).run observed).support) :
    OtsContactTrace.Seen segment endpoint result.1.1 ↔ Contact result.2 endpoint := by
  apply QueryPause.run_simulation_invariant stop _ (segment.visibleLazyImpl high auxiliary)
    (fun history rows => OtsContactTrace.Seen segment endpoint history ↔ Contact rows endpoint) _
    computation trace observed hseen result hresult
  intro history rows hrows _ input answer hanswer
  exact segment.visible_step_contact high auxiliary endpoint history rows hrows input answer hanswer
theorem visible_step_queryCount (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (trace : OtsContactTrace.Trace) (observed : Fin segment.digit.val → Digest → Option Digest)
    (hcount : queryCount observed ≤ OtsContactTrace.prefixCalls segment trace)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    queryCount result.2 ≤ OtsContactTrace.prefixCalls segment (trace * hashObservationTrace input result.1) := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
      obtain ⟨answer, _, rfl⟩ := hresult
      simpa only [hashObservationTrace, mul_one] using hcount
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hparse,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          rw [OtsContactTrace.prefixCalls_mul]
          exact hcount.trans (Nat.le_add_right _ _)
      | some query =>
          have hbytes := (segment.parse_some_iff bytes query).mp hparse
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hresult
          obtain ⟨answer, _, rfl⟩ := hresult
          have hselected : segment.Selects (.inr (segment.input query)) := by
            change segment.parse (segment.input query) ≠ none
            rw [parse_input]
            exact Option.some_ne_none query
          have hsingle := OtsContactTrace.prefixCalls_step segment (.inr (segment.input query)) (combine answer (high query)) 1
          simp only [mul_one, if_pos hselected, OtsContactTrace.prefixCalls_one, Nat.add_zero] at hsingle
          rw [OtsContactTrace.prefixCalls_mul, hsingle]
          exact (queryCount_record_le observed query answer).trans (Nat.add_le_add_right hcount 1)
theorem visible_pause_queryCount (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (stop : OtsContactTrace.Trace → Prop) [DecidablePred stop]
    {Result : Type} (computation : OracleComp OracleWorld Result) (trace : OtsContactTrace.Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest)
    (hcount : queryCount observed ≤ OtsContactTrace.prefixCalls segment trace)
    (result : (OtsContactTrace.Trace × OracleComp OracleWorld Result) × (Fin segment.digit.val → Digest → Option Digest))
    (hresult : result ∈ ((simulateQ (segment.visibleLazyImpl high auxiliary)
      (QueryPause.run stop (fun input answer history => history * hashObservationTrace input answer) computation trace)).run observed).support) :
    queryCount result.2 ≤ OtsContactTrace.prefixCalls segment result.1.1 := by
  apply QueryPause.run_simulation_invariant stop _ (segment.visibleLazyImpl high auxiliary)
    (fun history rows => queryCount rows ≤ OtsContactTrace.prefixCalls segment history) _
    computation trace observed hcount result hresult
  intro history rows hrows _ input answer hanswer
  exact segment.visible_step_queryCount high auxiliary history rows hrows input answer hanswer
end SphincsSecurity.Concrete.OtsPrefix
end

section


namespace SphincsSecurity.Concrete.OtsContactTrace
open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def SeenRow (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, segment.parse entry.1 = some query ∧ truncateHash entry.2 = answer
theorem seenRow_one (segment : OtsPrefix) (query : segment.Query) (answer : Digest) : ¬SeenRow segment query answer 1 := by
  simp [SeenRow]
theorem seenRow_of (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (entry : HashInput × HashOutput) :
    SeenRow segment query answer (FreeMonoid.of entry) ↔ segment.parse entry.1 = some query ∧ truncateHash entry.2 = answer := by
  simp [SeenRow]
theorem seenRow_mul (segment : OtsPrefix) (query : segment.Query) (answer : Digest) (before after : Trace) :
    SeenRow segment query answer (before * after) ↔ SeenRow segment query answer before ∨ SeenRow segment query answer after := by
  simp only [SeenRow, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]
def RowsObserved (segment : OtsPrefix) (trace : Trace) (observed : Fin segment.digit.val → Digest → Option Digest) : Prop :=
  ∀ query : segment.Query, ∀ answer, SeenRow segment query answer trace ↔ observed query.1 query.2 = some answer
theorem rowsObserved_empty (segment : OtsPrefix) : RowsObserved segment 1 (fun _ _ => none) := by
  intro query answer
  simp only [seenRow_one, reduceCtorEq]
end SphincsSecurity.Concrete.OtsContactTrace
namespace SphincsSecurity.Concrete.OtsPrefix
open _root_.OracleComp OracleSpec PartialChainEndpoint OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
private theorem record_some_iff {State : Type} [DecidableEq State] {n : Nat}
    (observed : Fin n → State → Option State) (query target : Fin n × State) (answer value : State)
    (hc : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer) :
    record observed query answer target.1 target.2 = some value ↔
      observed target.1 target.2 = some value ∨ query = target ∧ answer = value := by
  by_cases he : target = query
  · subst target
    simp only [record, Function.update_self, Option.some.injEq, true_and]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · rcases hc with hc | hc
        · simp only [hc, reduceCtorEq] at h
        · exact Option.some.inj (hc.symm.trans h)
      · exact h
  · have hrow : record observed query answer target.1 target.2 = observed target.1 target.2 := by
      by_cases hl : target.1 = query.1
      · have hi : target.2 ≠ query.2 := fun hi => he (Prod.ext hl hi)
        simp only [record, hl, Function.update_self, Function.update_of_ne hi]
      · simp only [record, Function.update_of_ne hl]
    simp only [hrow, Ne.symm he, false_and, or_false]
theorem visible_step_rows (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    (trace : Trace) (observed : Fin segment.digit.val → Digest → Option Digest) (hrows : RowsObserved segment trace observed)
    (input : OracleWorld.Domain) (result : OracleWorld.Range input × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ ((segment.visibleLazyImpl high auxiliary input).run observed).support) :
    RowsObserved segment (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, simulateQ_spec_query,
        lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
      obtain ⟨answer, _, rfl⟩ := hr
      simpa only [hashObservationTrace, mul_one] using hrows
  | inr bytes =>
      cases hp : segment.parse bytes with
      | none =>
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, hp,
            simulateQ_spec_query, lazyImpl, StateT.run_mk, PMF.mem_support_map_iff] at hr
          obtain ⟨answer, _, rfl⟩ := hr
          intro query value
          simpa only [hashObservationTrace, seenRow_mul, seenRow_of, hp, reduceCtorEq, false_and, or_false] using hrows query value
      | some query =>
          have hb := (segment.parse_some_iff bytes query).mp hp
          subst bytes
          simp only [visibleLazyImpl, QueryImpl.apply_compose, visibleWorldImpl, visibleHashImpl, parse_input,
            simulateQ_map, simulateQ_spec_query, lazyImpl, StateT.run_map, StateT.run_mk,
            PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, PMF.mem_support_map_iff] at hr
          obtain ⟨answer, ha, rfl⟩ := hr
          have hc : observed query.1 query.2 = none ∨ observed query.1 query.2 = some answer := by
            cases hrow : observed query.1 query.2 with
            | none => exact Or.inl rfl
            | some old =>
                rw [hrow, rowLaw, PMF.mem_support_pure_iff] at ha
                exact Or.inr (congrArg some ha.symm)
          intro target value
          rw [hashObservationTrace, seenRow_mul, seenRow_of, hrows target value, record_some_iff observed query target answer value hc]
          simp only [parse_input, Option.some.injEq, truncate_combine]
theorem visible_traced_rows (segment : OtsPrefix) (high : segment.Query → High) (auxiliary : QueryImpl OracleWorld PMF)
    {Result : Type} (computation : OracleComp OracleWorld Result) (history : Trace)
    (observed : Fin segment.digit.val → Digest → Option Digest) (hrows : RowsObserved segment history observed)
    (result : (Result × Trace) × (Fin segment.digit.val → Digest → Option Digest))
    (hr : result ∈ (lazyRun auxiliary (QueryPause.traced (segment.visibleObservationTrace high)
      (simulateQ (segment.visibleWorldImpl high) computation)) observed).support) :
    RowsObserved segment (history * result.1.2) result.2 := by
  have ht : QueryPause.traced (segment.visibleObservationTrace high) (simulateQ (segment.visibleWorldImpl high) computation) =
      simulateQ (segment.visibleWorldImpl high) (QueryPause.traced hashObservationTrace computation) :=
    segment.visible_observation_program high computation
  rw [ht, lazyRun, ← QueryImpl.simulateQ_compose] at hr
  exact QueryPause.traced_simulation_invariant hashObservationTrace (segment.visibleLazyImpl high auxiliary)
    (RowsObserved segment) (fun trace rows h input answer ha => segment.visible_step_rows high auxiliary trace rows h input answer ha)
    computation history observed hrows result hr
end SphincsSecurity.Concrete.OtsPrefix
end

section


namespace SphincsSecurity.Concrete.PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
theorem twoEdgeEvent_iff_rows {State : Type} {depth : Nat} (observed : Fin depth → State → Option State) (endpoint : State) :
    TwoEdgeEvent observed endpoint ↔ ∃ first last : Fin depth × State,
      first.1.val + 2 = depth ∧ last.1.val + 1 = depth ∧
        observed first.1 first.2 = some last.2 ∧ observed last.1 last.2 = some endpoint := by
  cases depth with
  | zero => simp only [TwoEdgeEvent, Prod.exists, Fin.exists_fin_zero]
  | succ depth =>
      cases depth with
      | zero =>
          constructor
          · exact False.elim
          · rintro ⟨first, _, hf, _⟩
            omega
      | succ depth =>
          constructor
          · rintro ⟨start, middle, hf, hl⟩
            exact ⟨⟨(Fin.last depth).castSucc, start⟩, ⟨Fin.last (depth + 1), middle⟩, rfl, rfl, hf, hl⟩
          · rintro ⟨⟨first, start⟩, ⟨last, middle⟩, hf, hl, hfirst, hlast⟩
            change first.val + 2 = depth + 2 at hf
            change last.val + 1 = depth + 2 at hl
            have hfi : first = (Fin.last depth).castSucc := by
              apply Fin.ext
              simp only [Fin.val_castSucc, Fin.val_last]
              omega
            have hla : last = Fin.last (depth + 1) := by
              apply Fin.ext
              simp only [Fin.val_last]
              omega
            subst first last
            exact ⟨start, middle, hfirst, hlast⟩
end SphincsSecurity.Concrete.PartialChainEndpoint
namespace SphincsSecurity.Concrete.OtsContactTrace
set_option backward.isDefEq.respectTransparency false
def SeenTwoEdge (segment : OtsPrefix) (endpoint : Digest) (trace : Trace) : Prop :=
  ∃ first last : segment.Query, first.1.val + 2 = segment.digit.val ∧ last.1.val + 1 = segment.digit.val ∧
    SeenRow segment first last.2 trace ∧ SeenRow segment last endpoint trace
theorem RowsObserved.twoEdge_iff {segment : OtsPrefix} {trace : Trace} {observed : Fin segment.digit.val → Digest → Option Digest}
    (h : RowsObserved segment trace observed) (endpoint : Digest) :
    SeenTwoEdge segment endpoint trace ↔ PartialChainEndpoint.TwoEdgeEvent observed endpoint := by
  dsimp only [RowsObserved] at h
  simp only [SeenTwoEdge, h, PartialChainEndpoint.twoEdgeEvent_iff_rows]
end SphincsSecurity.Concrete.OtsContactTrace
end

section





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
noncomputable def mkSample (T : Answers) (run : SeedResult) : RefSample :=
  ⟨T, (evalWithAnswerFn T keygen).1, traceOf T run.2⟩
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
open PrefixGame in
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
def PrefixRowAt (answers : Answers) (a : ChainAddr) (input : HashInput) : Prop :=
  ∃ step value, step < depth answers a ∧ input = chainRow a step value
structure PrefixView where
  depth : Nat
  frontier : Digest
  rows : Nat → Digest → Option Digest
  count : Nat
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
theorem reference_eq_mixture (adversary : AdversaryP) (q : Nat) (a : ChainAddr) (ha : WotsExtract.SourceChain a) :
    (referenceExperiment adversary q).map (sampleView a) =
      (restLaw adversary).bind (fun R =>
        (realRun (fun _ => SphincsSecurity.Concrete.OtsPrefix.uniformImpl) (seedGame adversary q a R)
          (fun _ _ => none)).map (runView a R)) :=
  reference_map_eq_mixture adversary q a ha (sampleView a) (runView a)
    (sampleView_coupled adversary q a)
def PrefixView.TwoEdge (v : PrefixView) : Prop :=
  2 ≤ v.depth ∧ ∃ start middle, v.rows (v.depth - 2) start = some middle ∧ v.rows (v.depth - 1) middle = some v.frontier
def PrefixView.Contact (v : PrefixView) : Prop :=
  1 ≤ v.depth ∧ ∃ value, v.rows (v.depth - 1) value = some v.frontier
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
end SigGolfCandidate.T3.Security.Wots
end
