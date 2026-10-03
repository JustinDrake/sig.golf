import SigGolfCandidate.SphincsSecurity.Proof.Reference.CausalFrontierAllocation
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixAllocation
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingFreshRow
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsContactTrace
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingOracleObservation
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTraceInvariant
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingTablePrior
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryTracePotential

section

namespace SphincsSecurity.Concrete
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def SigningBoundaryTrace.nonmessageCalls (trace : SigningBoundaryTrace) : Nat :=
  trace.toList.countP Option.isNone
theorem SigningBoundaryTrace.nonmessageCalls_mul (first second : SigningBoundaryTrace) :
    (first * second).nonmessageCalls = first.nonmessageCalls + second.nonmessageCalls := by
  simp only [SigningBoundaryTrace.nonmessageCalls, FreeMonoid.toList_mul, List.countP_append]
theorem SigningBoundaryTrace.partition (trace : SigningBoundaryTrace) :
    trace.nonmessageCalls + trace.messageCalls.length = trace.hashCalls := by
  unfold SigningBoundaryTrace.nonmessageCalls SigningBoundaryTrace.messageCalls SigningBoundaryTrace.hashCalls
  generalize trace.toList = records
  induction records with
  | nil => rfl
  | cons entry records ih =>
      cases entry <;> simp_all <;> omega
namespace CausalFrontierProgram
def NonmessageHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ¬FtsProbeSimulation.MessageHashInput parameter input
noncomputable instance (parameter : PublicParameter) : DecidablePred (NonmessageHash parameter) := Classical.decPred _
noncomputable def nonmessageTraceCharge (parameter : PublicParameter) : TraceCharge parameter where
  selected := NonmessageHash parameter
  decidable := inferInstance
  cost := SigningBoundaryTrace.nonmessageCalls
  cost_mul := SigningBoundaryTrace.nonmessageCalls_mul
  uniform := by intro input; exact not_false
  step := by
    intro input answer
    cases input with
    | inl input => simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls]
    | inr input =>
        by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input <;>
          simp [NonmessageHash, signingBoundaryTrace, SigningBoundaryTrace.nonmessageCalls, hmessage]
theorem game_nonmessage_recorded_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × List OracleWorld.Domain)
    (hresult : result ∈ support (QueryCap.recorded (game parameter external ftsSecret words frontier adversary))) :
    QueryCap.calls (NonmessageHash parameter) result.2 + result.1.2.messageCalls.length ≤ result.1.2.hashCalls := by
  have h := QueryCap.recorded_calls_le (NonmessageHash parameter) _ (fun result => result.2.nonmessageCalls)
    (TraceCharge.game_counted_le (nonmessageTraceCharge parameter) external ftsSecret words frontier adversary) result hresult
  exact (Nat.add_le_add_right h _).trans_eq (SigningBoundaryTrace.partition result.1.2)
end CausalFrontierProgram
end SphincsSecurity.Concrete
end

section


namespace SphincsSecurity.Concrete.QueryClass
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
def EncodingHash (parameter : PublicParameter) : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr input => ∃ position, AtEncodingPosition parameter input position
def OtherHash (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) : Prop :=
  CausalFrontierProgram.NonmessageHash parameter input ∧ ¬EncodingHash parameter input ∧
    ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input
noncomputable instance (parameter : PublicParameter) : DecidablePred (EncodingHash parameter) := Classical.decPred _
noncomputable instance (parameter : PublicParameter) (words : OtsReferenceWords) : DecidablePred (OtherHash parameter words) :=
  Classical.decPred _
theorem encoding_nonmessage (parameter : PublicParameter) (input : OracleWorld.Domain) (hencoding : EncodingHash parameter input) :
    CausalFrontierProgram.NonmessageHash parameter input := by
  cases input with
  | inl input => exact False.elim hencoding
  | inr input =>
      obtain ⟨position, payload, hinput⟩ := hencoding
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective parameter (by trivial) (by trivial) (hinput.symm.trans hmessage.symm)).1
      simp only [EncodingPosition.domain, reduceCtorEq] at hdomain
theorem prefix_nonmessage (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    CausalFrontierProgram.NonmessageHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨message, hmessage⟩
      have hdomain := (tweakableHashInput_injective segment.parameter (by trivial) (by trivial)
        (hinput.symm.trans hmessage.symm)).1
      simp only [reduceCtorEq] at hdomain
theorem prefix_not_encoding (segment : OtsPrefix) (input : OracleWorld.Domain) (hprefix : segment.Selects input) :
    ¬EncodingHash segment.parameter input := by
  cases input with
  | inl input => exact False.elim hprefix
  | inr input =>
      obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hprefix
      have hinput := (segment.parse_some_iff input query).mp hquery
      rintro ⟨position, hencoding⟩
      exact hencoding.not_atPosition (.chain segment.lay segment.tree segment.leaf segment.chainIdx (segment.step query.1))
        ⟨digestBytes query.2, hinput⟩
theorem allocation_step (parameter : PublicParameter) (words : OtsReferenceWords) (input : OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) +
        (if EncodingHash parameter input then 1 else 0) + (if OtherHash parameter words input then 1 else 0) =
      if CausalFrontierProgram.NonmessageHash parameter input then 1 else 0 := by
  classical
  by_cases hprefix : ∃ address, (OtsPrefix.atAddress parameter words address).Selects input
  · obtain ⟨address, haddress⟩ := hprefix
    have hsum : (∑ other : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words other).Selects input then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single address]
      · exact if_pos haddress
      · intro other _ hne
        exact if_neg (fun hother => hne (OtsPrefix.atAddress_selects_unique parameter words other address input hother haddress))
      · simp
    have hn := prefix_nonmessage _ input haddress
    have he := prefix_not_encoding _ input haddress
    have ho : ¬OtherHash parameter words input := fun h => h.2.2 address haddress
    simp only [hsum, if_neg he, if_neg ho, if_pos hn, Nat.add_zero]
  · have hnone : ∀ address, ¬(OtsPrefix.atAddress parameter words address).Selects input := by simpa using hprefix
    have hsum : (∑ address : OtsPrefix.ChainAddress, if (OtsPrefix.atAddress parameter words address).Selects input then 1 else 0) = 0 := by
      simp only [hnone, if_false, Finset.sum_const_zero]
    rw [hsum, Nat.zero_add]
    by_cases he : EncodingHash parameter input
    · have hn := encoding_nonmessage parameter input he
      simp only [he, hn, OtherHash, not_true_eq_false, and_false, false_and, if_true, if_false, Nat.add_zero]
    · by_cases hn : CausalFrontierProgram.NonmessageHash parameter input <;>
        simp [he, hn, OtherHash, hnone]
theorem allocation_calls (parameter : PublicParameter) (words : OtsReferenceWords) (inputs : List OracleWorld.Domain) :
    (∑ address : OtsPrefix.ChainAddress, QueryCap.calls (OtsPrefix.atAddress parameter words address).Selects inputs) +
        QueryCap.calls (EncodingHash parameter) inputs + QueryCap.calls (OtherHash parameter words) inputs =
      QueryCap.calls (CausalFrontierProgram.NonmessageHash parameter) inputs := by
  induction inputs with
  | nil => simp only [QueryCap.calls_nil, Finset.sum_const_zero, Nat.add_zero]
  | cons input inputs ih =>
      simp only [QueryCap.calls_cons, Finset.sum_add_distrib]
      have h := allocation_step parameter words input
      omega
end SphincsSecurity.Concrete.QueryClass
end

section

namespace SphincsSecurity.OtsCode
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
def backwardWeight (reference candidate : Encoding) : Nat :=
  ∑ index : ChainIndex, ((reference index).val - (candidate index).val)
private theorem two_terms_le_sum (f : ChainIndex → Nat) {left right : ChainIndex} (hne : left ≠ right) :
    f left + f right ≤ ∑ index, f index := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := f) (Finset.subset_univ ({left, right} : Finset ChainIndex))
    (fun _ _ _ => Nat.zero_le _)
  simpa only [Finset.sum_pair hne] using h
private theorem single_of_sum_one (f : ChainIndex → Nat) (hsum : (∑ index, f index) = 1) :
    ∃ index, f index = 1 ∧ ∀ other, other ≠ index → f other = 0 := by
  have hnonzero : ∃ index, f index ≠ 0 := by
    by_contra hnone
    push Not at hnone
    have hz : (∑ index, f index) = 0 := Finset.sum_eq_zero fun index _ => hnone index
    omega
  obtain ⟨index, hi⟩ := hnonzero
  have hle : f index ≤ ∑ other, f other := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  have hone : f index = 1 := by omega
  refine ⟨index, hone, ?_⟩
  intro other hne
  have hpair := two_terms_le_sum f hne
  omega
theorem unitNeighbor_of_backwardWeight_one {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 1) :
    ∃ lowered, UnitNeighborAt reference candidate lowered := by
  obtain ⟨lowered, hlower, hothers⟩ := single_of_sum_one (fun index => (reference index).val - (candidate index).val) hweight
  refine ⟨lowered, hreference, hcandidate, ?_, fun index hne => ?_⟩
  · omega
  · have hdown := hothers index hne
    omega
theorem eq_of_backwardWeight_zero {reference candidate : Encoding}
    (hreference : Valid reference) (hcandidate : Valid candidate) (hweight : backwardWeight reference candidate = 0) :
    reference = candidate := by
  apply eq_of_le_of_valid hreference hcandidate
  intro index
  have hle : (reference index).val - (candidate index).val ≤ backwardWeight reference candidate := by
    unfold backwardWeight
    exact Finset.single_le_sum (f := fun index : ChainIndex => (reference index).val - (candidate index).val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  omega
theorem backwardWeight_two_witness {reference candidate : Encoding} (hweight : 2 ≤ backwardWeight reference candidate) :
    (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hlarge : ∃ index, (candidate index).val + 2 ≤ (reference index).val
  · exact Or.inl hlarge
  have hnonzero : ∃ index, (candidate index).val < (reference index).val := by
    by_contra hnone
    push Not at hnone
    have hz : backwardWeight reference candidate = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      exact Nat.sub_eq_zero_of_le (hnone index)
    omega
  obtain ⟨left, hl⟩ := hnonzero
  by_cases hother : ∃ right, left ≠ right ∧ (candidate right).val < (reference right).val
  · obtain ⟨right, hne, hr⟩ := hother
    exact Or.inr ⟨left, right, hne, hl, hr⟩
  · have hzero : ∀ index, index ≠ left → (reference index).val - (candidate index).val = 0 := by
      intro index hne
      have hn : ¬(candidate index).val < (reference index).val := fun hi => hother ⟨index, hne.symm, hi⟩
      omega
    have hsum : backwardWeight reference candidate = (reference left).val - (candidate left).val := by
      apply Finset.sum_eq_single left
      · intro index _ hne
        exact hzero index hne
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    have hn := not_exists.mp hlarge left
    omega
theorem valid_encoding_classification {reference candidate : Encoding} (hreference : Valid reference) (hcandidate : Valid candidate) :
    reference = candidate ∨ (∃ lowered, UnitNeighborAt reference candidate lowered) ∨
      (∃ index, (candidate index).val + 2 ≤ (reference index).val) ∨
      ∃ left right, left ≠ right ∧ (candidate left).val < (reference left).val ∧ (candidate right).val < (reference right).val := by
  by_cases hzero : backwardWeight reference candidate = 0
  · exact Or.inl (eq_of_backwardWeight_zero hreference hcandidate hzero)
  by_cases hone : backwardWeight reference candidate = 1
  · exact Or.inr (Or.inl (unitNeighbor_of_backwardWeight_one hreference hcandidate hone))
  exact Or.inr (Or.inr (backwardWeight_two_witness (by omega)))
end SphincsSecurity.OtsCode
end

section




namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ OtsContactTrace.contacts canonicalEncodingInputs
def EntryMarker (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (entry : HashInput × HashOutput) : Prop :=
  AtEncodingPosition parameter entry.1 ⟨address.1, address.2.1, address.2.2.1⟩ ∧
    entry.1 ∈ canonicalEncodingInputs parameter ∧
    ∃ candidate, decodeEncodingOutput entry.2 = some candidate ∧
      OtsCode.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2
theorem entryMarker_encoding_iff (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (message : Digest) (counter : Counter) (output : HashOutput) :
    EntryMarker parameter words address
      (tweakableHashInput parameter (.encoding address.1 address.2.1 address.2.2.1)
        (digestBytes message ++ counterBytes counter), output) ↔
      ∃ candidate, decodeEncodingOutput output = some candidate ∧
        OtsCode.UnitNeighborAt (words address.1 address.2.1 address.2.2.1) candidate address.2.2.2 := by
  have hcounter : counter.toNat < 2 ^ counterBits := counter.isLt
  have hin := encodingRetryInput_mem_canonicalEncodingInputs_wide parameter
    ⟨address.1, address.2.1, address.2.2.1⟩ message ⟨counter.toNat, hcounter⟩
  simp only [encodingRetryInput, BitVec.ofNat_toNat] at hin
  exact and_iff_right ⟨_, rfl⟩ |>.trans (and_iff_right hin)
def Seen (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (trace : OtsContactTrace.Trace) : Prop := ∃ entry ∈ trace.toList, EntryMarker parameter words address entry
theorem entryMarker_unique (parameter : PublicParameter) (words : OtsReferenceWords) (entry : HashInput × HashOutput)
    (left right : OtsPrefix.ChainAddress) (hleft : EntryMarker parameter words left entry) (hright : EntryMarker parameter words right entry) :
    left = right := by
  rcases left with ⟨leftLay, leftTree, leftLeaf, leftChain⟩
  rcases right with ⟨rightLay, rightTree, rightLeaf, rightChain⟩
  obtain ⟨hl, _, leftWord, hdecodeLeft, hneighborLeft⟩ := hleft
  obtain ⟨hr, _, rightWord, hdecodeRight, hneighborRight⟩ := hright
  have hp := atEncodingPosition_unique hl hr
  simp only [EncodingPosition.mk.injEq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  have hw : leftWord = rightWord := Option.some.inj (hdecodeLeft.symm.trans hdecodeRight)
  subst rightWord
  have hc := hneighborLeft.lowered_unique hneighborRight
  cases hc
  rfl
theorem entryMarker_not_contact (parameter : PublicParameter) (words : OtsReferenceWords) (address other : OtsPrefix.ChainAddress)
    (endpoint : Digest) (entry : HashInput × HashOutput) (hm : EntryMarker parameter words address entry) :
    ¬OtsContactTrace.EntryContact (OtsPrefix.atAddress parameter words other) endpoint entry := by
  intro hc
  exact QueryClass.prefix_not_encoding (OtsPrefix.atAddress parameter words other) (.inr entry.1)
    (OtsContactTrace.entryContact_selects _ endpoint entry hc) ⟨_, hm.1⟩
theorem seen_one (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) :
    ¬Seen parameter words address 1 := by simp [Seen]
theorem seen_of (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) :
    Seen parameter words address (FreeMonoid.of entry) ↔ EntryMarker parameter words address entry := by simp [Seen]
theorem seen_mul (parameter : PublicParameter) (words : OtsReferenceWords) (address : OtsPrefix.ChainAddress) (before after : OtsContactTrace.Trace) :
    Seen parameter words address (before * after) ↔ Seen parameter words address before ∨ Seen parameter words address after := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]
noncomputable def markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) :
    Finset OtsPrefix.ChainAddress := Finset.univ.filter fun address => Seen parameter words address trace
theorem mem_markers (parameter : PublicParameter) (words : OtsReferenceWords) (trace : OtsContactTrace.Trace) (address : OtsPrefix.ChainAddress) :
    address ∈ markers parameter words trace ↔ Seen parameter words address trace := by
  simp only [markers, Finset.mem_filter, Finset.mem_univ, true_and]
theorem markers_one (parameter : PublicParameter) (words : OtsReferenceWords) : markers parameter words 1 = ∅ := by
  ext address
  simp only [mem_markers, seen_one, Finset.notMem_empty]
theorem markers_mul (parameter : PublicParameter) (words : OtsReferenceWords) (before after : OtsContactTrace.Trace) :
    markers parameter words (before * after) = markers parameter words before ∪ markers parameter words after := by
  ext address
  simp only [mem_markers, seen_mul, Finset.mem_union]
attribute [local irreducible] markers
end SphincsSecurity.Concrete.OtsEncodingMarker
end

section



namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec UniformTableCompletion RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs Finset.univ
def TraceConsistent (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) : Prop :=
  (∀ cell output, (cell.val, output) ∈ trace.toList → allowed cell = {output}) ∧
    ∀ cell, (∀ output, (cell.val, output) ∉ trace.toList) → allowed cell = initial cell
theorem traceConsistent_one (parameter : PublicParameter)
    (initial : canonicalEncodingInputs parameter → Finset HashOutput) :
    TraceConsistent parameter initial 1 initial := by
  constructor
  · simp
  · intros; rfl
theorem TraceConsistent.outside {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (input : HashInput)
    (houtside : input ∉ canonicalEncodingInputs parameter) (output : HashOutput) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (input, output)) allowed := by
  constructor
  · intro cell answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, _⟩
    · exact h.1 cell answer hentry
    · exact False.elim (houtside (heq ▸ cell.property))
  · intro cell hfresh
    apply h.2 cell
    intro answer hentry
    apply hfresh answer
    exact List.mem_append_left _ hentry
theorem TraceConsistent.disclose {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (output : HashOutput) (houtput : output ∈ allowed cell) :
    TraceConsistent parameter initial (trace * FreeMonoid.of (cell.val, output))
      (discloseTableValue allowed cell output) := by
  constructor
  · intro other answer hentry
    simp only [FreeMonoid.toList_mul, FreeMonoid.toList_of, List.mem_append,
      List.mem_singleton, Prod.mk.injEq] at hentry
    rcases hentry with hentry | ⟨heq, rfl⟩
    · by_cases heq : other = cell
      · subst other
        have heq : output = answer := Finset.mem_singleton.mp ((h.1 cell answer hentry) ▸ houtput)
        simp only [discloseTableValue, Function.update_self, heq]
      · rw [discloseTableValue, Function.update_of_ne heq]
        exact h.1 other answer hentry
    · have heq : other = cell := Subtype.ext heq
      subst other
      exact Function.update_self cell {answer} allowed
  · intro other hfresh
    have heq : other ≠ cell := by
      intro heq
      subst other
      exact hfresh output (List.mem_append_right _ (by simp))
    rw [discloseTableValue, Function.update_of_ne heq]
    apply h.2 other
    intro answer hentry
    exact hfresh answer (List.mem_append_left _ hentry)
noncomputable def lazyWorldImpl (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding) :
    QueryImpl OracleWorld (StateT (canonicalEncodingInputs parameter → Finset HashOutput) SPMF) :=
  (UniformTableObservation.lazyImpl (auxiliary parameter inputs hencoding outside)).compose (translate parameter)
theorem lazyRun_eq_simulate {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside computation allowed =
      (simulateQ (lazyWorldImpl parameter inputs hencoding outside) computation).run allowed := by
  rw [lazyRun, UniformTableObservation.lazyRun, lazyWorldImpl, QueryImpl.simulateQ_compose]
theorem lazyRun_map {Result Next : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (f : Result → Next)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput) :
    lazyRun parameter inputs hencoding outside (f <$> computation) allowed =
      (fun result => (f result.1, result.2)) <$> lazyRun parameter inputs hencoding outside computation allowed := by
  simp only [lazyRun_eq_simulate, simulateQ_map, StateT.run_map]
theorem lazyWorldImpl_traceConsistent (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (initial allowed : canonicalEncodingInputs parameter → Finset HashOutput) (trace : OtsContactTrace.Trace)
    (h : TraceConsistent parameter initial trace allowed) (input : OracleWorld.Domain)
    (result : OracleWorld.Range input × (canonicalEncodingInputs parameter → Finset HashOutput))
    (hr : (lazyWorldImpl parameter inputs hencoding outside input).run allowed result ≠ 0) :
    TraceConsistent parameter initial (trace * hashObservationTrace input result.1) result.2 := by
  cases input with
  | inl input =>
      simp only [lazyWorldImpl, QueryImpl.compose, translate, simulateQ_spec_query,
        UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
      obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
      subst result
      simpa only [hashObservationTrace, mul_one] using h
  | inr input =>
      by_cases hc : input ∈ canonicalEncodingInputs parameter
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, ha, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        have hin : answer ∈ allowed ⟨input, hc⟩ := by
          by_contra hn
          simp only [cell_apply, if_neg hn, ne_eq, not_true_eq_false] at ha
        exact h.disclose ⟨input, hc⟩ answer hin
      · simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_neg hc, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, ← bind_pure_comp] at hr
        obtain ⟨answer, _, heq⟩ := (bind_nonzero _ _ _).mp hr
        simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at heq
        subst result
        exact h.outside input hc answer
theorem TraceConsistent.cached_reply {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (previous output : HashOutput) (hp : (cell.val, previous) ∈ trace.toList)
    (ho : UniformTableCompletion.cell (allowed cell) output ≠ 0) : output = previous := by
  rw [h.1 cell previous hp, cell_apply] at ho
  by_contra hn
  simp only [Finset.mem_singleton, hn, if_false, ne_eq, not_true_eq_false] at ho
theorem TraceConsistent.new_reply_probability_le {parameter : PublicParameter}
    {initial allowed : canonicalEncodingInputs parameter → Finset HashOutput} {trace : OtsContactTrace.Trace}
    (h : TraceConsistent parameter initial trace allowed) (cell : canonicalEncodingInputs parameter)
    (event : HashOutput → Prop) :
    Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList | UniformTableCompletion.cell (allowed cell)] ≤
      Pr[event | UniformTableCompletion.cell (initial cell)] := by
  by_cases hfresh : ∀ output, (cell.val, output) ∉ trace.toList
  · rw [h.2 cell hfresh]
    exact _root_.probEvent_mono (fun _ _ he => he.1)
  · obtain ⟨previous, hp⟩ := not_forall.mp hfresh
    have hp : (cell.val, previous) ∈ trace.toList := not_not.mp hp
    have hz : Pr[fun output => event output ∧ (cell.val, output) ∉ trace.toList |
        UniformTableCompletion.cell (allowed cell)] = 0 := by
      apply probEvent_eq_zero
      intro output ho he
      have heq := h.cached_reply cell previous output hp ((SPMF.mem_support_iff _ _).mp ho)
      exact he.2 (heq.symm ▸ hp)
    rw [hz]
    exact bot_le
end SphincsSecurity.Concrete.EncodingObservation
end

section


namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs
theorem entryMarker_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (address : OtsPrefix.ChainAddress)
    (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  by_cases hp : AtEncodingPosition parameter cell.val ⟨address.1, address.2.1, address.2.2.1⟩
  · refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_neighbor_le
      (referenceFamilyWords selections dummy address.1 address.2.1 address.2.2.1) address.2.2.2 _ _
      (referenceEncodingAllowed_fresh parameter messages selections dummy cell _ hp))
    intro output _ hm
    obtain ⟨_, _, candidate, hd, hn⟩ := hm
    exact OtsCode.mem_decodingDigests.mpr ⟨candidate, OtsCode.mem_unitNeighbors.mpr hn, hd⟩
  · have he : (fun output : HashOutput => EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output)) =
        fun _ => False := by
      funext output
      apply propext
      exact ⟨fun hm => hp hm.1, False.elim⟩
    rw [he]
    simp only [probEvent_eq_tsum_ite, if_false, tsum_zero, zero_le]
theorem encodingInput_position (parameter : PublicParameter) (input : HashInput)
    (hc : input ∈ canonicalEncodingInputs parameter) : ∃ position, AtEncodingPosition parameter input position := by
  rw [canonicalEncodingInputs] at hc
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hc
  obtain ⟨position, pair, hinput⟩ := hc
  exact ⟨position, _, hinput.symm⟩
theorem entryMarker_any_allowed_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (cell : canonicalEncodingInputs parameter) :
    Pr[fun output : HashOutput => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address (cell.val, output) |
      PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
        (referenceEncodingAllowed_nonempty parameter messages selections cell)] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  obtain ⟨position, hp⟩ := encodingInput_position parameter cell.val cell.property
  refine (_root_.probEvent_mono (mx := (liftM (PMF.uniformOfFinset (referenceEncodingAllowed parameter messages selections cell)
      (referenceEncodingAllowed_nonempty parameter messages selections cell)) : SPMF HashOutput)) ?_).trans (freshEncodingSupport_all_neighbors_le
    (referenceFamilyWords selections dummy position.lay position.tree position.leafIdx) _ _
    (referenceEncodingAllowed_fresh parameter messages selections dummy cell position hp))
  intro output _ hm
  obtain ⟨⟨lay, tree, leaf, chain⟩, hposition, _, candidate, hd, hn⟩ := hm
  have he := atEncodingPosition_unique hposition hp
  subst position
  exact OtsCode.mem_decodingDigests.mpr ⟨candidate, OtsCode.mem_allUnitNeighbors.mpr ⟨chain, hn⟩, hd⟩
end SphincsSecurity.Concrete.OtsEncodingMarker
end

section


namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers
def NewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (address : OtsPrefix.ChainAddress) (entry : HashInput × HashOutput) : Prop :=
  EntryMarker parameter words address entry ∧ ¬Seen parameter words address history
theorem NewMarker.not_mem {parameter : PublicParameter} {words : OtsReferenceWords} {history : OtsContactTrace.Trace}
    {address : OtsPrefix.ChainAddress} {entry : HashInput × HashOutput}
    (h : NewMarker parameter words history address entry) : entry ∉ history.toList :=
  fun hin => h.2 ⟨entry, hin, h.1⟩
theorem newMarker_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (address : OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ (OtsCode.unitNeighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ⟨h.1, h.not_mem⟩)).trans
    ((hc.new_reply_probability_le row (fun output => EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
    entryMarker_allowed_le parameter messages selections dummy address row
theorem newMarker_subset_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (addresses : Finset OtsPrefix.ChainAddress) (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address ∈ addresses, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ ((OtsCode.unitNeighborBound : ENNReal) * (addresses.card : ENNReal)) / Fintype.card Digest := by
  have h := (probEvent_exists_finset_le_sum addresses (cell (allowed row))
    (fun address output => NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output))).trans
    (Finset.sum_le_sum fun address _ => newMarker_cell_le parameter messages selections dummy history allowed hc address row)
  simpa only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
theorem newMarker_any_cell_le (parameter : PublicParameter) (messages : EncodingPosition → Digest)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (row : canonicalEncodingInputs parameter) :
    Pr[fun output => ∃ address, NewMarker parameter (referenceFamilyWords selections dummy) history address (row.val, output) |
      cell (allowed row)] ≤ (OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal) := by
  refine (_root_.probEvent_mono (fun _ _ h => ?_)).trans
    ((hc.new_reply_probability_le row (fun output => ∃ address, EntryMarker parameter (referenceFamilyWords selections dummy) address
      (row.val, output))).trans ?_)
  · obtain ⟨address, hm⟩ := h
    exact ⟨⟨address, hm.1⟩, hm.not_mem⟩
  · simpa only [cell, dif_pos (referenceEncodingAllowed_nonempty parameter messages selections row), SPMF.probEvent_liftM] using
      entryMarker_any_allowed_le parameter messages selections dummy row
section Cardinality
local instance (priority := 11000) : DecidableEq OtsPrefix.ChainAddress := inferInstance
attribute [local instance 10000] Classical.propDecidable
theorem markers_step_card (parameter : PublicParameter) (words : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (entry : HashInput × HashOutput) :
    (markers parameter words (history * FreeMonoid.of entry)).card = (markers parameter words history).card +
      if ∃ address, NewMarker parameter words history address entry then 1 else 0 := by
  rw [markers_mul]
  by_cases hm : ∃ address, NewMarker parameter words history address entry
  · obtain ⟨address, he, hn⟩ := hm
    have hi : address ∈ markers parameter words (FreeMonoid.of entry) := (mem_markers _ _ _ _).mpr ((seen_of _ _ _ _).mpr he)
    have hs : markers parameter words (FreeMonoid.of entry) = {address} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, fun other ho =>
        entryMarker_unique parameter words entry other address ((seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp ho)) he⟩
    have ha : address ∉ markers parameter words history := fun hin => hn ((mem_markers _ _ _ _).mp hin)
    rw [if_pos ⟨address, he, hn⟩, hs, Finset.union_singleton, Finset.card_insert_of_notMem ha]
  · have hs : markers parameter words (FreeMonoid.of entry) ⊆ markers parameter words history := by
      intro address hi
      by_contra hn
      exact hm ⟨address, (seen_of _ _ _ _).mp ((mem_markers _ _ _ _).mp hi),
        fun hs => hn ((mem_markers _ _ _ _).mpr hs)⟩
    rw [if_neg hm, Finset.union_eq_left.mpr hs, Nat.add_zero]
end Cardinality
end SphincsSecurity.Concrete.OtsEncodingMarker
end

section

namespace SphincsSecurity.Concrete.OtsEncodingMarker
open _root_.OracleComp OracleSpec UniformTableCompletion EncodingObservation RetainedObservation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs markers
def QueryNewMarker (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : OracleWorld.Domain) (answer : OracleWorld.Range input) : Prop :=
  ∃ address, Seen parameter words address (history * hashObservationTrace input answer) ∧ ¬Seen parameter words address history
theorem queryNewMarker_coin (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : unifSpec.Domain) (answer : unifSpec.Range input) : ¬QueryNewMarker parameter words history (.inl input) answer := by
  simp only [QueryNewMarker, hashObservationTrace, mul_one, and_not_self, exists_false, not_false_eq_true]
theorem queryNewMarker_hash (parameter : PublicParameter) (words : OtsReferenceWords) (history : OtsContactTrace.Trace)
    (input : HashInput) (output : HashOutput) :
    QueryNewMarker parameter words history (.inr input) output ↔ ∃ address, NewMarker parameter words history address (input, output) := by
  simp only [QueryNewMarker, hashObservationTrace, seen_mul, seen_of, or_and_right, and_not_self, false_or, NewMarker]
theorem queryNewMarker_any_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history input result.1 |
      (lazyWorldImpl parameter inputs hencoding outside input).run allowed] ≤
      ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inl input) result.1 |
          (lazyWorldImpl parameter inputs hencoding outside (.inl input)).run allowed] = 0 :=
        probEvent_eq_zero fun result _ => queryNewMarker_coin _ _ _ _ result.1
      rw [hz]
      exact bot_le
  | inr input =>
      by_cases hi : input ∈ canonicalEncodingInputs parameter
      · have he : QueryClass.EncodingHash parameter (.inr input) := encodingInput_position parameter input hi
        simp only [lazyWorldImpl, QueryImpl.compose, translate, dif_pos hi, simulateQ_spec_query,
          UniformTableObservation.lazyImpl, StateT.run_mk, probEvent_map, Function.comp_def,
          queryNewMarker_hash, if_pos he, Nat.cast_one, mul_one]
        exact newMarker_any_cell_le parameter messages selections dummy history allowed hc ⟨input, hi⟩
      · have hz : Pr[fun result => QueryNewMarker parameter (referenceFamilyWords selections dummy) history (.inr input) result.1 |
            (lazyWorldImpl parameter inputs hencoding outside (.inr input)).run allowed] = 0 := by
          apply probEvent_eq_zero
          intro result _ hm
          obtain ⟨_, hm⟩ := (queryNewMarker_hash _ _ _ _ _).mp hm
          exact hi hm.1.2.1
        rw [hz]
        exact bot_le
section Potential
attribute [local instance 10000] Classical.propDecidable
theorem markers_query_potential_le (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (history : OtsContactTrace.Trace) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (input : OracleWorld.Domain) :
    (∑' result, Pr[= result | (lazyWorldImpl parameter inputs hencoding outside input).run allowed] *
      ((markers parameter (referenceFamilyWords selections dummy) (history * hashObservationTrace input result.1)).card : ENNReal)) ≤
      ((markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ((if QueryClass.EncodingHash parameter input then 1 else 0 : Nat) : ENNReal) := by
  cases input with
  | inl input =>
      simp only [hashObservationTrace, mul_one, QueryClass.EncodingHash, if_false, Nat.cast_zero,
        mul_zero, add_zero, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one
  | inr input =>
      simp only [hashObservationTrace, markers_step_card, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
        mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero, ← probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
      apply add_le_add (mul_le_of_le_one_left zero_le tsum_probOutput_le_one)
      simpa only [queryNewMarker_hash, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_ite, mul_one, mul_zero] using
        queryNewMarker_any_le parameter inputs hencoding outside messages selections dummy history allowed hc (.inr input)
end Potential
end SphincsSecurity.Concrete.OtsEncodingMarker
end

section


namespace SphincsSecurity.Concrete.UniformTableObservation
open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
theorem lazyRun_neverFail {Coordinate Value AuxIndex Result : Type} [DecidableEq Coordinate]
    {auxSpec : OracleSpec AuxIndex} (auxiliary : QueryImpl auxSpec SPMF)
    (haux : ∀ input, NeverFail (auxiliary input))
    (computation : OracleComp (auxSpec + TableSpec Coordinate Value) Result)
    (allowed : Coordinate → Finset Value) (ha : ∀ coordinate, (allowed coordinate).Nonempty) :
    NeverFail (lazyRun auxiliary computation allowed) := by
  induction computation using OracleComp.inductionOn generalizing allowed with
  | pure value => rw [lazyRun_pure]; infer_instance
  | query_bind input next ih =>
      cases input with
      | inl input =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          exact ⟨haux input, fun answer _ => ih answer allowed ha⟩
      | inr coordinate =>
          simp only [lazyRun_query_bind, lazyImpl, StateT.run_mk, bind_map_left, neverFail_bind_iff]
          constructor
          · rw [cell, dif_pos (ha coordinate)]
            exact ⟨probFailure_of_liftM_PMF _⟩
          · intro answer _
            exact ih answer _ (discloseTableValue_nonempty allowed ha coordinate answer)
end SphincsSecurity.Concrete.UniformTableObservation
namespace SphincsSecurity.Concrete.EncodingObservation
open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ canonicalEncodingInputs OtsEncodingMarker.markers
theorem lazyRun_neverFail {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (computation : OracleComp OracleWorld Result) (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (ha : ∀ row, (allowed row).Nonempty) : NeverFail (lazyRun parameter inputs hencoding outside computation allowed) := by
  apply UniformTableObservation.lazyRun_neverFail _ _ _ _ ha
  intro input
  exact ⟨probFailure_eq_zero (mx := fixedHashWorld (nonencodingAnswer parameter inputs hencoding outside) input)⟩
noncomputable def encodingCalls (parameter : PublicParameter) (trace : OtsContactTrace.Trace) : Nat :=
  QueryCap.calls (QueryClass.EncodingHash parameter) (trace.toList.map fun entry => .inr entry.1)
theorem encodingCalls_one (parameter : PublicParameter) : encodingCalls parameter 1 = 0 := rfl
theorem encodingCalls_step (parameter : PublicParameter) (input : OracleWorld.Domain) (answer : OracleWorld.Range input)
    (tail : OtsContactTrace.Trace) :
    encodingCalls parameter (hashObservationTrace input answer * tail) =
      (if QueryClass.EncodingHash parameter input then 1 else 0) + encodingCalls parameter tail := by
  cases input with
  | inl input => simp only [hashObservationTrace, one_mul, QueryClass.EncodingHash, if_false, Nat.zero_add]
  | inr input =>
      simp only [encodingCalls, hashObservationTrace, FreeMonoid.toList_mul, FreeMonoid.toList_of,
        List.singleton_append, List.map_cons, QueryCap.calls_cons]
theorem markers_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) (history : OtsContactTrace.Trace)
    (allowed : canonicalEncodingInputs parameter → Finset HashOutput)
    (hc : TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed)
    (ha : ∀ row, (allowed row).Nonempty) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) (history * result.1.2)).card : ENNReal)) ≤
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card : ENNReal) +
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation) allowed] *
            (encodingCalls parameter result.1.2 : ENNReal) := by
  simp only [lazyRun_eq_simulate]
  apply QueryPause.traced_spmf_potential_le hashObservationTrace (lazyWorldImpl parameter inputs hencoding outside)
    (fun history allowed => TraceConsistent parameter (referenceEncodingAllowed parameter messages selections) history allowed ∧
      ∀ row, (allowed row).Nonempty)
    _ _ (fun history _ => (OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) history).card)
    _ (encodingCalls parameter) _ (encodingCalls_one parameter) (encodingCalls_step parameter) _ computation history allowed ⟨hc, ha⟩
  · intro history allowed hi input result hr
    exact ⟨lazyWorldImpl_traceConsistent parameter inputs hencoding outside _ allowed history hi.1 input result hr,
      UniformTableObservation.lazyRun_nonempty (auxiliary parameter inputs hencoding outside) (translate parameter input)
        allowed hi.2 result hr⟩
  · intro computation history allowed hi
    rw [← lazyRun_eq_simulate]
    exact probFailure_eq_zero' (lazyRun_neverFail parameter inputs hencoding outside _ allowed hi.2)
  · intro history allowed hi input
    exact OtsEncodingMarker.markers_query_potential_le parameter inputs hencoding outside messages selections dummy history allowed hi.1 input
theorem markers_initial_lazyRun_le {Result : Type} (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (outside : NonencodingRows parameter inputs hencoding)
    (messages : EncodingPosition → Digest) (selections : ReferenceFamily) (dummy : OtsReferenceWords)
    (computation : OracleComp OracleWorld Result) :
    (∑' result, Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
      (referenceEncodingAllowed parameter messages selections)] *
      ((OtsEncodingMarker.markers parameter (referenceFamilyWords selections dummy) result.1.2).card : ENNReal)) ≤
        ((OtsCode.neighborBound : ENNReal) / (Fintype.card Digest : ENNReal)) * ∑' result,
          Pr[= result | lazyRun parameter inputs hencoding outside (QueryPause.traced hashObservationTrace computation)
            (referenceEncodingAllowed parameter messages selections)] * (encodingCalls parameter result.1.2 : ENNReal) := by
  simpa only [one_mul, OtsEncodingMarker.markers_one, Finset.card_empty, Nat.cast_zero, zero_add] using
    markers_lazyRun_le parameter inputs hencoding outside messages selections dummy computation 1 _
      (traceConsistent_one parameter _) (referenceEncodingAllowed_nonempty parameter messages selections)
end SphincsSecurity.Concrete.EncodingObservation
end
