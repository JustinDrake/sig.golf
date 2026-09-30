import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.ReferenceGraphContext
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferencePrimitiveWitness
namespace SphincsSecurity.Concrete.ReferenceStructuralMatch

open _root_.OracleComp OracleSpec CanonicalProbeRouting OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalPayloadInputs instFintypePosition

/-- A structural entry: a noncanonical canonical-graph query, above the frontier **or of a length other
than `48`** (so no OTS prefix row: the padded verifier's 80-byte chain inputs), whose answer is the honest
label of its position. -/
def Entry (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (input : HashInput) (answer : HashOutput) : Prop :=
  input ∈ canonicalGraphInputs key.parameter ∧ ∃ position,
    (ReferencePrimitiveWitness.AboveFrontier words position ∨ input.length ≠ 48) ∧ position.TreeBound ∧
    AtPosition key.parameter input position ∧ input ≠ canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels ∧
      truncateHash answer = truncateHash (labels position)

def Seen (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (trace : Trace) : Prop :=
  ∃ entry ∈ trace.toList, Entry key labels words entry.1 entry.2

theorem seen_one (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) :
    ¬Seen key labels words 1 := by simp [Seen]

theorem seen_of (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (entry : HashInput × HashOutput) :
    Seen key labels words (FreeMonoid.of entry) ↔ Entry key labels words entry.1 entry.2 := by simp [Seen]

theorem seen_mul (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (before after : Trace) :
    Seen key labels words (before * after) ↔ Seen key labels words before ∨ Seen key labels words after := by
  simp only [Seen, FreeMonoid.toList_mul, List.mem_append, or_and_right, exists_or]

/-- **A padded chain match is a (widened) structural entry** of the honest labels: the new event is
charged exactly like the record's structural matches. -/
theorem source_paddedMatch (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (trace : Trace) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (h : OtsVerifierWitness.PaddedChainMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace) :
    ∃ entry ∈ trace.toList,
      Entry key (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words entry.1 entry.2 := by
  obtain ⟨chainIdx, pad, previous, hpad, hrow, hhit⟩ := h
  let position : Position := .chain lay tree leaf chainIdx Position.lastChainStep
  have hbound : position.TreeBound := trivial
  have hcanonical := canonicalGraphInput_eq_honest key.parameter key.otsSecret key.ftsSecret f position
    (hbound.valid position) (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
    (fun child hc => congrArg truncateHash
      (canonicalGraphLabels_eq_honest key.parameter key.otsSecret key.ftsSecret f child (hbound.child hc)))
  refine ⟨_, hrow, paddedInput_mem_canonicalGraphInputs key.parameter lay tree leaf chainIdx _ pad previous,
    position, Or.inr ?_, hbound, ⟨_, rfl⟩, ?_, ?_⟩
  · rw [paddedInput_length key.parameter lay tree leaf chainIdx _ pad previous hpad]
    decide
  · rw [hcanonical]
    exact paddedInput_ne_honestInput key.parameter lay tree leaf chainIdx _ pad previous f key.otsSecret
      key.ftsSecret hpad
  · rw [canonicalGraphLabels_eq_honest key.parameter key.otsSecret key.ftsSecret f position hbound]
    change _ = honestValue f key.parameter key.otsSecret key.ftsSecret position
    rw [honestValue_chain]
    exact hhit

theorem source_match (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) (trace : Trace)
    (h : ReferencePrimitiveWitness.StructuralMatch key f words trace) :
    Seen key (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words trace := by
  rcases h with ⟨position, habove, hbound, payload, hpayload, hrow, hne, hvalue⟩ | ⟨lay, tree, leaf, hpad⟩
  · have hcanonical := canonicalGraphInput_eq_honest key.parameter key.otsSecret key.ftsSecret f position
      (hbound.valid position) (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)
      (fun child hc => congrArg truncateHash
        (canonicalGraphLabels_eq_honest key.parameter key.otsSecret key.ftsSecret f child (hbound.child hc)))
    refine ⟨_, hrow, graphInput_mem_of_payload key.parameter position payload hpayload, position, Or.inl habove, hbound,
      ⟨_, rfl⟩, ?_, ?_⟩
    · intro heq
      rw [hcanonical] at heq
      exact hne (tweakableHashInput_injective key.parameter position.domain_inRange position.domain_inRange heq).2
    · rw [canonicalGraphLabels_eq_honest key.parameter key.otsSecret key.ftsSecret f position hbound]
      exact hvalue
  · exact source_paddedMatch key f words trace lay tree leaf hpad

theorem Entry.noncanonical {key : SecretKey} {labels : CanonicalGraphLabels} {words : OtsReferenceWords}
    {input : HashInput} {answer : HashOutput} (h : Entry key labels words input answer) :
    ∀ position, input ≠ canonicalGraphInput key.parameter key.otsSecret key.ftsSecret position labels := by
  obtain ⟨_, position, _, _, hp, hn, _⟩ := h
  exact noncanonical_at key.parameter key.otsSecret key.ftsSecret labels input position hp hn

theorem Entry.otherHash {key : SecretKey} {labels : CanonicalGraphLabels} {words : OtsReferenceWords}
    {input : HashInput} {answer : HashOutput} (h : Entry key labels words input answer) :
    QueryClass.OtherHash key.parameter words (.inr input) := by
  obtain ⟨_, position, hshape, _, hp, _, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨payload, heq⟩
    have hd := (decodePosition_some_iff key.parameter input position).mpr hp
    rw [← heq, decodePosition_message] at hd
    contradiction
  · rintro ⟨encoding, he⟩
    exact he.not_atPosition position hp
  · intro address hs
    rcases hshape with habove | hlength
    · obtain ⟨query, hquery⟩ := Option.ne_none_iff_exists'.mp hs
      have hi := ((OtsPrefix.atAddress key.parameter words address).parse_some_iff input query).mp hquery
      have heq := atPosition_unique key.parameter hp
        (show AtPosition key.parameter input (.chain address.1 address.2.1 address.2.2.1 address.2.2.2
          ((OtsPrefix.atAddress key.parameter words address).step query.1)) from ⟨_, hi⟩)
      subst position
      change (words address.1 address.2.1 address.2.2.1 address.2.2.2).val ≤ query.1.val at habove
      exact Nat.not_lt_of_ge habove query.1.isLt
    · exact hs (parse_eq_none_of_length hlength)

theorem entry_uniform_le (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (input : HashInput) :
    Pr[Entry key labels words input | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ := by
  by_cases hp : ∃ position, AtPosition key.parameter input position
  · obtain ⟨position, hp⟩ := hp
    calc
      _ ≤ Pr[fun answer => truncateHash answer = truncateHash (labels position) |
          (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] := by
        apply _root_.probEvent_mono
        rintro answer _ ⟨_, other, _, _, ho, _, he⟩
        obtain rfl := atPosition_unique key.parameter ho hp
        exact he
      _ = _ := HiddenLabelProbe.prob_truncate_eq _
  · have hz : Pr[Entry key labels words input | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 := by
      apply probEvent_eq_zero
      rintro answer _ ⟨_, position, _, _, hi, _⟩
      exact hp ⟨position, hi⟩
    rw [hz]
    exact bot_le

theorem entry_uniform_other_le (key : SecretKey) (labels : CanonicalGraphLabels) (words : OtsReferenceWords) (input : HashInput) :
    Pr[Entry key labels words input | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] ≤
      (Fintype.card Digest : ENNReal)⁻¹ * ((if QueryClass.OtherHash key.parameter words (.inr input) then 1 else 0 : Nat) : ENNReal) := by
  by_cases ho : QueryClass.OtherHash key.parameter words (.inr input)
  · simpa only [if_pos ho, Nat.cast_one, mul_one] using entry_uniform_le key labels words input
  · have hz : Pr[Entry key labels words input | (liftM (PMF.uniformOfFintype HashOutput) : SPMF HashOutput)] = 0 :=
      probEvent_eq_zero fun _ _ h => ho h.otherHash
    rw [hz]
    exact bot_le

end SphincsSecurity.Concrete.ReferenceStructuralMatch
