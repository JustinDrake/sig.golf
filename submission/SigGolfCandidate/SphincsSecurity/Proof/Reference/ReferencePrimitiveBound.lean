import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.StructuralMatchBound
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMatchBound
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsDistinctContactBound
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsMarkerContactProbability
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsContactFirstProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs canonicalGraphLabels Finset.univ

theorem referenceGraphContextGame_encoding {Result : Type} (observer : FrontierObserver Result)
    (inputs : Finset HashInput) (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) :
    (fun result : GraphContextResult Result => (result.1.parameter, result.2.2.1, canonicalGraphMessage result.2.1, result.2.2.2)) <$>
      referenceGraphContextGame observer inputs hencoding dummy adversary =
        referenceEncodingContextGame observer inputs hencoding dummy adversary := by
  simp only [referenceGraphContextGame, referenceGraphContextRest, referenceEncodingContextGame, referenceEncodingContextRest,
    map_bind, map_pure, bind_assoc, pure_bind]

theorem referenceGraphContextGame_contact_event (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (dummy : OtsReferenceWords) (adversary : Adversary)
    (event : InstrumentedResult ContactResult → Prop) :
    Pr[fun result => event (result.1.parameter, result.2.2.1, result.2.2.2) |
      referenceGraphContextGame contactObserver inputs hencoding dummy adversary] =
        Pr[event | referenceContactGame inputs hencoding dummy adversary] := by
  rw [referenceContactGame, ← referenceGraphContextGame_erased contactObserver inputs hencoding dummy adversary, probEvent_map]
  rfl

def GraphPrimitiveEvent (dummy : OtsReferenceWords) (result : GraphContextResult ContactResult) : Prop :=
  let words := referenceFamilyWords result.2.2.1 dummy
  let trace := result.2.2.2.before * result.2.2.2.after
  OtsVerifierWitness.EncodingOutputMatch result.1.parameter words (canonicalGraphMessage result.2.1) result.2.2.1 trace ∨
    ReferenceStructuralMatch.Seen result.1 result.2.1 words trace ∨
      result.2.2.2.TwoEdge result.1.parameter words ∨ result.2.2.2.TwoContacts result.1.parameter words ∨
        result.2.2.2.MarkerContact result.1.parameter words

theorem graphPrimitiveEvent_of_outcome (key : SecretKey) (f : QueryImpl HashSpec Id) (selections : ReferenceFamily)
    (dummy : OtsReferenceWords) (result : ContactResult)
    (h : ReferencePrimitiveWitness.Outcome key f (referenceFamilyWords selections dummy)
      (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) selections result) :
    GraphPrimitiveEvent dummy (key, canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f, selections, result) := by
  rcases h with hencoding | hstructural | htwo | hdistinct | hmarker
  · exact Or.inl hencoding
  · exact Or.inr (Or.inl (ReferenceStructuralMatch.source_match key f _ _ hstructural))
  · exact Or.inr (Or.inr (Or.inl htwo))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hdistinct)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmarker)))

noncomputable def rawPrimitivePrefixRate (q : Nat) : ENNReal :=
  let n : ENNReal := Fintype.card Digest
  let x := (q : ENNReal) / n
  prefixTwoEdgeRate q / (1 - x) + (4 * x) / ((1 - x)^2 * n) + ((2 * ((63 / 32 : ENNReal) * (OtsCode.unitNeighborBound : ENNReal))) * x) / ((1 - x) * n)

noncomputable def rawPrimitiveEncodingRate (q : Nat) : ENNReal :=
  let n : ENNReal := Fintype.card Digest
  let x := (q : ENNReal) / n
  (63 / 32 : ENNReal) * n⁻¹ + ((2 * ((63 / 32 : ENNReal) * (OtsCode.neighborBound : ENNReal))) * x) / ((1 - x) * n)

/-- The contact union is charged once, rather than separately for each witness. -/
noncomputable def coarsePrimitivePrefixRate (q : Nat) : ENNReal :=
  (2 / Fintype.card Digest) / (1 - (q : ENNReal) / Fintype.card Digest)

/-- Mix one part of the fine bound with fifteen parts of the contact-union bound. -/
noncomputable def primitivePrefixRate (q : Nat) : ENNReal :=
  (1 / 16 : ENNReal) * rawPrimitivePrefixRate q +
    (15 / 16 : ENNReal) * coarsePrimitivePrefixRate q

noncomputable def primitiveEncodingRate (q : Nat) : ENNReal :=
  (1 / 16 : ENNReal) * rawPrimitiveEncodingRate q +
    (15 / 16 : ENNReal) * ((63 / 32 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹)

theorem primitivePrefixRate_mono {q r : Nat} (h : q ≤ r) : primitivePrefixRate q ≤ primitivePrefixRate r := by
  dsimp only [primitivePrefixRate, rawPrimitivePrefixRate, coarsePrimitivePrefixRate, prefixTwoEdgeRate]
  gcongr

theorem primitiveEncodingRate_mono {q r : Nat} (h : q ≤ r) : primitiveEncodingRate q ≤ primitiveEncodingRate r := by
  dsimp only [primitiveEncodingRate, rawPrimitiveEncodingRate]
  gcongr

theorem primitive_rates_small (q : Nat) (hq : q ≤ budgetSplit) :
    primitivePrefixRate q ≤ primitiveCoefficient / Fintype.card Digest ∧
      primitiveEncodingRate q ≤ primitiveCoefficient / Fintype.card Digest := by
  rw [budgetSplit_def] at hq
  rw [primitiveCoefficient_def]
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hn : (Fintype.card Digest : ENNReal) ≠ 0 := by positivity
  have hx : (((65 * 2 ^ 106) : Nat) : ENNReal) / Fintype.card Digest < 1 := by
    rw [ENNReal.div_lt_iff (Or.inl hn) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast (show (65 * 2 ^ 106) < Fintype.card Digest by rw [hcard]; norm_num)
  have hd : 1 - (((65 * 2 ^ 106) : Nat) : ENNReal) / Fintype.card Digest ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hx)
  have hs := ENNReal.toReal_sub_of_le hx.le (show (1 : ENNReal) ≠ ⊤ by finiteness)
  constructor
  · apply (primitivePrefixRate_mono hq).trans
    dsimp only [primitivePrefixRate, rawPrimitivePrefixRate, coarsePrimitivePrefixRate, prefixTwoEdgeRate]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, hcard, OtsCode.unitNeighborBound_eq]
  · apply (primitiveEncodingRate_mono hq).trans
    dsimp only [primitiveEncodingRate, rawPrimitiveEncodingRate]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    repeat rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv, hs,
      ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.toReal_one]
    norm_num [hcard, OtsCode.neighborBound_eq]

private theorem primitive_marker_rate_mono {a b s t x den P E : ENNReal} (h : a ≤ b) :
    ((2 * (a * s)) * x * P + (2 * (a * t)) * x * E) / den ≤
      ((2 * (b * s)) * x * P + (2 * (b * t)) * x * E) / den := by
  gcongr

theorem referenceGraphContextGame_primitive_raw_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hprefix : PrefixBudget dummy adversary q) (hcontact : ContactBudget dummy adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      rawPrimitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) +
      rawPrimitiveEncodingRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal)) +
      (Fintype.card Digest : ENNReal)⁻¹ * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal)) := by
  let law := referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have he := referenceEncodingContextGame_match_le_encodingCost dummy adversary
  replace he := he.trans (mul_le_mul' (mul_le_mul' (show _ ≤ (63 / 32 : ENNReal) from by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]) le_rfl) le_rfl)
  rw [← referenceGraphContextGame_encoding contactObserver _ _ dummy adversary, probEvent_map] at he
  have hs := referenceGraphContextGame_match_le_otherCost dummy adversary
  have ht := referenceContactGame_twoEdge_le dummy adversary q hprefix hsmall
  have hd := referenceContactGame_distinct_le dummy adversary q hprefix hcontact hsmall
  have hm := referenceContactGame_markerContact_le dummy adversary q hprefix hcontact hsmall
  replace hm := hm.trans (primitive_marker_rate_mono (show _ ≤ (63 / 32 : ENNReal) from by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]))
  rw [← referenceGraphContextGame_contact_event _ _ dummy adversary] at ht hd hm
  have h := (probEvent_or_le law _ _).trans (add_le_add he
    ((probEvent_or_le law _ _).trans (add_le_add hs
      ((probEvent_or_le law _ _).trans (add_le_add ht
        ((probEvent_or_le law _ _).trans (add_le_add hd hm)))))))
  change Pr[GraphPrimitiveEvent dummy | law] ≤ _ at h
  refine h.trans_eq ?_
  simp only [rawPrimitivePrefixRate, rawPrimitiveEncodingRate, div_eq_mul_inv]
  ring

private theorem primitiveContact_card_pos (parameter : PublicParameter) (words : OtsReferenceWords)
    (result : ContactResult)
    (h : result.TwoEdge parameter words ∨ result.TwoContacts parameter words ∨ result.MarkerContact parameter words) :
    0 < (OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)).card := by
  rcases h with htwo | hdistinct | hmarker
  · obtain ⟨address, first, last, _, hlast, _, entry, hentry, hparse, hanswer⟩ := htwo
    apply Finset.card_pos.mpr
    refine ⟨address, (OtsContactTrace.mem_contacts _ _ _ _ _).mpr ?_⟩
    exact ⟨entry, hentry, last, hparse, hlast, hanswer⟩
  · change 2 ≤ (OtsContactTrace.contacts parameter words result.frontier (result.before * result.after)).card at hdistinct
    omega
  · obtain ⟨address, _, hcontact⟩ := hmarker
    exact Finset.card_pos.mpr ⟨address, hcontact⟩

theorem referenceContactGame_primitiveContact_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hprefix : PrefixBudget dummy adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) ∨
      result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) ∨
      result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      coarsePrimitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) := by
  have hcount : Pr[fun result => result.2.2.TwoEdge result.1 (referenceFamilyWords result.2.1 dummy) ∨
      result.2.2.TwoContacts result.1 (referenceFamilyWords result.2.1 dummy) ∨
      result.2.2.MarkerContact result.1 (referenceFamilyWords result.2.1 dummy) |
        referenceContactGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      ∑' result, Pr[= result | referenceContactGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] *
          ((OtsContactTrace.contacts result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.frontier
            (result.2.2.before * result.2.2.after)).card : ENNReal) := by
    rw [probEvent_eq_tsum_ite]
    apply ENNReal.tsum_le_tsum
    intro result
    split
    · rename_i he
      have hp := primitiveContact_card_pos _ _ _ he
      exact (mul_one _).symm.trans_le (mul_le_mul' le_rfl (by exact_mod_cast Nat.succ_le_iff.mpr hp))
    · exact bot_le
  have hscaled := (mul_le_mul' (le_refl (1 - (q : ENNReal) / Fintype.card Digest)) hcount).trans
    (referenceContactGame_contacts_cost_le dummy adversary q hprefix hsmall)
  have hcard : (Fintype.card Digest : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hpositive : 0 < 1 - (q : ENNReal) / Fintype.card Digest := by
    apply tsub_pos_iff_lt.mpr
    rw [ENNReal.div_lt_iff (Or.inl hcard) (Or.inl (by finiteness)), one_mul]
    exact_mod_cast hsmall
  calc
    _ ≤ ((2 / Fintype.card Digest) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal))) /
        (1 - (q : ENNReal) / Fintype.card Digest) := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hpositive)) (Or.inl (by finiteness))).mpr
      simpa only [mul_comm] using hscaled
    _ = _ := by
      simp only [coarsePrimitivePrefixRate, div_eq_mul_inv]
      ring

theorem referenceGraphContextGame_primitive_coarse_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hprefix : PrefixBudget dummy adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      coarsePrimitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) +
      ((63 / 32 : ENNReal) * (Fintype.card Digest : ENNReal)⁻¹) * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal)) +
      (Fintype.card Digest : ENNReal)⁻¹ * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal)) := by
  let law := referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have he := referenceEncodingContextGame_match_le_encodingCost dummy adversary
  replace he := he.trans (mul_le_mul' (mul_le_mul' (show _ ≤ (63 / 32 : ENNReal) from by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]) le_rfl) le_rfl)
  rw [← referenceGraphContextGame_encoding contactObserver _ _ dummy adversary, probEvent_map] at he
  have hs := referenceGraphContextGame_match_le_otherCost dummy adversary
  have hc := referenceContactGame_primitiveContact_le dummy adversary q hprefix hsmall
  rw [← referenceGraphContextGame_contact_event _ _ dummy adversary] at hc
  have h := (probEvent_or_le law _ _).trans (add_le_add he
    ((probEvent_or_le law _ _).trans (add_le_add hs hc)))
  change Pr[GraphPrimitiveEvent dummy | law] ≤ _ at h
  exact h.trans_eq (by ring)

private theorem primitive_mixture {p a b c d o P E O : ENNReal}
    (hfine : p ≤ a * P + b * E + o * O) (hcoarse : p ≤ c * P + d * E + o * O) :
    p ≤ ((1 / 16 : ENNReal) * a + (15 / 16 : ENNReal) * c) * P +
      ((1 / 16 : ENNReal) * b + (15 / 16 : ENNReal) * d) * E + o * O := by
  have hweights : (1 / 16 : ENNReal) + (15 / 16 : ENNReal) = 1 := by
    rw [ENNReal.div_add_div_same, show (1 : ENNReal) + 15 = 16 by norm_num]
    exact ENNReal.div_self (by norm_num) (by finiteness)
  calc
    p = (1 / 16 : ENNReal) * p + (15 / 16 : ENNReal) * p := by
      rw [← add_mul, hweights, one_mul]
    _ ≤ (1 / 16 : ENNReal) * (a * P + b * E + o * O) +
        (15 / 16 : ENNReal) * (c * P + d * E + o * O) :=
      add_le_add (mul_le_mul' le_rfl hfine) (mul_le_mul' le_rfl hcoarse)
    _ = ((1 / 16 : ENNReal) * a + (15 / 16 : ENNReal) * c) * P +
        ((1 / 16 : ENNReal) * b + (15 / 16 : ENNReal) * d) * E +
        ((1 / 16 : ENNReal) + (15 / 16 : ENNReal)) * (o * O) := by ring
    _ = _ := by rw [hweights, one_mul]

theorem referenceGraphContextGame_primitive_le (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hprefix : PrefixBudget dummy adversary q) (hcontact : ContactBudget dummy adversary q) (hsmall : q < Fintype.card Digest) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] ≤
      primitivePrefixRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.prefixCalls dummy : ENNReal)) +
      primitiveEncodingRate q * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.encodingCalls : ENNReal)) +
      (Fintype.card Digest : ENNReal)⁻¹ * (∑' result,
        Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.otherCalls dummy : ENNReal)) := by
  exact primitive_mixture (referenceGraphContextGame_primitive_raw_le dummy adversary q hprefix hcontact hsmall)
    (referenceGraphContextGame_primitive_coarse_le dummy adversary q hprefix hsmall)

theorem referenceGraphContextGame_primitive_joint_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q < Fintype.card Digest)
    (rate : ENNReal) (hp : primitivePrefixRate q ≤ rate) (he : primitiveEncodingRate q ≤ rate)
    (ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ rate) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      rate * (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) ≤ rate * q := by
  let law := referenceRecordedGame (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary
  have h := add_le_add (referenceGraphContextGame_primitive_le dummy adversary q (prefixBudget_of_hasHashQueryBound dummy adversary q hbound)
    (contactBudget_of_hasHashQueryBound dummy adversary q hbound) hsmall)
    (le_refl (rate * ∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)))
  refine h.trans ?_
  calc
    _ ≤ rate * (∑' result, Pr[= result | law] * (result.prefixCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.encodingCalls : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.otherCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' hp le_rfl) (mul_le_mul' he le_rfl)) (mul_le_mul' ho le_rfl)) le_rfl
    _ = rate * ∑' result, Pr[= result | law] * ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal) := by
      simp only [ReferenceRecordedResult.remainingCalls, Nat.cast_add, mul_add, ENNReal.tsum_add, add_assoc]
    _ ≤ rate * q := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∑' result, Pr[= result | law] * (q : ENNReal) := by
          apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : result ∈ support law
          · exact mul_le_mul' le_rfl (Nat.cast_le.mpr (referenceRecordedGame_joint_budget dummy adversary q hbound result hr))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ q := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem referenceGraphContextGame_primitive_small_budget (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (hsmall : q ≤ budgetSplit) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] +
      (primitiveCoefficient / Fintype.card Digest) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * (result.messageCalls : ENNReal)) ≤
        primitiveCoefficient * ((q : ENNReal) / Fintype.card Digest) := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hq : q < Fintype.card Digest := hsmall.trans_lt (budgetSplit_le.trans_lt (by rw [hcard]; norm_num))
  have hr := primitive_rates_small q hsmall
  have ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ primitiveCoefficient / Fintype.card Digest := by
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div, hcard]
  simpa only [div_eq_mul_inv, mul_right_comm, mul_assoc] using
    referenceGraphContextGame_primitive_joint_budget dummy adversary q hbound hq _ hr.1 hr.2 ho

end SphincsSecurity.Concrete
