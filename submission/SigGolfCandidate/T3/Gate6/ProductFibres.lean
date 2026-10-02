import SigGolfCandidate.T3.Gate6.FreshDefs
namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000

/-- Acceptance tests only the actual payload: the entire 59-bit mark is free. -/
noncomputable def acceptedEquiv : {r : RawRecord // Accepted r} ≃
    MarkedLabel × {p : Payload // PayloadAccepted p} where
  toFun r := (r.1.1,⟨r.1.2,r.2⟩)
  invFun x := ⟨(x.1,x.2.1),x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def markFibreEquiv (mark : MarkedLabel) :
    {r : RawRecord // Accepted r ∧ r.1=mark} ≃ {p : Payload // PayloadAccepted p} where
  toFun r := ⟨r.1.2,r.2.1⟩
  invFun p := ⟨(mark,p.1),p.2,rfl⟩
  left_inv r := by apply Subtype.ext; exact Prod.ext r.2.2.symm rfl
  right_inv _ := rfl

noncomputable def payloadEquiv : {p : Payload // PayloadAccepted p} ≃
    {s : Slots // SlotsAccepted s} × Unused where
  toFun p := (⟨p.1.1,p.2.2⟩,p.1.2.2)
  invFun x := ⟨(x.1.1,(0,x.2)),rfl,x.1.2⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext p.2.1.symm rfl)
  right_inv _ := rfl

theorem accepted_card : Fintype.card {r : RawRecord // Accepted r} =
    2^59 * Fintype.card {p : Payload // PayloadAccepted p} := by
  rw [Fintype.card_congr acceptedEquiv,Fintype.card_prod,markedLabel_card]

theorem fibre_card (mark : MarkedLabel) :
    Fintype.card {r : RawRecord // Accepted r ∧ r.1=mark} =
      Fintype.card {p : Payload // PayloadAccepted p} := Fintype.card_congr (markFibreEquiv mark)

theorem payload_accepted_card : Fintype.card {p : Payload // PayloadAccepted p} =
    Fintype.card {s : Slots // SlotsAccepted s} * 2^44 := by
  rw [Fintype.card_congr payloadEquiv,Fintype.card_prod]
  simp only [Unused,Fintype.card_fin]

theorem fresh_acceptance : Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] =
    (Fintype.card {p : Payload // PayloadAccepted p} : ENNReal) / 2^197 := by
  rw [probEvent_uniformSample,← Fintype.card_subtype,accepted_card,rawRecord_card,Nat.cast_mul]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [show (2 : ENNReal)^256=2^59*2^197 by rw [← pow_add]]
  exact ENNReal.mul_div_mul_left _ _ (by positivity) (by finiteness)

theorem fresh_mark_joint (mark : MarkedLabel) :
    Pr[fun r => Accepted r ∧ r.1=mark | ($ᵗ RawRecord : ProbComp RawRecord)] =
      Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] / 2^59 := by
  rw [probEvent_uniformSample,← Fintype.card_subtype,fibre_card,rawRecord_card,fresh_acceptance]
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  simp only [div_eq_mul_inv]
  rw [show (2 : ENNReal)^256=2^197*2^59 by rw [← pow_add],
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness)),mul_assoc]

/-- The fresh full mark is exactly uniform conditional on the actual
six-zero-bit, distinct-triple and summed-authentication-cap predicate. -/
theorem fresh_mark_conditional (mark : MarkedLabel) :
    Pr[fun r => Accepted r ∧ r.1=mark | ($ᵗ RawRecord : ProbComp RawRecord)] /
      Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] = (2^59 : ENNReal)⁻¹ := by
  rw [fresh_mark_joint]
  have hp : Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] ≠ 0 := by
    rw [fresh_acceptance]
    exact ENNReal.div_ne_zero.mpr ⟨by exact_mod_cast Fintype.card_ne_zero,by finiteness⟩
  rw [div_eq_mul_inv,div_eq_mul_inv]
  calc
    _ = (Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)] *
        (Pr[Accepted | ($ᵗ RawRecord : ProbComp RawRecord)])⁻¹) * (2^59 : ENNReal)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hp probEvent_ne_top,one_mul]

end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.fresh_mark_conditional
