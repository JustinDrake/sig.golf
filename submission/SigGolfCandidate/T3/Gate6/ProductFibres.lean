import Mathlib.Tactic
import SigGolfCandidate.Budget.Octopus.Tuples
import VCVio.OracleComp.Constructions.SampleableType

section



namespace SigGolfResearch.Gate6
open SigGolfCandidate.Budget.Octopus Finset
set_option maxHeartbeats 3000000
abbrev Address := Fin (2^31)
abbrev Bank := Fin 7
abbrev Bucket := Fin 16
abbrev MarkedLabel := Address × (Bank → Bucket)
theorem markedLabel_card : Fintype.card MarkedLabel = 2^59 := by
  norm_num [MarkedLabel,Address,Bank,Bucket,Fintype.card_prod,Fintype.card_fun]
abbrev Triple := Fin 3 → Fin 128
abbrev Slots := Bank → Triple
abbrev Padding := Fin 8
abbrev Unused := Fin (2^47)
abbrev Payload := Slots × (Padding × Unused)
abbrev RawRecord := MarkedLabel × Payload
def slotSet (v : Triple) : Finset Nat := (valList v).toFinset
def childAuth (v : Triple) : Nat := octH 7 (slotSet v).sort
def SlotsAccepted (slots : Slots) : Prop :=
  (∀ bank, Function.Injective (slots bank)) ∧ (∑ bank, childAuth (slots bank)) ≤ 87
def PayloadAccepted (payload : Payload) : Prop :=
  payload.2.1 = 0 ∧ SlotsAccepted payload.1
def Accepted (raw : RawRecord) : Prop := PayloadAccepted raw.2
noncomputable instance : DecidablePred SlotsAccepted := Classical.decPred _
noncomputable instance : DecidablePred PayloadAccepted := Classical.decPred _
noncomputable instance : DecidablePred Accepted := Classical.decPred _
theorem rawRecord_card : Fintype.card RawRecord = 2^256 := by
  norm_num [RawRecord,Payload,Slots,Triple,Padding,Unused,MarkedLabel,Address,Bank,Bucket,
    Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
theorem payload_card : Fintype.card Payload = 2^197 := by
  norm_num [Payload,Slots,Triple,Padding,Unused,Bank,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
def witnessTriple : Triple := fun i => ⟨i.val,by omega⟩
theorem witness_injective : Function.Injective witnessTriple := by
  intro a b h
  exact Fin.ext (show a.val=b.val from congrArg (fun x : Fin 128 => x.val) h)
theorem witness_auth : childAuth witnessTriple = 6 := by
  unfold childAuth slotSet
  rw [← sortLeaves_eq ((valList_nodup _).mpr witness_injective)]
  decide
theorem accepted_witness : Accepted ((0,fun _ => 0),((fun _ => witnessTriple),(0,0))) := by
  refine ⟨rfl,fun _ => witness_injective,?_⟩
  simp only [witness_auth,sum_const,Fintype.card_fin,Bank,smul_eq_mul]
  norm_num
instance : Nonempty {r : RawRecord // Accepted r} :=
  ⟨⟨_,accepted_witness⟩⟩
instance : Nonempty {p : Payload // PayloadAccepted p} :=
  ⟨⟨_,accepted_witness⟩⟩
end SigGolfResearch.Gate6
#print axioms SigGolfResearch.Gate6.rawRecord_card
#print axioms SigGolfResearch.Gate6.accepted_witness
end

section

namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
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
    Fintype.card {s : Slots // SlotsAccepted s} * 2^47 := by
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
end
