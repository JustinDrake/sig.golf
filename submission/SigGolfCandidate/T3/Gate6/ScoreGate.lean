import SigGolfCandidate.T3.Gate6.BPORSPrefix
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp ENNReal
open SigGolfResearch.Gate6
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Regroup the exact raw layout so that all scoring coordinates precede the
independent ten-bit acceptance gate field and unused suffix. -/
def rawRecordViewEquiv : RawRecord ≃ RawView × (Padding × Unused) where
  toFun r := ((r.1.1,fun c => (r.1.2 c,r.2.1 c)),r.2.2)
  invFun r := ((r.1.1,fun c => (r.1.2 c).1),(fun c => (r.1.2 c).2,r.2))
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def gateCoordinatesEquiv : HashOutput ≃ RawView × (Padding × Unused) :=
  (Equiv.ofBijective digestRecord digestRecord_bijective).trans rawRecordViewEquiv

theorem gateCoordinates_view (output : HashOutput) :
    (gateCoordinatesEquiv output).1=rawView output := rfl

theorem gateCoordinates_gate (output : HashOutput) :
    digestGate output=true ↔ (gateCoordinatesEquiv output).2.1.val<135 := by
  change digestGate output=true ↔ (digestRecord output).2.2.1.val<135
  rw [digestGate,decide_eq_true_eq,digestRecord_gate_accept]

theorem finiteAverage_div {α : Type} [Fintype α] (f : α → ENNReal) (d : ENNReal) :
    BPORS.finiteAverage (fun x => f x/d)=BPORS.finiteAverage f/d := by
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem gate_card : (Finset.univ.filter fun gate : Padding => gate.val<135).card=135 := by
  first
  | simpa using (Fin.card_filter_val_lt (n := 1024) (m := 135))
  | decide
  | rfl

/-- An arbitrary nonnegative raw-coordinate payoff acquires precisely the
independent gate factor 135/1024 under a uniform hash output. -/
theorem average_gate_weight (payoff : RawView → ENNReal) :
    BPORS.finiteAverage (fun output : HashOutput =>
      if digestGate output=true then payoff (rawView output) else 0)=
        BPORS.finiteAverage payoff/(1024/135) := by
  have he (output : HashOutput) :
      (if digestGate output=true then payoff (rawView output) else 0)=
        (if (gateCoordinatesEquiv output).2.1.val<135 then payoff (gateCoordinatesEquiv output).1 else 0) := by
    simp only [gateCoordinates_view,gateCoordinates_gate]
  simp_rw [he]
  rw [BPORS.finiteAverage_equiv gateCoordinatesEquiv
    (fun p => if p.2.1.val<135 then payoff p.1 else 0),BPORS.finiteAverage_pair]
  have hi (view : RawView) : BPORS.finiteAverage
      (fun suffix : Padding × Unused => if suffix.1.val<135 then payoff view else 0)=
        payoff view/(1024/135) := by
    rw [BPORS.finiteAverage_pair]
    change BPORS.finiteAverage (fun gate : Padding =>
      BPORS.finiteAverage (fun _ : Unused => if gate.val<135 then payoff view else 0))=_
    simp_rw [BPORS.History.finiteAverage_constant]
    unfold BPORS.finiteAverage
    rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,gate_card,
      div_eq_mul_inv (payoff view) (1024/135 : ENNReal),
      ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    simp only [Padding,Fintype.card_fin,Nat.cast_ofNat,div_eq_mul_inv]
    ring
  simp_rw [hi]
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro view _
  ring

end SigGolfCandidate.T3.DigestSampling
