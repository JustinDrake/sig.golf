import SigGolfCandidate.T3.Gate6.BPORSPrefix
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp ENNReal
open SigGolfResearch.Gate6
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Regroup the exact raw layout so that all scoring coordinates precede the
independent five-bit acceptance gate and unused suffix. -/
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
    digestGate output=true ↔ (gateCoordinatesEquiv output).2.1=0 := by
  change digestGate output=true ↔ (digestRecord output).2.2.1=0
  rw [digestGate,decide_eq_true_eq,digestRecord_gate_zero]

theorem finiteAverage_div {α : Type} [Fintype α] (f : α → ENNReal) (d : ENNReal) :
    BPORS.finiteAverage (fun x => f x/d)=BPORS.finiteAverage f/d := by
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- An arbitrary nonnegative raw-coordinate payoff acquires precisely the
independent five-bit gate factor under a uniform hash output. -/
theorem average_gate_weight (payoff : RawView → ENNReal) :
    BPORS.finiteAverage (fun output : HashOutput =>
      if digestGate output=true then payoff (rawView output) else 0)=
        BPORS.finiteAverage payoff/32 := by
  have he (output : HashOutput) :
      (if digestGate output=true then payoff (rawView output) else 0)=
        (if (gateCoordinatesEquiv output).2.1=0 then payoff (gateCoordinatesEquiv output).1 else 0) := by
    simp only [gateCoordinates_view,gateCoordinates_gate]
  simp_rw [he]
  rw [BPORS.finiteAverage_equiv gateCoordinatesEquiv
    (fun p => if p.2.1=0 then payoff p.1 else 0),BPORS.finiteAverage_pair]
  have hi (view : RawView) : BPORS.finiteAverage
      (fun suffix : Padding × Unused => if suffix.1=0 then payoff view else 0)=payoff view/32 := by
    rw [BPORS.finiteAverage_pair]
    change BPORS.finiteAverage (fun gate : Padding =>
      BPORS.finiteAverage (fun _ : Unused => if gate=0 then payoff view else 0))=_
    simp_rw [BPORS.History.finiteAverage_constant]
    unfold BPORS.finiteAverage
    simp [Padding]
  simp_rw [hi]
  unfold BPORS.finiteAverage
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro view _
  ring

end SigGolfCandidate.T3.DigestSampling
