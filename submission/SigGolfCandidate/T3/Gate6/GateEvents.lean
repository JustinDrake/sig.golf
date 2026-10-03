import SigGolfCandidate.T3.Gate6.Coverage
namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

noncomputable def gatedEventEquiv (event : CoordinateDraw → Prop) :
    {draw : GatedDraw // draw.2=0 ∧ event draw.1} ≃
      {draw : CoordinateDraw // event draw} where
  toFun d := ⟨d.1.1,d.2.2⟩
  invFun d := ⟨(d.1,0),rfl,d.2⟩
  left_inv d := by apply Subtype.ext;exact Prod.ext rfl d.2.1.symm
  right_inv _ := rfl

/-- Every coordinate-only event, including a near-cover or a fixed-target
condition, receives the exact independent five-bit gate factor. -/
theorem gated_event_probability (event : CoordinateDraw → Prop) :
    Pr[fun draw : GatedDraw => draw.2=0 ∧ event draw.1 | ($ᵗ GatedDraw : ProbComp GatedDraw)] =
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/32 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (gatedEventEquiv event),
    probEvent_uniformSample,←Fintype.card_subtype]
  simp only [GatedDraw,Fintype.card_prod,Padding,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_ofNat]
  rw [div_div]

theorem digest_gated_event_probability (event : CoordinateDraw → Prop) :
    Pr[fun output => (digestRecord output).2.2.1=0 ∧
      event (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/32 := by
  rw [digest_event (fun raw => raw.2.2.1=0 ∧ event (rawDraw raw).1)]
  change Pr[fun raw => (rawDraw raw).2=0 ∧ event (rawDraw raw).1 | _]=_
  rw [raw_draw_event (fun draw => draw.2=0 ∧ event draw.1),gated_event_probability]

noncomputable def rawAtEventEquiv (index : Address) (event : GatedDraw → Prop) :
    {raw : RawRecord // raw.1.1=index ∧ event (rawDraw raw)} ≃
      {draw : GatedDraw // event draw} × Unused where
  toFun r := (⟨rawDraw r.1,r.2.2⟩,r.1.2.2.2)
  invFun r := ⟨((index,fun c => (r.1.1.1 c).1),
    (fun c => (r.1.1.1 c).2,(r.1.1.2,r.2))),rfl,r.1.2⟩
  left_inv r := by apply Subtype.ext;exact Prod.ext (Prod.ext r.2.1.symm rfl) rfl
  right_inv _ := rfl

theorem raw_at_draw_event (index : Address) (event : GatedDraw → Prop) :
    Pr[fun raw => raw.1.1=index ∧ event (rawDraw raw) | ($ᵗ RawRecord : ProbComp RawRecord)] =
      (Pr[event | ($ᵗ GatedDraw : ProbComp GatedDraw)])/2^31 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (rawAtEventEquiv index event),
    Fintype.card_prod,rawRecord_card,
    probEvent_uniformSample,←Fintype.card_subtype,gatedDraw_card]
  simp only [Unused,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num
  ring

theorem digest_at_gated_event_probability (index : Address) (event : CoordinateDraw → Prop) :
    Pr[fun output => (digestRecord output).1.1=index ∧
      (digestRecord output).2.2.1=0 ∧ event (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      ((Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/32)/2^31 := by
  rw [digest_event (fun raw => raw.1.1=index ∧ raw.2.2.1=0 ∧ event (rawDraw raw).1)]
  change Pr[fun raw => raw.1.1=index ∧ (rawDraw raw).2=0 ∧ event (rawDraw raw).1 | _]=_
  rw [raw_at_draw_event index (fun draw => draw.2=0 ∧ event draw.1),gated_event_probability]

end SigGolfResearch.Gate6
