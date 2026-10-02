import SigGolfCandidate.T3.Gate6.MomentNumeric
namespace SigGolfResearch.Gate6
open OracleComp ENNReal Finset
open Moments
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

abbrev CoordinateDraw := Bank → Bucket × Triple
abbrev GatedDraw := CoordinateDraw × Padding

def rawDraw (raw : RawRecord) : GatedDraw :=
  ((fun c => (raw.1.2 c,raw.2.1 c)),raw.2.2.1)

noncomputable def rawEventEquiv (event : GatedDraw → Prop) :
    {raw : RawRecord // event (rawDraw raw)} ≃
      Address × ({draw : GatedDraw // event draw} × Unused) where
  toFun r := (r.1.1.1,(⟨rawDraw r.1,r.2⟩,r.1.2.2.2))
  invFun r := ⟨((r.1,fun c => (r.2.1.1.1 c).1),
    (fun c => (r.2.1.1.1 c).2,(r.2.1.1.2,r.2.2))),r.2.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem gatedDraw_card : Fintype.card GatedDraw=2^181 := by
  norm_num [GatedDraw,CoordinateDraw,Bank,Bucket,Triple,Padding,
    Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]

theorem raw_draw_event (event : GatedDraw → Prop) :
    Pr[fun raw => event (rawDraw raw) | ($ᵗ RawRecord : ProbComp RawRecord)] =
      Pr[event | ($ᵗ GatedDraw : ProbComp GatedDraw)] := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (rawEventEquiv event),
    Fintype.card_prod,Fintype.card_prod,rawRecord_card,
    probEvent_uniformSample,←Fintype.card_subtype,gatedDraw_card]
  simp only [Address,Unused,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num
  ring

def CoordinateCovered (exposed : Bank → Bucket → Finset (Fin 128))
    (draw : CoordinateDraw) : Prop := ∀ c, Covered (exposed c (draw c).1) (draw c).2

def GatedCovered (exposed : Bank → Bucket → Finset (Fin 128)) (draw : GatedDraw) : Prop :=
  draw.2=0 ∧ CoordinateCovered exposed draw.1

noncomputable def gatedCoveredEquiv (exposed : Bank → Bucket → Finset (Fin 128)) :
    {draw : GatedDraw // GatedCovered exposed draw} ≃
      {draw : CoordinateDraw // CoordinateCovered exposed draw} where
  toFun d := ⟨d.1.1,d.2.2⟩
  invFun d := ⟨(d.1,0),rfl,d.2⟩
  left_inv d := by apply Subtype.ext;exact Prod.ext rfl d.2.1.symm
  right_inv _ := rfl

theorem gated_covered_probability (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[GatedCovered exposed | ($ᵗ GatedDraw : ProbComp GatedDraw)] =
      (Pr[CoordinateCovered exposed | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/64 := by
  rw [probEvent_uniformSample,←Fintype.card_subtype,Fintype.card_congr (gatedCoveredEquiv exposed),
    probEvent_uniformSample,←Fintype.card_subtype]
  simp only [GatedDraw,Fintype.card_prod,Padding,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_ofNat]
  rw [div_div]

/-- The six-bit gate gives exactly its full factor in the fixed-exposure
coverage probability; no independence premise about chosen histories is used. -/
theorem digest_gate_covered_probability (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[fun output => GatedCovered exposed (rawDraw (digestRecord output)) |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (∏ c : Bank, ((∑ b : Bucket, ((exposed c b).card.descFactorial 3 : ENNReal))/(16*128^3)))/64 := by
  rw [digest_event (fun raw => GatedCovered exposed (rawDraw raw)),raw_draw_event,
    gated_covered_probability]
  exact congrArg (fun p : ENNReal => p/64) (bpors_covered_probability exposed)

/-- The actual acceptance predicate implies the independent gate condition.
Keeping the authentication cap can only reduce this fixed-exposure event. -/
theorem accepted_covered_le_gate (exposed : Bank → Bucket → Finset (Fin 128)) :
    Pr[fun output => DigestAccepted output ∧
      CoordinateCovered exposed (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
    Pr[fun output => GatedCovered exposed (rawDraw (digestRecord output)) |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  apply probEvent_mono
  intro output _ h
  exact ⟨h.1.1,h.2⟩


/-- The actual accepted, exposed digest event is bounded by the gated
forest potential whose finite-history moments are certified in MomentNumeric. -/
theorem accepted_covered_le_forestEnvelope {steps : Nat}
    (table : Fin 7 → Fin steps → Fin 16) (exposed : Bank → Bucket → Finset (Fin 128))
    (hsize : ∀ c bucket, (exposed c bucket).card ≤ 3*(List.ofFn (table c)).count bucket) :
    Pr[fun output => DigestAccepted output ∧
      CoordinateCovered exposed (rawDraw (digestRecord output)).1 |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ Moments.Numeric.forestEnvelope table := by
  refine (accepted_covered_le_gate exposed).trans ?_
  rw [digest_gate_covered_probability]
  have he : (∏ c : Bank,
      ((∑ bucket : Bucket, ((3*(List.ofFn (table c)).count bucket).descFactorial 3 : ENNReal))/(16*128^3)))/64 =
      Moments.Numeric.forestEnvelope table := by
    simp only [Moments.Numeric.forestEnvelope,coordinateEnvelope,bucketMass,div_eq_mul_inv,
      Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Bank,Fintype.card_fin]
    rw [mul_assoc,mul_assoc]
    congr 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_mul]
  rw [←he]
  apply ENNReal.div_le_div_right
  gcongr with c hc bucket hb
  exact hsize c bucket

end SigGolfResearch.Gate6
