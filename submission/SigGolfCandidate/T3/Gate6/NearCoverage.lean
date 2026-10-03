import SigGolfCandidate.T3.Gate6.Coverage
import SigGolfCandidate.T3.Gate6.BPORSPrefix

section

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
theorem gated_event_probability (event : CoordinateDraw → Prop) :
    Pr[fun draw : GatedDraw => draw.2=0 ∧ event draw.1 | ($ᵗ GatedDraw : ProbComp GatedDraw)] =
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8 := by
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
      (Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8 := by
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
      ((Pr[event | ($ᵗ CoordinateDraw : ProbComp CoordinateDraw)])/8)/2^31 := by
  rw [digest_event (fun raw => raw.1.1=index ∧ raw.2.2.1=0 ∧ event (rawDraw raw).1)]
  change Pr[fun raw => raw.1.1=index ∧ (rawDraw raw).2=0 ∧ event (rawDraw raw).1 | _]=_
  rw [raw_at_draw_event index (fun draw => draw.2=0 ∧ event draw.1),gated_event_probability]
end SigGolfResearch.Gate6
end

section


namespace SigGolfCandidate.T3.BPORS
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def OmitCovered (exposed : Finset (Fin 128)) (omitted : Fin 3)
    (draw : Fin 3 → Fin 128) : Prop := Covered exposed (omitted.removeNth draw)
theorem omitCovered_of_all_but (exposed : Finset (Fin 128)) (omitted : Fin 3)
    (draw : Fin 3 → Fin 128) (hinj : Function.Injective draw)
    (hcovered : ∀ slot, slot ≠ omitted → draw slot ∈ exposed) :
    OmitCovered exposed omitted draw := by
  refine ⟨hinj.comp Fin.succAbove_right_injective, ?_⟩
  intro slot
  exact hcovered (omitted.succAbove slot) (Fin.succAbove_ne omitted slot)
noncomputable def omitCoveredEquiv (exposed : Finset (Fin 128)) (omitted : Fin 3) :
    {draw : Fin 3 → Fin 128 // OmitCovered exposed omitted draw} ≃
      ({draw : Fin 2 → Fin 128 // Covered exposed draw} × Fin 128) where
  toFun draw := (⟨omitted.removeNth draw.1, draw.2⟩, draw.1 omitted)
  invFun draw := ⟨omitted.insertNth draw.2 draw.1.1, by
    simpa only [OmitCovered, Fin.removeNth_insertNth] using draw.1.2⟩
  left_inv draw := by
    apply Subtype.ext
    exact Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  right_inv draw := by
    apply Prod.ext
    · apply Subtype.ext
      dsimp only
      exact Fin.removeNth_insertNth (α := fun _ : Fin 3 => Fin 128) omitted draw.2 draw.1.1
    · dsimp only
      exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => Fin 128) omitted draw.2 draw.1.1
theorem omitCovered_count (exposed : Finset (Fin 128)) (omitted : Fin 3) :
    (Finset.univ.filter fun draw : Fin 3 → Fin 128 => OmitCovered exposed omitted draw).card =
      exposed.card.descFactorial 2 * 128 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (omitCoveredEquiv exposed omitted),
    Fintype.card_prod, Fintype.card_subtype, covered_count, Fintype.card_fin]
noncomputable def bucketOmitCoveredEquiv (exposed : Fin 16 → Finset (Fin 128))
    (omitted : Fin 3) :
    {draw : Fin 16 × (Fin 3 → Fin 128) // OmitCovered (exposed draw.1) omitted draw.2} ≃
      (bucket : Fin 16) × {draw : Fin 3 → Fin 128 // OmitCovered (exposed bucket) omitted draw} where
  toFun draw := ⟨draw.1.1, draw.1.2, draw.2⟩
  invFun draw := ⟨(draw.1, draw.2.1), draw.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem bucket_omitCovered_count (exposed : Fin 16 → Finset (Fin 128)) (omitted : Fin 3) :
    (Finset.univ.filter fun draw : Fin 16 × (Fin 3 → Fin 128) =>
      OmitCovered (exposed draw.1) omitted draw.2).card =
      (∑ bucket, (exposed bucket).card.descFactorial 2) * 128 := by
  rw [← Fintype.card_subtype, Fintype.card_congr (bucketOmitCoveredEquiv exposed omitted),
    Fintype.card_sigma]
  simp only [Fintype.card_subtype, omitCovered_count, Finset.sum_mul]
theorem bucket_omitCovered_probability (exposed : Fin 16 → Finset (Fin 128)) (omitted : Fin 3) :
    Pr[fun draw : Fin 16 × (Fin 3 → Fin 128) => OmitCovered (exposed draw.1) omitted draw.2 |
      ($ᵗ (Fin 16 × (Fin 3 → Fin 128)) : ProbComp _)] =
      (∑ bucket, ((exposed bucket).card.descFactorial 2 : ENNReal)) / (16 * 128^2) := by
  rw [probEvent_uniformSample, bucket_omitCovered_count]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum]
  rw [div_eq_mul_inv, mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem uniform_forall_probability {α : Type} [Fintype α] [SampleableType α]
    (count : Nat) (event : Fin count → α → Prop) :
    Pr[fun draw : Fin count → α => ∀ coord, event coord (draw coord) |
      ($ᵗ (Fin count → α) : ProbComp _)] =
      ∏ coord, Pr[event coord | ($ᵗ α : ProbComp _)] := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype,
    Fintype.card_congr (Equiv.subtypePiEquivPi (p := event)), Fintype.card_pi]
  simp only [probEvent_uniformSample, Fintype.card_subtype, Nat.cast_prod, Fintype.card_fun,
    Fintype.card_fin, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
def NearCovered (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) (draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : Prop :=
  ∀ coord, if coord = missing then OmitCovered (exposed coord (draw coord).1) omitted (draw coord).2
    else Covered (exposed coord (draw coord).1) (draw coord).2
theorem nearCovered_of_all_but (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) (draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128)))
    (hinj : ∀ coord, Function.Injective (draw coord).2)
    (hcovered : ∀ coord slot, (coord, slot) ≠ (missing, omitted) →
      (draw coord).2 slot ∈ exposed coord (draw coord).1) :
    NearCovered exposed missing omitted draw := by
  intro coord
  by_cases hcoord : coord = missing
  · rw [if_pos hcoord]
    apply omitCovered_of_all_but _ _ _ (hinj coord)
    intro slot hslot
    exact hcovered coord slot (fun he => hslot (Prod.mk.inj he).2)
  · rw [if_neg hcoord]
    exact ⟨hinj coord, fun slot => hcovered coord slot (fun he => hcoord (Prod.mk.inj he).1)⟩
theorem nearCovered_probability (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[NearCovered exposed missing omitted |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] =
      ∏ coord, if coord = missing then
        (∑ bucket, ((exposed coord bucket).card.descFactorial 2 : ENNReal)) / (16 * 128^2)
      else (∑ bucket, ((exposed coord bucket).card.descFactorial 3 : ENNReal)) / (16 * 128^3) := by
  unfold NearCovered
  rw [uniform_forall_probability 7 (fun coord (draw : Fin 16 × (Fin 3 → Fin 128)) =>
    if coord = missing then OmitCovered (exposed coord draw.1) omitted draw.2
    else Covered (exposed coord draw.1) draw.2)]
  apply Finset.prod_congr rfl
  intro coord _
  by_cases he : coord = missing
  · simp only [he, if_true]
    exact bucket_omitCovered_probability _ omitted
  · simp only [he, if_false]
    exact bucket_covered_probability _
theorem near_denominator_product (missing : Fin 7) :
    (∏ coord : Fin 7, if coord = missing then ((128 : ENNReal)^2)⁻¹
      else ((128 : ENNReal)^3)⁻¹) = ((2 : ENNReal)^140)⁻¹ := by
  have he : (∏ coord : Fin 7, if coord = missing then ((128 : ENNReal)^2)⁻¹
      else ((128 : ENNReal)^3)⁻¹) =
      ((128 : ENNReal)^2)⁻¹ * (((128 : ENNReal)^3)⁻¹)^6 := by
    rw [Finset.prod_ite]
    have hfilter : (Finset.univ.filter fun coord : Fin 7 => coord = missing) = {missing} := by
      ext coord
      simp
    rw [hfilter]
    simp [Finset.prod_const, Finset.filter_ne']
  rw [he]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow]
theorem div_bucket_leaf_power (value : ENNReal) (power : Nat) :
    value / (16 * (128 : ENNReal)^power) = value / 16 / 128^power := by
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num : (16 : ENNReal) ≠ 0))
    (Or.inl (by finiteness : (16 : ENNReal) ≠ ⊤)), mul_assoc]
noncomputable def rawNearWordEnvelope (missing : Fin 7) (word : List History.Buckets) : ENNReal :=
  (∏ c, if c=missing then Numeric.nearCoordinateEnvelope (word.map fun row => row c)
    else coordinateEnvelope (word.map fun row => row c))/2^140
theorem nearCovered_le_rawWordEnvelope
    (word : List History.Buckets) (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (hcard : ∀ coord bucket, (exposed coord bucket).card ≤
      3 * (word.map (fun row => row coord)).count bucket)
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[NearCovered exposed missing omitted |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] ≤
      rawNearWordEnvelope missing word := by
  rw [nearCovered_probability]
  calc
    _ ≤ ∏ coord : Fin 7, if coord = missing then
        Numeric.nearCoordinateEnvelope (word.map (fun row => row coord)) / 128^2
      else coordinateEnvelope (word.map (fun row => row coord)) / 128^3 := by
      apply Finset.prod_le_prod'
      intro coord _
      by_cases he : coord = missing
      · simp only [he, if_true, Numeric.nearCoordinateEnvelope, div_bucket_leaf_power]
        apply ENNReal.div_le_div_right
        apply ENNReal.div_le_div_right
        apply Finset.sum_le_sum
        intro bucket _
        exact_mod_cast Nat.descFactorial_le 2 (hcard missing bucket)
      · simp only [he, if_false, coordinateEnvelope, bucketMass, div_bucket_leaf_power]
        apply ENNReal.div_le_div_right
        apply ENNReal.div_le_div_right
        apply Finset.sum_le_sum
        intro bucket _
        exact_mod_cast Nat.descFactorial_le 3 (hcard coord bucket)
    _ = _ := by
      have hf : (fun coord : Fin 7 => if coord = missing then
          Numeric.nearCoordinateEnvelope (word.map (fun row => row coord)) / 128^2
        else coordinateEnvelope (word.map (fun row => row coord)) / 128^3) =
          (fun coord : Fin 7 =>
            (if coord = missing then Numeric.nearCoordinateEnvelope (word.map (fun row => row coord))
              else coordinateEnvelope (word.map (fun row => row coord))) *
            (if coord = missing then ((128 : ENNReal)^2)⁻¹ else ((128 : ENNReal)^3)⁻¹)) := by
        funext coord
        split_ifs <;> rfl
      rw [hf, Finset.prod_mul_distrib, near_denominator_product]
      rfl
theorem nearCovered_le_wordEnvelope
    (word : List History.Buckets) (exposed : Fin 7 → Fin 16 → Finset (Fin 128))
    (hcard : ∀ coord bucket, (exposed coord bucket).card ≤
      3*(word.map (fun row => row coord)).count bucket)
    (missing : Fin 7) (omitted : Fin 3) :
    Pr[fun output => (SigGolfResearch.Gate6.digestRecord output).2.2.1=0 ∧
      NearCovered exposed missing omitted
        (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ History.nearWordEnvelope missing word := by
  rw [SigGolfResearch.Gate6.digest_gated_event_probability]
  refine (ENNReal.div_le_div_right (nearCovered_le_rawWordEnvelope word exposed hcard missing omitted) 8).trans_eq ?_
  simp only [rawNearWordEnvelope,History.nearWordEnvelope,div_eq_mul_inv,mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_pow]
end SigGolfCandidate.T3.BPORS
end
