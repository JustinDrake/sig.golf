import SigGolfCandidate.T3.Gate6.SourceWeighted
import SigGolfCandidate.T3.Proofs
namespace SigGolfCandidate.T3.DigestSampling
open OracleComp OracleSpec ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

abbrev RawView := Fin (2^31) × (Fin 7 → Fin 16 × (Fin 3 → Fin 128))
abbrev Coordinates := RawView × BitVec 50

def rawView (output : HashOutput) : RawView :=
  ((output.extractLsb' 0 31).toFin, fun c =>
    ((output.extractLsb' (31+25*c.val) 4).toFin,
      fun j => (output.extractLsb' (31+25*c.val+4+7*j.val) 7).toFin))

def coordinates (output : HashOutput) : Coordinates :=
  (rawView output,output.extractLsb' 206 50)

/-- All 256 bits are partitioned into index, seven bucket/leaf groups, and
unused bits. No rejection or sorting is involved in this bijection. -/
theorem coordinates_injective : Function.Injective coordinates := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  by_cases hindex : position<31
  · have hc := congrArg (fun x : Coordinates => BitVec.ofFin x.1.1) heq
    change left.extractLsb' 0 31=right.extractLsb' 0 31 at hc
    have hb := congrArg (fun bits : BitVec 31 => bits.getLsbD position) hc
    simpa only [BitVec.getLsbD_extractLsb',hindex,decide_true,Bool.true_and,Nat.zero_add] using hb
  · by_cases hslots : position<206
    · let c : Fin 7 := ⟨(position-31)/25,by omega⟩
      let within := (position-31)%25
      have hwithin : within<25 := by dsimp [within];omega
      have hoff : 31+25*c.val+within=position := by dsimp [c,within];omega
      by_cases hbucket : within<4
      · have hc := congrArg (fun x : Coordinates => (BitVec.ofFin (x.1.2 c).1 : BitVec 4)) heq
        change left.extractLsb' (31+25*c.val) 4=right.extractLsb' (31+25*c.val) 4 at hc
        have hb := congrArg (fun bits : BitVec 4 => bits.getLsbD within) hc
        simpa only [BitVec.getLsbD_extractLsb',hbucket,decide_true,Bool.true_and,hoff] using hb
      · let j : Fin 3 := ⟨(within-4)/7,by omega⟩
        let bit := (within-4)%7
        have hbit : bit<7 := by dsimp [bit];omega
        have hoff' : 31+25*c.val+4+7*j.val+bit=position := by dsimp [j,bit];omega
        have hc := congrArg (fun x : Coordinates => (BitVec.ofFin ((x.1.2 c).2 j) : BitVec 7)) heq
        change left.extractLsb' (31+25*c.val+4+7*j.val) 7=
          right.extractLsb' (31+25*c.val+4+7*j.val) 7 at hc
        have hb := congrArg (fun bits : BitVec 7 => bits.getLsbD bit) hc
        simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff'] using hb
    · have hc := congrArg Prod.snd heq
      change left.extractLsb' 206 50=right.extractLsb' 206 50 at hc
      have hb := congrArg (fun bits : BitVec 50 => bits.getLsbD (position-206)) hc
      have hbit : position-206<50 := by omega
      have hoff : 206+(position-206)=position := by omega
      simpa only [BitVec.getLsbD_extractLsb',hbit,decide_true,Bool.true_and,hoff] using hb

theorem coordinates_bijective : Function.Bijective coordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨coordinates_injective,?_⟩
  simp only [Coordinates,RawView,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bitVec]
  rfl

noncomputable def coordinatesEquiv : HashOutput ≃ Coordinates :=
  Equiv.ofBijective coordinates coordinates_bijective

theorem uniform_coordinates :
    𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ Coordinates : ProbComp Coordinates)] :=
  evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Coordinates) coordinates coordinates_bijective

def rawSelections (view : RawView) : List Selection :=
  List.ofFn fun c : Fin 7 =>
    ⟨(view.2 c).1.val,(List.ofFn fun j : Fin 3 => ((view.2 c).2 j).val).mergeSort (· ≤ ·)⟩

theorem rawView_index (output : HashOutput) : (rawView output).1.val=output.toNat%2^31 := by
  simp [rawView,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem rawView_bucket (output : HashOutput) (c : Fin 7) :
    ((rawView output).2 c).1.val=output.toNat/2^(31+25*c.val)%16 := by
  simp [rawView,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]

theorem rawView_leaf (output : HashOutput) (c : Fin 7) (j : Fin 3) :
    (((rawView output).2 c).2 j).val=output.toNat/2^(31+25*c.val)/2^(4+7*j.val)%128 := by
  simp only [rawView,BitVec.val_toFin,BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul,← Nat.pow_add]
  congr 3
  omega

theorem rawSelections_eq_selections (output : HashOutput) :
    rawSelections (rawView output)=selections output := by
  apply List.ext_getElem
  · simp [rawSelections,selections]
  · intro c hc hc'
    simp only [rawSelections,List.getElem_ofFn,selections,List.getElem_map,List.getElem_range]
    congr 1
    · exact rawView_bucket output ⟨c,by simpa [rawSelections] using hc⟩
    · congr 1
      apply List.ext_getElem
      · simp
      · intro j hj hj'
        simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range]
        exact rawView_leaf output ⟨c,by simpa [rawSelections] using hc⟩ ⟨j,by simpa using hj⟩



abbrev LeafChoices := Fin 7 → Fin 3 → Fin 128

def leafSelections (leaves : LeafChoices) : List Selection :=
  List.ofFn fun c : Fin 7 =>
    ⟨0,(List.ofFn fun j : Fin 3 => (leaves c j).val).mergeSort (· ≤ ·)⟩

def leafAdmissible (leaves : LeafChoices) : Bool := admissible (leafSelections leaves)

theorem raw_admissible (view : RawView) :
    admissible (rawSelections view)=leafAdmissible (fun c => (view.2 c).2) := by
  simpa only [rawSelections,leafAdmissible,leafSelections,List.map_ofFn,Function.comp_def] using
    (admissible_bucket_map (rawSelections view) (fun _ => 0)).symm

/-- Exact source acceptance reads only the 147 leaf bits. In particular, it
is independent of the 31 index bits and the 28 bucket bits before sampling. -/
theorem source_admissible (output : HashOutput) :
    admissible (selections output)=leafAdmissible (fun c => ((rawView output).2 c).2) := by
  rw [← rawSelections_eq_selections]
  exact raw_admissible _

end SigGolfCandidate.T3.DigestSampling


namespace SigGolfCandidate.T3.DigestSampling
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfResearch.Gate6.Moments
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

abbrev IndexBuckets := Fin (2^31) × (Fin 7 → Fin 16)
abbrev SamplingData := IndexBuckets × LeafChoices

def regroup : Coordinates ≃ SamplingData × BitVec 50 where
  toFun x := (((x.1.1,fun c => (x.1.2 c).1),fun c => (x.1.2 c).2),x.2)
  invFun x := ((x.1.1.1,fun c => (x.1.1.2 c,x.1.2 c)),x.2)
  left_inv x := by rcases x with ⟨⟨idx,columns⟩,unused⟩;rfl
  right_inv x := by rcases x with ⟨⟨⟨idx,buckets⟩,leaves⟩,unused⟩;rfl

def samplingData (output : HashOutput) : SamplingData := (regroup (coordinates output)).1

theorem uniform_samplingData :
    𝒮[samplingData <$> ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ SamplingData : ProbComp SamplingData)] := by
  have hwhole : 𝒮[(fun output => regroup (coordinates output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)]=
      𝒮[($ᵗ (SamplingData × BitVec 50) : ProbComp _)] :=
    evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := SamplingData × BitVec 50)
      _ (regroup.bijective.comp coordinates_bijective)
  change 𝒮[(fun output => (regroup (coordinates output)).1) <$> ($ᵗ HashOutput : ProbComp _)]=_
  rw [show (fun output => (regroup (coordinates output)).1) <$> ($ᵗ HashOutput : ProbComp _)=
    Prod.fst <$> ((fun output => regroup (coordinates output)) <$> ($ᵗ HashOutput : ProbComp _)) by
      simp only [Functor.map_map,Function.comp_def]]
  rw [evalSPMF_map,hwhole,← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod

theorem samplingData_expectedValue (payoff : SamplingData → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun output => payoff (samplingData output))=
      expectedValue ($ᵗ SamplingData : ProbComp SamplingData) payoff := by
  rw [← expectedValue_map]
  unfold expectedValue probOutput
  rw [uniform_samplingData]

theorem finiteAverage_mul_const {α : Type} [Fintype α] (f : α → ENNReal) (c : ENNReal) :
    finiteAverage (fun x => f x*c)=finiteAverage f*c := by
  simp only [finiteAverage,Finset.sum_mul,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem finiteAverage_const_mul {α : Type} [Fintype α] (c : ENNReal) (f : α → ENNReal) :
    finiteAverage (fun x => c*f x)=c*finiteAverage f := by
  simpa only [mul_comm] using finiteAverage_mul_const f c

theorem finiteAverage_pair_product {α β : Type} [Fintype α] [Fintype β]
    (f : α → ENNReal) (g : β → ENNReal) :
    finiteAverage (fun pair : α × β => f pair.1*g pair.2)=finiteAverage f*finiteAverage g := by
  rw [finiteAverage_pair]
  simp_rw [finiteAverage_const_mul,finiteAverage_mul_const]

noncomputable def acceptanceProbability : ENNReal := SigGolfResearch.Gate6.acceptance

/-- Exact factorization at the source rejection predicate: conditioning a
fresh digest on acceptance leaves the index/bucket distribution uniform. -/
theorem samplingData_mark (output : HashOutput) :
    (samplingData output).1=(SigGolfResearch.Gate6.digestRecord output).1 := rfl

theorem accepted_samplingData (payoff : IndexBuckets → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => if digestAdmissible output then payoff (samplingData output).1 else 0)=
        finiteAverage payoff*acceptanceProbability := by
  simp only [samplingData_mark,acceptanceProbability]
  exact SigGolfResearch.Gate6.Source.actual_accepted_mark_weight payoff

/-- A fresh random-oracle digest can be sampled through the same exact
index/bucket/leaf decomposition, even with an arbitrary continuation. -/
theorem fresh_digest_coordinates {Result : Type} (input : SphincsSecurity.HashInput)
    (cache : QueryCache SphincsSecurity.HashSpec) (hcache : cache input=none)
    (continuation : SphincsSecurity.HashOutput × QueryCache SphincsSecurity.HashSpec → ProbComp Result) :
    𝒮[(randomOracle input).run cache >>= continuation]=
      𝒮[($ᵗ Coordinates : ProbComp Coordinates) >>= fun pieces =>
        let output := coordinatesEquiv.symm pieces
        continuation (output,cache.cacheQuery input output)] := by
  rw [OracleSpec.randomOracle,QueryImpl.withCaching_run_none _ hcache]
  change 𝒮[((fun output : HashOutput => (output,cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation]=_
  have hcomp : ((fun output : HashOutput => (output,cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation=
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output => continuation (output,cache.cacheQuery input output) := by
    rw [map_eq_bind_pure_comp,LawfulMonad.bind_assoc]
    simp only [Function.comp_def,LawfulMonad.pure_bind,Equiv.symm_apply_apply]
  rw [hcomp]
  have hback : (coordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>=
      (fun pieces => continuation (coordinatesEquiv.symm pieces,cache.cacheQuery input (coordinatesEquiv.symm pieces)))=
      ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output => continuation (output,cache.cacheQuery input output) := by
    rw [map_eq_bind_pure_comp,LawfulMonad.bind_assoc]
    simp only [Function.comp_def,LawfulMonad.pure_bind,Equiv.symm_apply_apply]
  rw [← hback,evalSPMF_bind]
  change (𝒮[coordinates <$> ($ᵗ HashOutput : ProbComp HashOutput)] >>= _)=_
  rw [uniform_coordinates,← evalSPMF_bind]



/-- Counter-in-tweak inputs are distinct throughout every permitted search.
This statement includes an arbitrary starting counter without wraparound. -/
theorem digest_trial_inputs_injective (rho : Digest) (message : Message) (start fuel : Nat)
    (hlimit : start+fuel≤2^32) :
    Function.Injective (fun trial : Fin fuel => digestInput rho message (BitVec.ofNat 32 (start+trial.val))) := by
  intro i j he
  have hc := (digestInput_injective he).2.2
  have hi : start+i.val<2^32 := by omega
  have hj : start+j.val<2^32 := by omega
  have hn := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at hn
  exact Fin.ext (by omega)

end SigGolfCandidate.T3.DigestSampling


