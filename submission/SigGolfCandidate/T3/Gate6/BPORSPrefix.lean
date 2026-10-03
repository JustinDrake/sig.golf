import SigGolfCandidate.T3.Gate6.SourceBridge
import SigGolfCandidate.T3.Gate6.BankMoments
import SigGolfCandidate.T3.Proofs
import SigGolfCandidate.T3.Gate6.ExcessSquare
import SigGolfCandidate.T3.Gate6.Coverage

section


namespace SigGolfResearch.Gate6.Source
open SigGolfCandidate.T3 OracleComp ENNReal OracleComp.EvalDist Finset
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
set_option maxHeartbeats 1000000
theorem actual_accepted_mark_weight (payoff : MarkedLabel → ENNReal) :
    expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256))
      (fun output => if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        Moments.finiteAverage payoff*acceptance := by
  have hs (output : BitVec 256) :
      (if digestAdmissible output then payoff (digestRecord output).1 else 0)=
        ∑ mark : MarkedLabel,
          (if digestAdmissible output=true ∧ (digestRecord output).1=mark then 1 else 0)*payoff mark := by
    by_cases ha : digestAdmissible output=true
    · simp [ha,eq_comm]
    · simp [ha]
  simp only [expectedValue_def]
  simp_rw [hs,Finset.mul_sum,←mul_assoc,mul_ite,mul_one,mul_zero]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  simp_rw [ENNReal.tsum_mul_right,←probEvent_eq_tsum_ite,actual_mark_joint_exact]
  simp only [Moments.finiteAverage,markedLabel_card,Nat.cast_pow,Nat.cast_ofNat,
    div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mark _
  ring
end SigGolfResearch.Gate6.Source
end

section


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
theorem samplingData_mark (output : HashOutput) :
    (samplingData output).1=(SigGolfResearch.Gate6.digestRecord output).1 := rfl
theorem accepted_samplingData (payoff : IndexBuckets → ENNReal) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun output => if digestAdmissible output then payoff (samplingData output).1 else 0)=
        finiteAverage payoff*acceptanceProbability := by
  simp only [samplingData_mark,acceptanceProbability]
  exact SigGolfResearch.Gate6.Source.actual_accepted_mark_weight payoff
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
end

section



namespace SigGolfCandidate.T3.BPORS
export SigGolfResearch.Gate6.Moments (Covered coveredEquiv covered_count covered_probability covered_probability_le covered_product_count three_openings_polynomial two_openings_polynomial bucket_thinning near_bucket_thinning bucketCoveredEquiv bucket_covered_count bucket_covered_probability bucket_product_count bpors_covered_probability envelope distinct_bucket_cross_moment natEnvelope factorialPolynomial envelope_cast factorialPolynomial_eval fullCoefficients squareCoefficients full_envelope square_polynomial full_square_envelope envelope_thinning same_bucket_second_moment different_bucket_second_moment diagonalMoment crossMoment bucketMass coordinateEnvelope bucket_pair_moment coordinate_second_moment finiteAverage expected_uniform_eq_finiteAverage finiteAverage_product uniform_coordinate_product finiteAverage_equiv finiteAverage_pair uniformWordAverage_succ word_array_average seven_coordinate_second_moment firstMoment bucket_first_moment coordinate_first_moment seven_coordinate_first_moment)
namespace Numeric
export SigGolfResearch.Gate6.Moments.Numeric (childCoefficients childSquareCoefficients nearChildCoefficients meanCoeffs varianceCoeffs nearCoeffs mean_polynomial variance_polynomial near_polynomial envelope_power mean_envelope_power variance_envelope_power firstMoment_coefficients secondMoment_coefficients firstMoment_power_coefficients secondMoment_power_coefficients binomial_envelope_le_poisson forestEnvelope forest_first_moment forest_second_moment poissonEnvelope forest_binomial_first_bound forest_binomial_second_bound proposalLength poisson_mean_bound poisson_excess_bound poisson_near_bound poisson_near_tight_bound nearCoordinateEnvelope near_coordinate_first_moment nearForestEnvelope near_envelope_product near_forest_first_moment near_forest_binomial_bound uniform_history_mean_bound uniform_history_excess_bound uniform_history_near_bound)
end Numeric
end SigGolfCandidate.T3.BPORS
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete
open SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable def atIndex {α β : Type} [DecidableEq α] (index : α) (word : List (α × β)) : List β :=
  word.filterMap fun pair => if pair.1=index then some pair.2 else none
theorem atIndex_cons {α β : Type} [DecidableEq α] (index : α) (next : α × β) (word : List (α × β)) :
    atIndex index (next::word)=if next.1=index then next.2::atIndex index word else atIndex index word := by
  unfold atIndex
  split <;> simp_all
theorem finiteAverage_constant {α : Type} [Fintype α] [SampleableType α] (value : ENNReal) :
    finiteAverage (fun _ : α => value)=value := by
  rw [← expected_uniform_eq_finiteAverage]
  exact expectedValue_const (by simp) value
theorem average_binomial_commute {β : Type} [Fintype β]
    (p : ENNReal) (steps : Nat) (f : β → Nat → ENNReal) :
    finiteAverage (fun value => binomialAverage p steps (f value))=
      binomialAverage p steps (fun count => finiteAverage (fun value => f value count)) := by
  unfold finiteAverage
  simp only [div_eq_mul_inv]
  rw [binomialAverage_mul_right,binomialAverage_sum]
theorem finiteAverage_choice {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (index : α) (hit miss : ENNReal) :
    finiteAverage (fun next => if next=index then hit else miss)=
      (1-(Fintype.card α : ENNReal)⁻¹)*miss+(Fintype.card α : ENNReal)⁻¹*hit := by
  rw [← expected_uniform_eq_finiteAverage]
  exact expected_uniformSample_choice index hit miss
theorem uniform_marked_word_atIndex {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (index : α) (steps : Nat) (payoff : List β → ENNReal) :
    uniformWordAverage steps (fun word : List (α × β) => payoff (atIndex index word))=
      binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage count payoff) := by
  induction steps generalizing payoff with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,atIndex,binomialAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,finiteAverage_pair]
      have hm (next : α) :
          finiteAverage (fun mark : β => uniformWordAverage steps
            (fun word : List (α × β) => payoff (atIndex index ((next,mark)::word))))=
          if next=index then
            binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage (count+1) payoff)
          else binomialAverage (Fintype.card α : ENNReal)⁻¹ steps (fun count => uniformWordAverage count payoff) := by
        by_cases h : next=index
        · simp only [atIndex_cons,h,ite_true]
          have hmark (mark : β) : uniformWordAverage steps
              (fun word => payoff (mark::atIndex index word))=
              binomialAverage (Fintype.card α : ENNReal)⁻¹ steps
                (fun count => uniformWordAverage count (fun word => payoff (mark::word))) :=
            ih (fun word => payoff (mark::word))
          simp_rw [hmark]
          rw [average_binomial_commute]
          simp_rw [← uniformWordAverage_succ]
        · simp only [atIndex_cons,h,ite_false]
          rw [ih,finiteAverage_constant]
      simp_rw [hm]
      rw [finiteAverage_choice]
      rfl
abbrev Buckets := Fin 7 → Fin 16
noncomputable def wordEnvelope (word : List Buckets) : ENNReal :=
  (∏ c, coordinateEnvelope (word.map fun row => row c))/2^150
theorem word_forest_moment (steps power : Nat) :
    uniformWordAverage steps (fun word => wordEnvelope word^power)=
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
        (fun table => Numeric.forestEnvelope table^power) := by
  rw [word_array_average,expected_uniform_eq_finiteAverage]
  rw [← finiteAverage_equiv (Equiv.piComm (fun (_ : Fin 7) (_ : Fin steps) => Fin 16))]
  congr 1
  funext table
  simp only [wordEnvelope,Numeric.forestEnvelope,List.map_ofFn,Function.comp_def,Equiv.piComm_apply]
theorem uniform_proposal_forest_moment (index : Fin (2^31)) (steps power : Nat) :
    uniformWordAverage steps
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)^power)=
      binomialAverage (1/2^31) steps (fun count =>
        expectedValue ($ᵗ (Fin 7 → Fin count → Fin 16) : ProbComp _) (fun table => Numeric.forestEnvelope table^power)) := by
  rw [uniform_marked_word_atIndex index steps (fun word => wordEnvelope word^power)]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,one_div]
  simp_rw [word_forest_moment]
theorem uniform_proposal_mean_bound (index : Fin (2^31)) :
    (2 : ENNReal)^128*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)) ≤ 37/64 := by
  have h := uniform_proposal_forest_moment index Numeric.proposalLength 1
  simp only [pow_one] at h
  rw [h]
  exact Numeric.uniform_history_mean_bound
theorem uniform_proposal_excess_bound (index : Fin (2^31)) :
    (2 : ENNReal)^225*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex index word)^2) ≤ 18400/100000000 := by
  rw [uniform_proposal_forest_moment]
  exact Numeric.uniform_history_excess_bound
noncomputable def nearWordEnvelope (missing : Fin 7) (word : List Buckets) : ENNReal :=
  (∏ c, if c=missing then Numeric.nearCoordinateEnvelope (word.map fun row => row c)
    else coordinateEnvelope (word.map fun row => row c))/2^143
theorem word_near_forest_moment (steps : Nat) (missing : Fin 7) :
    uniformWordAverage steps (nearWordEnvelope missing)=
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (Numeric.nearForestEnvelope missing) := by
  rw [word_array_average,expected_uniform_eq_finiteAverage]
  rw [← finiteAverage_equiv (Equiv.piComm (fun (_ : Fin 7) (_ : Fin steps) => Fin 16))]
  congr 1
  funext table
  simp only [nearWordEnvelope,Numeric.nearForestEnvelope,List.map_ofFn,Function.comp_def,Equiv.piComm_apply]
theorem uniform_proposal_near_bound (index : Fin (2^31)) (missing : Fin 7) :
    21*(2 : ENNReal)^128*uniformWordAverage Numeric.proposalLength
      (fun word : List (Fin (2^31) × Buckets) => nearWordEnvelope missing (atIndex index word)) ≤ 404 := by
  rw [uniform_marked_word_atIndex index Numeric.proposalLength (nearWordEnvelope missing)]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
  simp_rw [word_near_forest_moment]
  simpa only [one_div] using Numeric.uniform_history_near_bound missing
def exposedLeaves (history : List (Buckets × LeafChoices)) (c : Fin 7) (bucket : Fin 16) : Finset (Fin 128) :=
  ((history.filter fun row => row.1 c==bucket).flatMap fun row => List.ofFn (row.2 c)).toFinset
theorem exposedLeaves_card_le (history : List (Buckets × LeafChoices)) (c : Fin 7) (bucket : Fin 16) :
    (exposedLeaves history c bucket).card ≤ 3*(history.map fun row => row.1 c).count bucket := by
  calc
    _ ≤ ((history.filter fun row => row.1 c==bucket).flatMap fun row => List.ofFn (row.2 c)).length :=
      List.toFinset_card_le _
    _ = 3*(history.filter fun row => row.1 c==bucket).length := by
      simp [List.length_flatMap,List.length_ofFn,List.sum_replicate,Nat.mul_comm]
    _ = _ := by
      simp only [List.count_eq_countP,List.countP_map]
      rw [List.countP_eq_length_filter]
      rfl
def wordTable (word : List Buckets) : Fin 7 → Fin word.length → Fin 16 :=
  fun c i => word.get i c
theorem wordTable_column (word : List Buckets) (c : Fin 7) :
    List.ofFn (wordTable word c)=word.map (fun row => row c) := by
  exact List.ofFn_getElem_eq_map word (fun row => row c)
theorem wordTable_envelope (word : List Buckets) :
    Numeric.forestEnvelope (wordTable word)=wordEnvelope word := by
  simp only [Numeric.forestEnvelope,wordEnvelope,wordTable_column]
theorem history_covered_probability_le (history : List (Buckets × LeafChoices)) :
    Pr[fun output : HashOutput => digestAdmissible output=true ∧
      SigGolfResearch.Gate6.CoordinateCovered (exposedLeaves history)
        (SigGolfResearch.Gate6.rawDraw (SigGolfResearch.Gate6.digestRecord output)).1 |
      ($ᵗ HashOutput : ProbComp HashOutput)] ≤ wordEnvelope (history.map Prod.fst) := by
  simp_rw [SigGolfResearch.Gate6.Source.actual_predicate_iff]
  rw [←wordTable_envelope]
  apply SigGolfResearch.Gate6.accepted_covered_le_forestEnvelope
  intro c bucket
  rw [wordTable_column]
  simpa only [List.map_map,Function.comp_def] using exposedLeaves_card_le history c bucket
end SigGolfCandidate.T3.BPORS.History
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
noncomputable def jointCountAverage {α : Type} [Fintype α] [DecidableEq α]
    (first second : α) : Nat → (Nat → Nat → ENNReal) → ENNReal
  | 0, payoff => payoff 0 0
  | steps+1, payoff => finiteAverage fun next : α =>
      if next=first then jointCountAverage first second steps (fun i j => payoff (i+1) j)
      else if next=second then jointCountAverage first second steps (fun i j => payoff i (j+1))
      else jointCountAverage first second steps payoff
theorem finiteAverage_commute {α β : Type} [Fintype α] [Fintype β] (f : α → β → ENNReal) :
    finiteAverage (fun a => finiteAverage (f a))=
      finiteAverage (fun b => finiteAverage (fun a => f a b)) := by
  rw [← finiteAverage_pair (fun pair : α × β => f pair.1 pair.2),
    ← finiteAverage_pair (fun pair : β × α => f pair.2 pair.1)]
  exact (finiteAverage_equiv (Equiv.prodComm β α) (fun pair : α × β => f pair.1 pair.2)).symm
theorem average_joint_commute {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    (first second : α) (steps : Nat) (payoff : β → Nat → Nat → ENNReal) :
    finiteAverage (fun mark => jointCountAverage first second steps (payoff mark))=
      jointCountAverage first second steps (fun i j => finiteAverage (fun mark => payoff mark i j)) := by
  induction steps generalizing payoff with
  | zero => rfl
  | succ steps ih =>
      simp only [jointCountAverage]
      rw [finiteAverage_commute]
      congr 1
      funext next
      by_cases hf : next=first
      · simp only [hf,ite_true]
        exact ih (fun mark i j => payoff mark (i+1) j)
      · by_cases hs : next=second
        · subst next
          simp only [hf,ite_false,ite_true]
          exact ih (fun mark i j => payoff mark i (j+1))
        · simp only [hf,hs,ite_false]
          exact ih payoff
theorem uniform_word_joint_count {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (first second : α) (hne : first≠second) (steps : Nat) (payoff : Nat → Nat → ENNReal) :
    uniformWordAverage steps (fun word : List α => payoff (word.count first) (word.count second))=
      jointCountAverage first second steps payoff := by
  induction steps generalizing payoff with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,jointCountAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,jointCountAverage]
      congr 1
      funext next
      by_cases hf : next=first
      · subst next
        simp only [List.count_cons_self,List.count_cons_of_ne hne,ite_true]
        exact ih (fun i j => payoff (i+1) j)
      · by_cases hs : next=second
        · subst next
          simp only [List.count_cons_self,List.count_cons_of_ne hne.symm,if_neg hf,ite_true]
          exact ih (fun i j => payoff i (j+1))
        · simp only [List.count_cons_of_ne hf,List.count_cons_of_ne hs,if_neg hf,if_neg hs]
          exact ih payoff
theorem uniform_marked_word_joint {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first≠second) (steps : Nat)
    (f g : List β → ENNReal) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)*g (atIndex second word))=
      jointCountAverage first second steps (fun i j => uniformWordAverage i f*uniformWordAverage j g) := by
  induction steps generalizing f g with
  | zero => simp [uniformWordAverage,sampleUniformProposalWord,atIndex,jointCountAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ,finiteAverage_pair,jointCountAverage]
      congr 1
      funext next
      by_cases hf : next=first
      · subst next
        simp only [atIndex_cons,if_pos rfl,if_neg hne,ite_true]
        have hm (mark : β) :
            uniformWordAverage steps (fun word : List (α × β) =>
              f (mark::atIndex first word)*g (atIndex second word))=
            jointCountAverage first second steps (fun i j =>
              uniformWordAverage i (fun word => f (mark::word))*uniformWordAverage j g) :=
          ih (fun word => f (mark::word)) g
        simp_rw [hm]
        rw [average_joint_commute]
        simp_rw [finiteAverage_mul_const,← uniformWordAverage_succ]
      · by_cases hs : next=second
        · subst next
          simp only [atIndex_cons,if_neg hf,if_pos rfl,ite_true]
          have hm (mark : β) :
              uniformWordAverage steps (fun word : List (α × β) =>
                f (atIndex first word)*g (mark::atIndex second word))=
              jointCountAverage first second steps (fun i j =>
                uniformWordAverage i f*uniformWordAverage j (fun word => g (mark::word))) :=
            ih f (fun word => g (mark::word))
          simp_rw [hm]
          rw [average_joint_commute]
          simp_rw [finiteAverage_const_mul,← uniformWordAverage_succ]
        · simp only [atIndex_cons,if_neg hf,if_neg hs]
          rw [ih,finiteAverage_constant]
theorem uniform_envelope_negative_correlation {α : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    (first second : α) (hne : first≠second) (steps : Nat) (a b : List Nat) :
    uniformWordAverage steps (fun word : List α => envelope a (word.count first)*envelope b (word.count second)) ≤
      uniformWordAverage steps (fun word : List α => envelope a (word.count first))*
        uniformWordAverage steps (fun word : List α => envelope b (word.count second)) := by
  simp only [envelope,Finset.sum_mul,Finset.mul_sum,uniformWordAverage_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  have hp (word : List α) :
      ((a.getD i 0 : ENNReal)*(word.count first).descFactorial i)*
        ((b.getD j 0 : ENNReal)*(word.count second).descFactorial j)=
      ((a.getD i 0 : ENNReal)*b.getD j 0)*
        ((word.count first).descFactorial i*(word.count second).descFactorial j) := by ring
  simp_rw [hp,uniformWordAverage_mul_left]
  calc
    _ ≤ ((a.getD i 0 : ENNReal)*b.getD j 0)*
        (uniformWordAverage steps (fun word : List α => (word.count first).descFactorial i)*
          uniformWordAverage steps (fun word : List α => (word.count second).descFactorial j)) :=
      mul_le_mul' le_rfl (uniformWordAverage_mixed_descFactorial_le_product first second hne steps i j)
    _ = _ := by ring
theorem uniformWordAverage_mul_right {α : Type} [SampleableType α]
    (steps : Nat) (factor : ENNReal) (payoff : List α → ENNReal) :
    uniformWordAverage steps (fun word => payoff word*factor)=uniformWordAverage steps payoff*factor := by
  simpa only [mul_comm] using uniformWordAverage_mul_left steps factor payoff
theorem marked_marginal_envelope {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (index : α) (steps : Nat) (f : List β → ENNReal)
    (a : List Nat) (scale : ENNReal) (hf : ∀ n, uniformWordAverage n f=envelope a n*scale) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex index word))=
      uniformWordAverage steps (fun word : List α => envelope a (word.count index))*scale := by
  rw [uniform_marked_word_atIndex]
  simp_rw [hf]
  rw [← uniformWordAverage_mul_right]
  exact (expected_uniformProposalWord_count index steps (fun n => envelope a n*scale)).symm
theorem marked_envelope_negative_correlation {α β : Type} [Fintype α] [SampleableType α] [DecidableEq α]
    [Fintype β] [SampleableType β] (first second : α) (hne : first≠second) (steps : Nat)
    (f g : List β → ENNReal) (a b : List Nat) (u v : ENNReal)
    (hf : ∀ n, uniformWordAverage n f=envelope a n*u)
    (hg : ∀ n, uniformWordAverage n g=envelope b n*v) :
    uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word)*g (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (α × β) => f (atIndex first word))*
        uniformWordAverage steps (fun word : List (α × β) => g (atIndex second word)) := by
  rw [uniform_marked_word_joint first second hne,
    ← uniform_word_joint_count first second hne]
  simp_rw [hf,hg]
  rw [marked_marginal_envelope first steps f a u hf,marked_marginal_envelope second steps g b v hg]
  have hp (word : List α) :
      (envelope a (word.count first)*u)*(envelope b (word.count second)*v)=
        (envelope a (word.count first)*envelope b (word.count second))*(u*v) := by ring
  simp_rw [hp]
  rw [uniformWordAverage_mul_right]
  calc
    _ ≤ (uniformWordAverage steps (fun word : List α => envelope a (word.count first))*
        uniformWordAverage steps (fun word : List α => envelope b (word.count second)))*(u*v) :=
      mul_le_mul' (uniform_envelope_negative_correlation first second hne steps a b) le_rfl
    _ = _ := by ring
theorem word_first_moment (steps : Nat) :
    uniformWordAverage steps wordEnvelope=envelope Numeric.meanCoeffs steps/2^234 := by
  have h := word_forest_moment steps 1
  simpa only [pow_one,Numeric.forest_first_moment] using h
theorem forest_negative_correlation (first second : Fin (2^31)) (hne : first≠second) (steps : Nat) :
    uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) =>
      wordEnvelope (atIndex first word)*wordEnvelope (atIndex second word)) ≤
      uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex first word))*
        uniformWordAverage steps (fun word : List (Fin (2^31) × Buckets) => wordEnvelope (atIndex second word)) := by
  apply marked_envelope_negative_correlation first second hne steps wordEnvelope wordEnvelope
    Numeric.meanCoeffs Numeric.meanCoeffs ((2^234 : ENNReal)⁻¹) ((2^234 : ENNReal)⁻¹)
  · intro n;simpa only [div_eq_mul_inv] using word_first_moment n
  · intro n;simpa only [div_eq_mul_inv] using word_first_moment n
end SigGolfCandidate.T3.BPORS.History
namespace SigGolfCandidate.T3.BPORS.History
open OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SphincsSecurity.Concrete SigGolfCandidate.T3.DigestSampling
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
abbrev Proposal := Fin (2^31) × Buckets
noncomputable def fullPrice (word : List Proposal) : ENNReal :=
  2^97*∑ index : Fin (2^31), wordEnvelope (atIndex index word)
theorem fullPrice_ne_top (word : List Proposal) : fullPrice word≠⊤ := by
  unfold fullPrice
  apply ENNReal.mul_ne_top (by finiteness)
  apply ENNReal.sum_ne_top.mpr
  intro index _
  unfold wordEnvelope coordinateEnvelope bucketMass
  apply ENNReal.div_ne_top ?_ (by norm_num)
  apply ENNReal.prod_ne_top
  intro c _
  apply ENNReal.div_ne_top ?_ (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro bucket _
  exact ENNReal.natCast_ne_top _
theorem fullPrice_mean (steps : Nat) :
    uniformWordAverage steps fullPrice=
      (2 : ENNReal)^128*binomialAverage (1/2^31) steps (fun count =>
        expectedValue ($ᵗ (Fin 7 → Fin count → Fin 16) : ProbComp _) Numeric.forestEnvelope) := by
  have hm (index : Fin (2^31)) := uniform_proposal_forest_moment index steps 1
  simp only [pow_one] at hm
  unfold fullPrice
  rw [uniformWordAverage_mul_left,uniformWordAverage_sum]
  simp_rw [hm]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_assoc,← pow_add]
theorem fullPrice_mean_bound :
    uniformWordAverage Numeric.proposalLength fullPrice ≤ 37/64 := by
  rw [fullPrice_mean]
  exact Numeric.uniform_history_mean_bound
theorem fullPrice_secondMoment_bound :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word^2) ≤
      uniformWordAverage Numeric.proposalLength fullPrice^2+(18400/100000000) := by
  have hs := uniformWordAverage_sum_square_le Numeric.proposalLength
    (fun index (word : List Proposal) => wordEnvelope (atIndex index word))
    (fun first second hne => forest_negative_correlation first second hne Numeric.proposalLength)
  have hscaled := mul_le_mul' (a := ((2 : ENNReal)^97)^2) le_rfl hs
  have hdiag :
      ((2 : ENNReal)^97)^2*(∑ index : Fin (2^31), uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) ≤ (18400/100000000) := by
    simp_rw [uniform_proposal_forest_moment]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [← pow_mul,← mul_assoc,← pow_add]
    simpa only [Nat.reduceMul,Nat.reduceAdd] using Numeric.uniform_history_excess_bound
  calc
    _ = ((2 : ENNReal)^97)^2*uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => (∑ index,wordEnvelope (atIndex index word))^2) := by
      simp only [fullPrice,mul_pow,uniformWordAverage_mul_left]
    _ ≤ ((2 : ENNReal)^97)^2*((∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
        (fun word : List Proposal => wordEnvelope (atIndex index word)))^2+
        ∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
          (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) := hscaled
    _ = uniformWordAverage Numeric.proposalLength fullPrice^2+
        ((2 : ENNReal)^97)^2*(∑ index : Fin (2^31),uniformWordAverage Numeric.proposalLength
          (fun word : List Proposal => wordEnvelope (atIndex index word)^2)) := by
      unfold fullPrice
      simp only [uniformWordAverage_mul_left,uniformWordAverage_sum,mul_pow,mul_add]
    _ ≤ _ := add_le_add le_rfl hdiag
theorem unit_excess_le_square (value mean : ENNReal) (hvalue : value≠⊤) (hmean : mean≤37/64) :
    (13/8)*(value-1)+2*mean*value ≤ value^2+mean^2 := by
  have hx : value-1≤value-63/64 := tsub_le_tsub_left (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_div]) value
  exact (add_le_add (mul_le_mul' le_rfl hx) le_rfl).trans
    (SigGolfResearch.Gate6.Excess.theta_excess_le_square value mean hvalue hmean)
theorem uniformWordAverage_constant {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (value : ENNReal) : uniformWordAverage steps (fun _ : List α => value)=value := by
  rw [word_array_average]
  exact finiteAverage_constant value
theorem fullPrice_excess_of_pointwise (threshold : ENNReal)
    (hpointwise : ∀ value mean : ENNReal,value≠⊤ → mean≤37/64 →
      (13/8)*(value-threshold)+2*mean*value≤value^2+mean^2) :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-threshold) ≤ 11324/100000000 := by
  let mean := uniformWordAverage Numeric.proposalLength fullPrice
  have hm : mean≠⊤ := ne_top_of_le_ne_top (by finiteness) fullPrice_mean_bound
  have h := uniformWordAverage_mono Numeric.proposalLength (fun word =>
    hpointwise (fullPrice word) mean (fullPrice_ne_top word) fullPrice_mean_bound)
  rw [uniformWordAverage_add,uniformWordAverage_add,uniformWordAverage_mul_left,
    uniformWordAverage_mul_left,uniformWordAverage_constant] at h
  have hcancel : (13/8:ENNReal)*uniformWordAverage Numeric.proposalLength
      (fun word => fullPrice word-threshold)≤18400/100000000 := by
    apply ENNReal.le_of_add_le_add_right (a := 2*mean^2) (by finiteness)
    calc
      _ = (13/8:ENNReal)*uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-threshold)+
          2*mean*uniformWordAverage Numeric.proposalLength fullPrice := by
        change _=_+2*mean*mean
        ring
      _ ≤ uniformWordAverage Numeric.proposalLength (fun word => fullPrice word^2)+mean^2 := h
      _ ≤ (mean^2+18400/100000000)+mean^2 := add_le_add fullPrice_secondMoment_bound le_rfl
      _ = _ := by ring
  have hi : (8/13:ENNReal)*(13/8)=1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
  calc
    _ = (8/13:ENNReal)*((13/8)*uniformWordAverage Numeric.proposalLength
        (fun word => fullPrice word-threshold)) := by rw [←mul_assoc,hi,one_mul]
    _ ≤ (8/13:ENNReal)*(18400/100000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div]
theorem fullPrice_excess_bound :
    uniformWordAverage Numeric.proposalLength (fun word => fullPrice word-1) ≤ 11324/100000000 :=
  fullPrice_excess_of_pointwise 1 unit_excess_le_square
noncomputable def fullNearPrice (word : List Proposal) : ENNReal :=
  3*2^97*∑ index : Fin (2^31), ∑ missing : Fin 7, nearWordEnvelope missing (atIndex index word)
theorem near_mean_at_index (index : Fin (2^31)) (missing : Fin 7) (steps : Nat) :
    uniformWordAverage steps (fun word : List Proposal => nearWordEnvelope missing (atIndex index word))=
      binomialAverage (1/2^31) steps (fun count => envelope Numeric.nearCoeffs count/2^223) := by
  rw [uniform_marked_word_atIndex index steps (nearWordEnvelope missing)]
  simp_rw [word_near_forest_moment,Numeric.near_forest_first_moment]
  simp only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,one_div]
theorem fullNearPrice_bound : uniformWordAverage Numeric.proposalLength fullNearPrice ≤ 404 := by
  have h := Numeric.uniform_history_near_bound (0 : Fin 7)
  simp_rw [Numeric.near_forest_first_moment] at h
  have he : uniformWordAverage Numeric.proposalLength fullNearPrice=
      21*(2 : ENNReal)^128*binomialAverage (1/2^31) Numeric.proposalLength
        (fun count => envelope Numeric.nearCoeffs count/2^223) := by
    unfold fullNearPrice
    rw [uniformWordAverage_mul_left]
    simp_rw [uniformWordAverage_sum,near_mean_at_index]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    rw [show (2 : ENNReal)^128=2^97*2^31 by rw [← pow_add]]
    ring
  rw [he]
  exact h
end SigGolfCandidate.T3.BPORS.History
end
