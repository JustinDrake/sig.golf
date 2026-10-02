import SigGolfCandidate.T3.Gate6.FreshProbability
import Mathlib.RingTheory.Polynomial.Pochhammer
import SigGolfCandidate.SphincsSecurity.Proof.Base.BinomialMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalMixedMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.UniformProposalVariance
namespace SigGolfResearch.Gate6.Moments
open OracleComp OracleSpec ENNReal
open scoped BigOperators
open SphincsSecurity.Concrete (binomialAverage binomialAverage_add binomialAverage_mul_left
  binomialAverage_descFactorial)
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Distinct sampled leaves must all belong to the exposed set. -/
def Covered {k n : Nat} (exposed : Finset (Fin n)) (draw : Fin k → Fin n) : Prop :=
  Function.Injective draw ∧ ∀ i, draw i ∈ exposed

noncomputable def coveredEquiv {k n : Nat} (exposed : Finset (Fin n)) :
    {draw : Fin k → Fin n // Covered exposed draw} ≃ (Fin k ↪ exposed) where
  toFun draw := ⟨fun i => ⟨draw.1 i,draw.2.2 i⟩,fun _i _j h => draw.2.1 (congrArg Subtype.val h)⟩
  invFun embedding := ⟨fun i => (embedding i).val,
    fun _i _j h => embedding.injective (Subtype.ext h),fun i => (embedding i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Credits the distinctness check exactly, including exposed sets smaller
than the number of requested openings. -/
theorem covered_count (k n : Nat) (exposed : Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin k → Fin n => Covered exposed draw).card =
      exposed.card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (coveredEquiv exposed),Fintype.card_embedding_eq]
  simp only [Fintype.card_fin,Fintype.card_coe]

theorem covered_probability (k n : Nat) [NeZero n] (exposed : Finset (Fin n)) :
    Pr[Covered exposed | ($ᵗ (Fin k → Fin n) : ProbComp _)] =
      (exposed.card.descFactorial k : ENNReal)/(n : ENNReal)^k := by
  classical
  rw [probEvent_uniformSample,covered_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]

theorem covered_probability_le (k n r : Nat) [NeZero n]
    (exposed : Finset (Fin n)) (hsize : exposed.card≤k*r) :
    Pr[Covered exposed | ($ᵗ (Fin k → Fin n) : ProbComp _)] ≤
      ((k*r).descFactorial k : ENNReal)/(n : ENNReal)^k := by
  rw [covered_probability k n]
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.descFactorial_le k hsize

/-- Independent coordinate draws multiply even when each coordinate's exposed
set is different. No independence assumption about how those sets were chosen
is made by this fixed-set statement. -/
theorem covered_product_count {d k n : Nat} (exposed : Fin d → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin d → (Fin k → Fin n) =>
      ∀ c, Covered (exposed c) (draw c)).card =
        ∏ c, (exposed c).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr Equiv.subtypePiEquivPi,Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fintype.card_subtype,covered_count]

/-- Positive falling-factorial coefficients used by the three-opening closer. -/
theorem three_openings_polynomial (r : Nat) :
    (3*r).descFactorial 3 =
      6*r.descFactorial 1+54*r.descFactorial 2+27*r.descFactorial 3 := by
  rcases r with _|_|r
  · decide
  · decide
  · simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]
    rw [show 3*(r+1+1)-2=3*r+4 by omega,show 3*(r+1+1)-1=3*r+5 by omega,
      show r+1+1-2=r by omega]
    ring

theorem two_openings_polynomial (r : Nat) :
    (3*r).descFactorial 2 = 6*r.descFactorial 1+9*r.descFactorial 2 := by
  rcases r with _|r
  · decide
  · simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.mul_one]
    simp only [Nat.sub_zero,Nat.add_sub_cancel]
    rw [show 3*(r+1)-1=3*r+2 by omega]
    ring

/-- Exact binomial thinning for the three-opening cover envelope. -/
theorem bucket_thinning (p : ENNReal) (hp : p≤1) (r : Nat) :
    binomialAverage p r (fun count => ((3*count).descFactorial 3 : ENNReal)) =
      6*(r.descFactorial 1 : ENNReal)*p+
      54*(r.descFactorial 2 : ENNReal)*p^2+
      27*(r.descFactorial 3 : ENNReal)*p^3 := by
  simp_rw [three_openings_polynomial,Nat.cast_add,Nat.cast_mul]
  rw [binomialAverage_add,binomialAverage_add]
  simp_rw [binomialAverage_mul_left,binomialAverage_descFactorial hp]
  norm_num only [Nat.cast_ofNat,pow_one]
  ring

theorem near_bucket_thinning (p : ENNReal) (hp : p≤1) (r : Nat) :
    binomialAverage p r (fun count => ((3*count).descFactorial 2 : ENNReal)) =
      6*(r.descFactorial 1 : ENNReal)*p+9*(r.descFactorial 2 : ENNReal)*p^2 := by
  simp_rw [two_openings_polynomial,Nat.cast_add,Nat.cast_mul]
  rw [binomialAverage_add]
  simp_rw [binomialAverage_mul_left,binomialAverage_descFactorial hp]
  norm_num only [Nat.cast_ofNat,pow_one]
  ring


noncomputable def bucketCoveredEquiv {b k n : Nat} (exposed : Fin b → Finset (Fin n)) :
    {draw : Fin b × (Fin k → Fin n) // Covered (exposed draw.1) draw.2} ≃
      (bucket : Fin b) × {draw : Fin k → Fin n // Covered (exposed bucket) draw} where
  toFun draw := ⟨draw.1.1,draw.1.2,draw.2⟩
  invFun draw := ⟨(draw.1,draw.2.1),draw.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem bucket_covered_count {b k n : Nat} (exposed : Fin b → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin b × (Fin k → Fin n) =>
      Covered (exposed draw.1) draw.2).card = ∑ bucket, (exposed bucket).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (bucketCoveredEquiv exposed),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro bucket _
  rw [Fintype.card_subtype,covered_count]

theorem bucket_covered_probability {b k n : Nat} [NeZero b] [NeZero n]
    (exposed : Fin b → Finset (Fin n)) :
    Pr[fun draw : Fin b × (Fin k → Fin n) => Covered (exposed draw.1) draw.2 |
      ($ᵗ (Fin b × (Fin k → Fin n)) : ProbComp _)] =
      (∑ bucket, ((exposed bucket).card.descFactorial k : ENNReal))/
        ((b : ENNReal)*(n : ENNReal)^k) := by
  classical
  rw [probEvent_uniformSample,bucket_covered_count]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.cast_sum]

theorem bucket_product_count {d b k n : Nat} (exposed : Fin d → Fin b → Finset (Fin n)) :
    (Finset.univ.filter fun draw : Fin d → (Fin b × (Fin k → Fin n)) =>
      ∀ c, Covered (exposed c (draw c).1) (draw c).2).card =
        ∏ c, ∑ bucket, (exposed c bucket).card.descFactorial k := by
  classical
  rw [← Fintype.card_subtype,Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (c : Fin d) (draw : Fin b × (Fin k → Fin n)) => Covered (exposed c draw.1) draw.2)),Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c _
  rw [Fintype.card_subtype,bucket_covered_count]

/-- Exact seven-coordinate fixed-exposure coverage, averaged over the eight
bucket choices in each coordinate. Admissibility can only decrease this event. -/
theorem bpors_covered_probability (exposed : Fin 7 → Fin 16 → Finset (Fin 128)) :
    Pr[fun draw : Fin 7 → (Fin 16 × (Fin 3 → Fin 128)) =>
      ∀ c, Covered (exposed c (draw c).1) (draw c).2 |
      ($ᵗ (Fin 7 → (Fin 16 × (Fin 3 → Fin 128))) : ProbComp _)] =
        ∏ c : Fin 7, ((∑ bucket : Fin 16, ((exposed c bucket).card.descFactorial 3 : ENNReal))/(16*128^3)) := by
  classical
  rw [probEvent_uniformSample,bucket_product_count]
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin,Nat.cast_pow,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_prod,Nat.cast_sum,div_eq_mul_inv,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,ENNReal.inv_pow]

/-- A nonnegative falling-factorial envelope. -/
noncomputable def envelope (coefficients : List Nat) (count : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range coefficients.length,
    (coefficients.getD degree 0 : ENNReal)*count.descFactorial degree

/-- Exact multinomial cross moment for two different buckets. The shared
number of trials appears as `(r)_(i+j)`, rather than a product of marginal
moments. This is the cross term in T3's variance calculation. -/
theorem distinct_bucket_cross_moment {α : Type} [SampleableType α] [Fintype α] [DecidableEq α]
    (first second : α) (hdistinct : first≠second) (steps : Nat) (a b : List Nat) :
    SphincsSecurity.Concrete.uniformWordAverage steps (fun word : List α =>
      envelope a (word.count first)*envelope b (word.count second)) =
      ∑ i ∈ Finset.range a.length, ∑ j ∈ Finset.range b.length,
        ((a.getD i 0 : ENNReal)*b.getD j 0)*
          ((steps.descFactorial (i+j) : ENNReal)*(Fintype.card α : ENNReal)⁻¹^(i+j)) := by
  simp only [envelope,Finset.sum_mul,Finset.mul_sum,
    SphincsSecurity.Concrete.uniformWordAverage_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun word : List α =>
      ((a.getD i 0 : ENNReal)*(word.count first).descFactorial i)*
        ((b.getD j 0 : ENNReal)*(word.count second).descFactorial j)) =
      (fun word : List α => ((a.getD i 0 : ENNReal)*b.getD j 0)*
        ((word.count first).descFactorial i*(word.count second).descFactorial j)) := by
    funext word;ring
  rw [he,SphincsSecurity.Concrete.uniformWordAverage_mul_left,
    SphincsSecurity.Concrete.uniformWordAverage_mixed_descFactorial first second hdistinct]


def natEnvelope (coefficients : List Nat) (count : Nat) : Nat :=
  ∑ degree ∈ Finset.range coefficients.length, coefficients.getD degree 0*count.descFactorial degree

noncomputable def factorialPolynomial (coefficients : List Nat) : Polynomial Int :=
  ∑ degree ∈ Finset.range coefficients.length,
    Polynomial.C (coefficients.getD degree 0 : Int)*descPochhammer Int degree

theorem envelope_cast (coefficients : List Nat) (count : Nat) :
    envelope coefficients count=(natEnvelope coefficients count : ENNReal) := by
  simp only [envelope,natEnvelope,Nat.cast_sum,Nat.cast_mul]

theorem factorialPolynomial_eval (coefficients : List Nat) (count : Nat) :
    (factorialPolynomial coefficients).eval (count : Int)=(natEnvelope coefficients count : Int) := by
  simp only [factorialPolynomial,natEnvelope,Polynomial.eval_finsetSum,Polynomial.eval_mul,
    Polynomial.eval_C,descPochhammer_eval_eq_descFactorial,Nat.cast_sum,Nat.cast_mul]

def fullCoefficients : List Nat := [0,6,54,27]
def squareCoefficients : List Nat := [0,36,7164,35154,33858,9477,729]

theorem full_envelope (count : Nat) :
    natEnvelope fullCoefficients count=(3*count).descFactorial 3 := by
  rw [three_openings_polynomial]
  norm_num [natEnvelope,fullCoefficients,Finset.sum_range_succ]

/-- Exact same-bucket diagonal term; coefficients remain nonnegative. -/
theorem square_polynomial :
    factorialPolynomial fullCoefficients^2=factorialPolynomial squareCoefficients := by
  norm_num [factorialPolynomial,fullCoefficients,squareCoefficients,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring

theorem full_square_envelope (count : Nat) :
    ((3*count).descFactorial 3 : ENNReal)^2=envelope squareCoefficients count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) square_polynomial
  rw [Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval] at he
  have hn : (natEnvelope fullCoefficients count)^2=natEnvelope squareCoefficients count := by
    exact_mod_cast he
  rw [full_envelope] at hn
  rw [envelope_cast]
  exact_mod_cast hn

theorem envelope_thinning (p : ENNReal) (hp : p≤1) (steps : Nat) (coefficients : List Nat) :
    binomialAverage p steps (envelope coefficients) =
      ∑ degree ∈ Finset.range coefficients.length,
        (coefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*p^degree := by
  change binomialAverage p steps (fun count => envelope coefficients count)=_
  simp only [envelope,SphincsSecurity.Concrete.binomialAverage_sum,
    binomialAverage_mul_left,binomialAverage_descFactorial hp,mul_assoc]

theorem same_bucket_second_moment (steps : Nat) :
    binomialAverage (1/16) steps (fun count => ((3*count).descFactorial 3 : ENNReal)^2) =
      ∑ degree ∈ Finset.range squareCoefficients.length,
        (squareCoefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*(1/16)^degree := by
  simp_rw [full_square_envelope]
  exact envelope_thinning (1/16) (by norm_num) steps squareCoefficients

/-- The cross-bucket formula instantiated at BPORS's eight buckets. -/
theorem different_bucket_second_moment (first second : Fin 16) (hne : first≠second) (steps : Nat) :
    SphincsSecurity.Concrete.uniformWordAverage steps (fun word : List (Fin 16) =>
      ((3*word.count first).descFactorial 3 : ENNReal)*
        (3*word.count second).descFactorial 3) =
      ∑ i ∈ Finset.range fullCoefficients.length, ∑ j ∈ Finset.range fullCoefficients.length,
        ((fullCoefficients.getD i 0 : ENNReal)*fullCoefficients.getD j 0)*
          ((steps.descFactorial (i+j) : ENNReal)*(1/16)^(i+j)) := by
  have he := distinct_bucket_cross_moment first second hne steps fullCoefficients fullCoefficients
  simpa only [envelope_cast,full_envelope,Fintype.card_fin,Nat.cast_ofNat,one_div] using he


open SphincsSecurity.Concrete (uniformWordAverage uniformWordAverage_sum uniformWordAverage_mul_left)

noncomputable def diagonalMoment (steps : Nat) : ENNReal :=
  ∑ degree ∈ Finset.range squareCoefficients.length,
    (squareCoefficients.getD degree 0 : ENNReal)*(steps.descFactorial degree : ENNReal)*(1/16)^degree

noncomputable def crossMoment (steps : Nat) : ENNReal :=
  ∑ i ∈ Finset.range fullCoefficients.length, ∑ j ∈ Finset.range fullCoefficients.length,
    ((fullCoefficients.getD i 0 : ENNReal)*fullCoefficients.getD j 0)*
      ((steps.descFactorial (i+j) : ENNReal)*(1/16)^(i+j))

noncomputable def bucketMass (word : List (Fin 16)) (bucket : Fin 16) : ENNReal :=
  (3*word.count bucket).descFactorial 3

noncomputable def coordinateEnvelope (word : List (Fin 16)) : ENNReal :=
  (∑ bucket, bucketMass word bucket)/16

theorem bucket_pair_moment (steps : Nat) (a b : Fin 16) :
    uniformWordAverage steps (fun word => bucketMass word a*bucketMass word b)=
      if a=b then diagonalMoment steps else crossMoment steps := by
  classical
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl]
    simp only [bucketMass,← pow_two,uniformWordAverage]
    rw [SphincsSecurity.Concrete.expected_uniformProposalWord_count a steps
      (fun count => ((3*count).descFactorial 3 : ENNReal)^2)]
    simpa only [Fintype.card_fin,Nat.cast_ofNat,one_div,diagonalMoment] using same_bucket_second_moment steps
  · rw [if_neg hab]
    exact different_bucket_second_moment a b hab steps

/-- Exact diagonal/cross mixture for a uniform choice among eight buckets. -/
theorem coordinate_second_moment (steps : Nat) :
    uniformWordAverage steps (fun word => coordinateEnvelope word^2)=
      (diagonalMoment steps+15*crossMoment steps)/16 := by
  classical
  have hpoint (word : List (Fin 16)) : coordinateEnvelope word^2=
      (16 : ENNReal)⁻¹^2*(∑ a : Fin 16, ∑ b : Fin 16, bucketMass word a*bucketMass word b) := by
    unfold coordinateEnvelope
    calc
      _ = (16 : ENNReal)⁻¹^2*((∑ a : Fin 16, bucketMass word a)*(∑ b : Fin 16, bucketMass word b)) := by
        rw [div_eq_mul_inv];ring
      _ = _ := by
        congr 1
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
  simp_rw [hpoint]
  rw [uniformWordAverage_mul_left]
  simp_rw [uniformWordAverage_sum,bucket_pair_moment]
  have hrow (a : Fin 16) :
      (∑ b : Fin 16, if a=b then diagonalMoment steps else crossMoment steps)=
        diagonalMoment steps+15*crossMoment steps := by
    rw [Finset.sum_ite]
    have hy : (Finset.univ.filter fun b : Fin 16 => a=b)={a} := by ext b;simp [eq_comm]
    have hn : (Finset.univ.filter fun b : Fin 16 => ¬a=b)=Finset.univ.erase a := by ext b;simp [eq_comm]
    rw [hy,hn,Finset.sum_singleton,Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ a)]
    norm_num only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hrow]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,div_eq_mul_inv,Nat.cast_ofNat]
  have he : (16 : ENNReal)⁻¹^2*16=16⁻¹ := by
    rw [pow_two,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),mul_one]
  rw [← mul_assoc,he]
  ring

open OracleComp.EvalDist
noncomputable def finiteAverage {α : Type} [Fintype α] (f : α → ENNReal) : ENNReal :=
  (∑ x, f x)/(Fintype.card α : ENNReal)

theorem expected_uniform_eq_finiteAverage {α : Type} [Fintype α] [SampleableType α]
    (f : α → ENNReal) : expectedValue ($ᵗ α : ProbComp α) f=finiteAverage f := by
  simp only [expectedValue_def,probOutput_uniformSample,tsum_fintype,finiteAverage,
    div_eq_mul_inv,← Finset.mul_sum]
  exact mul_comm _ _

theorem finiteAverage_product {α : Type} [Fintype α] (d : Nat) (f : Fin d → α → ENNReal) :
    finiteAverage (fun x : Fin d → α => ∏ i, f i (x i))=∏ i, finiteAverage (f i) := by
  simp only [finiteAverage,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,div_eq_mul_inv,
    ENNReal.inv_pow,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Fintype.prod_sum]

/-- Conditional on the shared number of proposals, the coordinate tables are
independent. This identity applies equally to first and second moments. -/
theorem uniform_coordinate_product (steps : Nat) (f : Fin 7 → (Fin steps → Fin 16) → ENNReal) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => ∏ c, f c (table c))=
      ∏ c, expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _) (f c) := by
  simp_rw [expected_uniform_eq_finiteAverage]
  exact finiteAverage_product 7 f


theorem finiteAverage_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ENNReal) :
    finiteAverage (fun x => f (e x))=finiteAverage f := by
  unfold finiteAverage
  rw [Fintype.card_congr e,Equiv.sum_comp]

theorem finiteAverage_pair {α β : Type} [Fintype α] [Fintype β] (f : α × β → ENNReal) :
    finiteAverage f=finiteAverage (fun a => finiteAverage (fun b => f (a,b))) := by
  simp only [finiteAverage,Fintype.card_prod,Nat.cast_mul,div_eq_mul_inv,Fintype.sum_prod_type]
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.sum_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

open SphincsSecurity.Concrete (uniformWordAverage sampleUniformProposalWord)

theorem uniformWordAverage_succ {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (f : List α → ENNReal) :
    uniformWordAverage (steps+1) f =
      finiteAverage (fun a => uniformWordAverage steps (fun word => f (a::word))) := by
  change expectedValue (sampleUniformProposalWord α (steps+1)) f=_
  rw [sampleUniformProposalWord,expectedValue_bind]
  simp_rw [expectedValue_bind,expectedValue_pure]
  exact expected_uniform_eq_finiteAverage _

/-- Uniform finite arrays and the recursive proposal-word sampler have the
same averages for every payoff, not just for the selected polynomial moments. -/
theorem word_array_average {α : Type} [Fintype α] [SampleableType α]
    (steps : Nat) (f : List α → ENNReal) :
    uniformWordAverage steps f=finiteAverage (fun word : Fin steps → α => f (List.ofFn word)) := by
  classical
  induction steps generalizing f with
  | zero =>
      simp [uniformWordAverage,sampleUniformProposalWord,finiteAverage]
  | succ steps ih =>
      rw [uniformWordAverage_succ]
      simp_rw [ih]
      rw [← finiteAverage_equiv (Fin.consEquiv (fun _ : Fin (steps+1) => α))]
      rw [finiteAverage_pair]
      congr 1
      funext a
      congr 1
      funext word
      simp [Fin.consEquiv,List.ofFn_succ]

/-- Seven independently sampled coordinate histories give the seventh power
of the exact one-coordinate second moment. -/
theorem seven_coordinate_second_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => (∏ c, coordinateEnvelope (List.ofFn (table c)))^2)=
        ((diagonalMoment steps+15*crossMoment steps)/16)^7 := by
  simp_rw [← Finset.prod_pow]
  rw [uniform_coordinate_product steps (fun _ word => coordinateEnvelope (List.ofFn word)^2)]
  have hcolumn : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => coordinateEnvelope (List.ofFn word)^2)=
        (diagonalMoment steps+15*crossMoment steps)/16 := by
    rw [expected_uniform_eq_finiteAverage,← word_array_average steps (fun word => coordinateEnvelope word^2)]
    exact coordinate_second_moment steps
  simp_rw [hcolumn]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]


noncomputable def firstMoment (steps : Nat) : ENNReal :=
  6*(steps.descFactorial 1 : ENNReal)*(1/16)+
    54*(steps.descFactorial 2 : ENNReal)*(1/16)^2+
    27*(steps.descFactorial 3 : ENNReal)*(1/16)^3

theorem bucket_first_moment (steps : Nat) (bucket : Fin 16) :
    uniformWordAverage steps (fun word => bucketMass word bucket)=firstMoment steps := by
  unfold uniformWordAverage bucketMass
  rw [SphincsSecurity.Concrete.expected_uniformProposalWord_count bucket steps
    (fun count => ((3*count).descFactorial 3 : ENNReal))]
  simpa only [firstMoment,Fintype.card_fin,Nat.cast_ofNat,one_div] using
    bucket_thinning (1/16) (by norm_num) steps

theorem coordinate_first_moment (steps : Nat) :
    uniformWordAverage steps coordinateEnvelope=firstMoment steps := by
  change uniformWordAverage steps (fun word => coordinateEnvelope word)=_
  simp only [coordinateEnvelope,ENNReal.div_eq_inv_mul]
  rw [SphincsSecurity.Concrete.uniformWordAverage_mul_left]
  simp_rw [SphincsSecurity.Concrete.uniformWordAverage_sum,bucket_first_moment]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  rw [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),one_mul]

theorem seven_coordinate_first_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → (Fin steps → Fin 16)) : ProbComp _)
      (fun table => ∏ c, coordinateEnvelope (List.ofFn (table c)))=firstMoment steps^7 := by
  rw [uniform_coordinate_product steps (fun _ word => coordinateEnvelope (List.ofFn word))]
  have hcolumn : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => coordinateEnvelope (List.ofFn word))=firstMoment steps := by
    rw [expected_uniform_eq_finiteAverage,← word_array_average steps coordinateEnvelope]
    exact coordinate_first_moment steps
  simp_rw [hcolumn]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]


end SigGolfResearch.Gate6.Moments
