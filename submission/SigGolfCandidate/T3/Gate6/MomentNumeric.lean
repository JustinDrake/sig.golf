import SigGolfCandidate.T3.Gate6.BankMoments

namespace SigGolfResearch.Gate6.Moments.Numeric
open OracleComp OracleSpec ENNReal
open scoped BigOperators
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
def childCoefficients : List Nat := [0,1536,864,27]
def childSquareCoefficients : List Nat := [0,37748736,504889344,0xaf4a000,21109248,851472,11664]
def nearChildCoefficients : List Nat := [0,96,9]
def meanCoeffs : List Nat := [0,0x4458000000000000000,0x18438e6e23060000000000,0x51e93f9a5d51993f39516c0,0x35d2708af7f6ff4e4a96e940,0xc3fcd9d6f66c079baeb62360,0x14659717f87175719f2b78ee0,0x12335cfa3d63e7d20ec035b50,0x99ed4fba2a30d20673cc0b50,0x338f31f1a931a77ab9250c20,0xb793d30e52a125609abe150,0x1c11d8f2e3500aa7da22bd0,0x30533154e101d2e1ac90d0,0x3b7fe86dd9e1dbc6e7a6e,0x34e35d15239cbac5fe72,0x2208db69296fb163b95,0xfc85f0972b74ee705,0x532fa173d477c373,0x12ea774bce2ae00,0x2d038ef351d5e,0x3eddb916ac7,0x26f7c52b3]
def varianceCoeffs : List Nat := [0,0x123ede400000000000000000000000000000000000000,0x227c35f84275e0aae180000000000000000000000000000000000,0x27542eb77a71e82e309700713d4e558a000000000000000000000000,0x207eeb8469a11b8dd8d2242f623535e7709f9a00000000000000000000,0x554954ec123155638f775b953db5c4abdad3880e2c23708400000000000,0x4dbf9873e281edc7dfd6a530a0321e6a5cd8450aa415f0f7c00000000000,0x20ab487d06a46d60f5a8c6cb03df9283fd471b625326ceda2800000000000,0x77a411b2767b27baea41436059fe631ac0ed06e122067bb60400000000000,0x10a1430e00d654a780de1834979c536c64d75e11bcc6fbb64d880000000000,0x1839814fe69bc0a8642fbfd9203a9c254b4a38de8073b6c8d6780000000000,0x186d044e9f00bcd0c9b724b82400a79be7bbf7e3e200f42404580000000000,0x11c6b293119158f796edeefa4ec8cc1386401f8e73c64cb20b400000000000,0x9a58a1049daaa4ac5497c847747b5dc8f37d11970e5a61380bd0000000000,0x4019671c8300534c2bf6ed08d7a1d2fb48729f2fc87027b171b0000000000,0x14cdf1e0a2bc6cb095cffbb76eee70ec13a07c6111739fd9e8a0000000000,0x55e7cd6f15a9cd8a1a071d809c2d0c30dc490e37b3940b317d0000000000,0x11e1d225c52b3e4ebc710795ba94db813ddfaf3df5b6c6e5a1c000000000,0x309db4eebb87a741bcee4030783c0b9044c3b1364a638c05e4000000000,0x6cfa1b32bf5080fd82d5263c9016fc99f778b347c16295dec000000000,0xcb1ce41373dbdda41629d98687387cd8489da5dd8a078978000000000,0x13cfd95686c3f97bf0f9af136eb52ac221d9918001096d86000000000,0x1a0ae70944e8432aec35c36bc0f837ce1444dd94d89f596000000000,0x1cf8c75ac4c13ee7c312d92e44f8c3b7111bda2baaed69000000000,0x1b61d9049cd250f673423e01b137e1178649231b978e5000000000,0x160d46c6d1039897a55547fd3e4934eb0db1653d2988d80000000,0xf2a011e2b45d03296db5ce4b0a087835fd1ec62c12280000000,0x8ea44ba526a42158c39773a3254133a4403e91d78480000000,0x47b9a88ab1be86b5d740b18c586ea8a372585c64000000000,0x1ed4e40fe09029ca73a8514bd43345a8785eac8790000000,0xb5023ff2d973832426c528b4e451cc3e348134f0000000,0x388c8d238702dbf4ac1045bbf49a1574b8c9fa0000000,0xefbd06156273b3ffde2d0798ea3e92c50df10000000,0x3595e195bbac23d0712fe7475bd9eb3587b0000000,0xa0788237df51f0064ad3fe01388850efd0000000,0x18e6f490fefdf369e5c70024300e61400000000,0x3294c68eb55b91de60e5ea22baa2a80000000,0x52839d2e1a5674e9d97eabbb56b20000000,0x69522efb931f62fe8e672df4a80000000,0x652c0e11a88068197280a0f20000000,0x44b20587131cf4ebc3f8070000000,0x1d5b5b4807add038b5eb0000000,0x5ee7e56e3721f29290000000]
def nearCoeffs : List Nat := [0,0x445800000000000000,0x10faced9e551000000000,0x2ccd148330ca1ce52fb640,0x183a3624ed10cc82ba249c0,0x4aa1c80383fec5e84b3f320,0x6ad17b90e445c20419dc9a0,0x52b3e819af70dfc34427290,0x262076fbe8c9f1a8e7fe850,0xb296555782b98be20c83f0,0x22b75122f67f7cbe7e8740,0x49f94728e86bf5dddf870,0x6e4f51ec1346e59a8ee0,0x74a328ecfd2b887282e,0x57ef380a207efd2e72,0x2f2657c7928cdb789,0x11c1570213f04701,0x491ba8924efe70,0xc3284df9687f,0x12f5a9991fb,0xcfd41b91]
theorem mean_polynomial : factorialPolynomial childCoefficients^7=factorialPolynomial meanCoeffs := by
  norm_num [factorialPolynomial,childCoefficients,meanCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem variance_polynomial : factorialPolynomial childSquareCoefficients^7=factorialPolynomial varianceCoeffs := by
  norm_num [factorialPolynomial,childSquareCoefficients,varianceCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem near_polynomial : factorialPolynomial childCoefficients^6*factorialPolynomial nearChildCoefficients=
    factorialPolynomial nearCoeffs := by
  norm_num [factorialPolynomial,childCoefficients,nearChildCoefficients,nearCoeffs,Finset.sum_range_succ,
    descPochhammer_succ_right,descPochhammer_zero]
  ring
theorem envelope_power {a b : List Nat} (power count : Nat)
    (h : factorialPolynomial a^power=factorialPolynomial b) :
    envelope a count^power=envelope b count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) h
  rw [Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval] at he
  have hn : (natEnvelope a count)^power=natEnvelope b count := by exact_mod_cast he
  simp_rw [envelope_cast]
  exact_mod_cast hn
theorem mean_envelope_power (count : Nat) :
    envelope childCoefficients count^7=envelope meanCoeffs count :=
  envelope_power 7 count mean_polynomial
theorem variance_envelope_power (count : Nat) :
    envelope childSquareCoefficients count^7=envelope varianceCoeffs count :=
  envelope_power 7 count variance_polynomial
theorem firstMoment_coefficients (count : Nat) :
    firstMoment count=envelope childCoefficients count/2^12 := by
  unfold firstMoment envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [childCoefficients,Finset.sum_range_succ]
  ring
theorem secondMoment_coefficients (count : Nat) :
    (diagonalMoment count+15*crossMoment count)/16=envelope childSquareCoefficients count/2^28 := by
  unfold diagonalMoment crossMoment envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [fullCoefficients,squareCoefficients,childSquareCoefficients,Finset.sum_range_succ]
  ring
theorem firstMoment_power_coefficients (count : Nat) :
    firstMoment count^7=envelope meanCoeffs count/2^84 := by
  rw [firstMoment_coefficients,div_eq_mul_inv,mul_pow,mean_envelope_power,div_eq_mul_inv,
    ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul]
theorem secondMoment_power_coefficients (count : Nat) :
    ((diagonalMoment count+15*crossMoment count)/16)^7=envelope varianceCoeffs count/2^196 := by
  rw [secondMoment_coefficients,div_eq_mul_inv,mul_pow,variance_envelope_power,div_eq_mul_inv,
    ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul]
theorem binomial_envelope_le_poisson (p : ENNReal) (hp : p≤1) (trials : Nat) (a : List Nat) :
    SphincsSecurity.Concrete.binomialAverage p trials (envelope a) ≤
      ∑ degree ∈ Finset.range a.length, (a.getD degree 0 : ENNReal)*((trials : ENNReal)*p)^degree := by
  rw [envelope_thinning p hp]
  apply Finset.sum_le_sum
  intro degree _
  calc
    _ ≤ (a.getD degree 0 : ENNReal)*(trials : ENNReal)^degree*p^degree := by
      gcongr
      exact_mod_cast Nat.descFactorial_le_pow trials degree
    _ = _ := by rw [mul_pow,mul_assoc]
open OracleComp.EvalDist SphincsSecurity.Concrete
noncomputable def forestEnvelope {steps : Nat} (table : Fin 7 → Fin steps → Fin 16) : ENNReal :=
  (∏ c, coordinateEnvelope (List.ofFn (table c)))/2^150
theorem forest_first_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope =
      envelope meanCoeffs steps/2^234 := by
  change expectedValue _ (fun table => forestEnvelope table)=_
  simp only [forestEnvelope,div_eq_mul_inv]
  rw [expectedValue_mul_const,seven_coordinate_first_moment,firstMoment_power_coefficients,
    div_eq_mul_inv,ENNReal.inv_pow,ENNReal.inv_pow,ENNReal.inv_pow,mul_assoc,← pow_add]
theorem forest_second_moment (steps : Nat) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
      (fun table => forestEnvelope table^2)=envelope varianceCoeffs steps/2^496 := by
  simp only [forestEnvelope,div_eq_mul_inv,mul_pow]
  rw [expectedValue_mul_const,seven_coordinate_second_moment,secondMoment_power_coefficients,
    div_eq_mul_inv,ENNReal.inv_pow,ENNReal.inv_pow,ENNReal.inv_pow,← pow_mul,mul_assoc,← pow_add]
noncomputable def poissonEnvelope (a : List Nat) (mean : ENNReal) : ENNReal :=
  ∑ degree ∈ Finset.range a.length, (a.getD degree 0 : ENNReal)*mean^degree
theorem forest_binomial_first_bound (p : ENNReal) (hp : p≤1) (trials : Nat) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope) ≤
        poissonEnvelope meanCoeffs ((trials : ENNReal)*p)/2^234 := by
  simp_rw [forest_first_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials meanCoeffs) le_rfl
theorem forest_binomial_second_bound (p : ENNReal) (hp : p≤1) (trials : Nat) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _)
        (fun table => forestEnvelope table^2)) ≤
        poissonEnvelope varianceCoeffs ((trials : ENNReal)*p)/2^496 := by
  simp_rw [forest_second_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials varianceCoeffs) le_rfl
def proposalLength : Nat := 4303355904
theorem poisson_mean_bound :
    (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 ≤ 37/64 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_excess_bound :
    (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/2^496 ≤ 18400/100000000 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [varianceCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_near_bound :
    21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 ≤ 404 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [nearCoeffs,proposalLength,Finset.sum_range_succ]
theorem poisson_near_tight_bound :
    21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 ≤ 6463/16 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [nearCoeffs,proposalLength,Finset.sum_range_succ]
noncomputable def nearCoordinateEnvelope (word : List (Fin 16)) : ENNReal :=
  (∑ bucket : Fin 16, ((3*word.count bucket).descFactorial 2 : ENNReal))/16
theorem near_coordinate_first_moment (steps : Nat) :
    uniformWordAverage steps nearCoordinateEnvelope=envelope nearChildCoefficients steps/2^8 := by
  change uniformWordAverage steps (fun word => nearCoordinateEnvelope word)=_
  simp only [nearCoordinateEnvelope,ENNReal.div_eq_inv_mul]
  rw [uniformWordAverage_mul_left]
  simp_rw [uniformWordAverage_sum]
  have hb (bucket : Fin 16) : uniformWordAverage steps
      (fun word => ((3*word.count bucket).descFactorial 2 : ENNReal))=
      6*(steps.descFactorial 1 : ENNReal)*(1/16)+9*(steps.descFactorial 2 : ENNReal)*(1/16)^2 := by
    unfold uniformWordAverage
    rw [expected_uniformProposalWord_count bucket steps (fun count => ((3*count).descFactorial 2 : ENNReal))]
    simpa only [Fintype.card_fin,Nat.cast_ofNat,one_div] using
      near_bucket_thinning (1/16) (by norm_num) steps
  simp_rw [hb]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  rw [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by finiteness),one_mul]
  unfold envelope
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one,
    ENNReal.toReal_inv]
  norm_num [nearChildCoefficients,Finset.sum_range_succ]
  ring
noncomputable def nearForestEnvelope {steps : Nat} (missing : Fin 7)
    (table : Fin 7 → Fin steps → Fin 16) : ENNReal :=
  (∏ c, if c=missing then nearCoordinateEnvelope (List.ofFn (table c))
    else coordinateEnvelope (List.ofFn (table c)))/2^143
theorem near_envelope_product (count : Nat) :
    envelope childCoefficients count^6*envelope nearChildCoefficients count=envelope nearCoeffs count := by
  have he := congrArg (fun p : Polynomial Int => p.eval (count : Int)) near_polynomial
  rw [Polynomial.eval_mul,Polynomial.eval_pow,factorialPolynomial_eval,factorialPolynomial_eval,
    factorialPolynomial_eval] at he
  have hn : (natEnvelope childCoefficients count)^6*natEnvelope nearChildCoefficients count=
      natEnvelope nearCoeffs count := by exact_mod_cast he
  simp_rw [envelope_cast]
  exact_mod_cast hn
theorem near_forest_first_moment (steps : Nat) (missing : Fin 7) :
    expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)=
      envelope nearCoeffs steps/2^223 := by
  change expectedValue _ (fun table => nearForestEnvelope missing table)=_
  simp only [nearForestEnvelope,div_eq_mul_inv]
  rw [expectedValue_mul_const,uniform_coordinate_product steps (fun c word =>
    if c=missing then nearCoordinateEnvelope (List.ofFn word) else coordinateEnvelope (List.ofFn word))]
  have he (c : Fin 7) : expectedValue ($ᵗ (Fin steps → Fin 16) : ProbComp _)
      (fun word => if c=missing then nearCoordinateEnvelope (List.ofFn word)
        else coordinateEnvelope (List.ofFn word)) =
      if c=missing then envelope nearChildCoefficients steps/2^8 else firstMoment steps := by
    by_cases h : c=missing
    · simp only [h,ite_true]
      rw [expected_uniform_eq_finiteAverage,← word_array_average steps nearCoordinateEnvelope,
        near_coordinate_first_moment]
    · simp only [h,ite_false]
      rw [expected_uniform_eq_finiteAverage,← word_array_average steps coordinateEnvelope,
        coordinate_first_moment]
  simp_rw [he]
  rw [Finset.prod_ite]
  have hy : (Finset.univ.filter fun c : Fin 7 => c=missing)={missing} := by ext c;simp
  have hn : (Finset.univ.filter fun c : Fin 7 => ¬c=missing)=Finset.univ.erase missing := by ext c;simp [eq_comm]
  rw [hy,hn,Finset.prod_singleton,Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ missing)]
  simp only [Finset.card_univ,Fintype.card_fin]
  rw [firstMoment_coefficients]
  simp only [div_eq_mul_inv,mul_pow,ENNReal.inv_pow,← pow_mul]
  calc
    _ = (envelope childCoefficients steps^6*envelope nearChildCoefficients steps)*
      ((2 : ENNReal)⁻¹^(12*6)*2⁻¹^8*2⁻¹^143) := by ring
    _ = _ := by rw [near_envelope_product,← pow_add,← pow_add]
theorem near_forest_binomial_bound (p : ENNReal) (hp : p≤1) (trials : Nat) (missing : Fin 7) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤
        poissonEnvelope nearCoeffs ((trials : ENNReal)*p)/2^223 := by
  simp_rw [near_forest_first_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials nearCoeffs) le_rfl
theorem uniform_history_mean_bound :
    (2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope) ≤ 37/64 := by
  calc
    _ ≤ (2 : ENNReal)^128*(poissonEnvelope meanCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^234) :=
      mul_le_mul' le_rfl (forest_binomial_first_bound (1/2^31) (by norm_num) proposalLength)
    _ = (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_mean_bound
theorem uniform_history_excess_bound :
    (2 : ENNReal)^225*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (fun table => forestEnvelope table^2)) ≤
        18400/100000000 := by
  calc
    _ ≤ (2 : ENNReal)^225*(poissonEnvelope varianceCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^496) :=
      mul_le_mul' le_rfl (forest_binomial_second_bound (1/2^31) (by norm_num) proposalLength)
    _ = (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/2^496 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_excess_bound
theorem uniform_history_near_bound (missing : Fin 7) :
    21*(2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤ 404 := by
  calc
    _ ≤ 21*(2 : ENNReal)^128*(poissonEnvelope nearCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^223) :=
      mul_le_mul' le_rfl (near_forest_binomial_bound (1/2^31) (by norm_num) proposalLength missing)
    _ = 21*(2 : ENNReal)^128*poissonEnvelope nearCoeffs (proposalLength/2^31)/2^223 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_near_bound
end SigGolfResearch.Gate6.Moments.Numeric
