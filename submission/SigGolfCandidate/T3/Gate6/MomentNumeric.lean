import SigGolfCandidate.T3.Gate6.BankMoments
namespace SigGolfResearch.Gate6.Moments.Numeric
open OracleComp OracleSpec ENNReal
open scoped BigOperators
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

def childCoefficients : List Nat := [0, 1536, 864, 27]
def childSquareCoefficients : List Nat := [0, 37748736, 504889344, 183803904, 21109248, 851472, 11664]
def nearChildCoefficients : List Nat := [0, 96, 9]
def meanCoeffs : List Nat := [0, 20171514644601394692096, 29333245598955398605307904, 1584391616756905719924856512, 16657111411214873624646707520, 60655254940591765236261200736, 101000243579587600920392208096, 90125191478570142529411570512, 47638098423001167714874821456, 15956847746908182665366932512, 3550904098520367616974643536, 542947282848942491382721488, 58421305766211766893449424, 4495665716301176312330862, 249757175320329712959090, 10045240286480260545429, 291139430424322696965, 5994187147911349107, 85189562793635328, 791892903402846, 4320125872839, 10460353203]
def varianceCoeffs : List Nat := [0, 109223703512546115621527503760190116847511187799146496, 886649239276143447340565785216092982023171105504826445480853504, 4141810041639470511958611218545784300179713410449115123687394115584, 876084528270669171881319501116722319428932091227163101129481018933248, 36789091183150219743964290947920231155262889063683698868364634878902272, 536599873656872402003958243723788820893937317861604383714513470743379968, 3607578686321153726675155793497207285742045759246626014311724657521197056, 13211697763932683341008653312904561212012797103081433879406224759249174528, 29382541989430628620964953524649434060425346548823851787899804769457274880, 42801215344106187069740843593780514985577652744260466348807784299734499328, 43156736026036805480959119711956030839304570944407334944201574675006881792, 31407760236537652165481972484360390189425069588998451082152149359941124096, 17044133918244475081809615581030565986338226826474630204530488262378127360, 7078345980101752596434754223495018600353300513876502612482983041601372160, 2297395018794099400610249392065759813523794181049056568378265292630917120, 592897821874664808546868450532303328583292276647714023335036354297856000, 123417807014554268441192736798614562923723505152716792787902926359101440, 20970974418378758580327512670202621838688579542647404054526648217763840, 2938013501672972906154056877440534909715048263289824059040949338112000, 342244483913571713883847569112234511790856242687369033523876922916864, 33383002419756055619325864707391027507322563520122439544850188599296, 2742604605647530778697348729354532226779597440241897481270401695744, 190692862481743437832067261041819061254251107387220836891580432384, 11264390996388076544994649619691412191403418991065716791944675328, 566975595745557442877213989492949187796336312204421888898760704, 24367736346319129937947368810961126816032915819585166116913152, 895376960087291810902395729849317418757329039977223391543296, 28139159569268737681667888583640864730420944135969264631808, 755988753664220849957953114504228049841638932874432348160, 17337197555911923764732811009536867203301375038665523200, 338520055391808804651585883245620860436320747914264576, 5606048419921634666559787480061331728614464480608256, 78315257114652495763978982690052405097737624748032, 916125956365182595520376443993206355864724701184, 8885390914550304816853157615204584403641565184, 70499840240320025526838838897500531149766656, 449249585290385583923130890268781389545472, 2239930573159341155350764719051831771136, 8405048374300872824703110320194846720, 22292930827138344256703489032323072, 37214243219344506732316006023168, 29371936242576564113903714304]
def nearCoeffs : List Nat := [0, 1260719665287587168256, 1282951279054712412831744, 54161199580191278450587200, 468625851387823125273135552, 1443592020117847099841966880, 2066166253826208806236703136, 1599704036868487002619802256, 737479867849420366202005584, 215898725142887143907820528, 41969167638873722796803904, 5589297922041022789843056, 520923509011890824711904, 34425267519194558572590, 1622104273121177316978, 54359991737062897545, 1279399435585996545, 20578084122984048, 214577874299007, 1302895104507, 3486784401]

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

/-- The Poisson substitution is a bound on every falling-factorial term;
there is no truncated distribution or omitted tail. -/
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

/-- Probability envelope after the 21 independent seven-bit leaves and four-bit gate. -/
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



/-- Number of padded raw proposals used in the T3 numerical envelope. -/
def proposalLength : Nat := 4303355904

/-- Concrete arithmetic for the mean polynomial, after leaf normalization. -/
theorem poisson_mean_bound :
    (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 ≤ 5 / 8 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [meanCoeffs,proposalLength,Finset.sum_range_succ]

/-- Concrete arithmetic for the normalized second-moment excess term. -/
theorem poisson_excess_bound :
    (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/(1*2^496) ≤ 18400/100000000 := by
  unfold poissonEnvelope
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_pow,ENNReal.toReal_sum,ENNReal.toReal_natCast,ENNReal.toReal_ofNat,ENNReal.toReal_one]
  norm_num [varianceCoeffs,proposalLength,Finset.sum_range_succ]

/-- Concrete arithmetic for the sum over 21 possible missing openings. -/
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

/-- The deficient coordinate has two exposed openings; the other six have three. -/
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
      ((2 : ENNReal)⁻¹^(12*6)*2⁻¹^8*2⁻¹^145) := by ring
    _ = _ := by rw [near_envelope_product,← pow_add,← pow_add]

/-- Finite-population bound for one designated missing opening. -/
theorem near_forest_binomial_bound (p : ENNReal) (hp : p≤1) (trials : Nat) (missing : Fin 7) :
    binomialAverage p trials (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (nearForestEnvelope missing)) ≤
        poissonEnvelope nearCoeffs ((trials : ENNReal)*p)/2^223 := by
  simp_rw [near_forest_first_moment,div_eq_mul_inv]
  rw [binomialAverage_mul_right]
  exact mul_le_mul' (binomial_envelope_le_poisson p hp trials nearCoeffs) le_rfl



/-- The actual uniform-history first moment satisfies the concrete T3 cap.
The separate adaptive-history domination obligation is not assumed here. -/
theorem uniform_history_mean_bound :
    (2 : ENNReal)^128*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) forestEnvelope) ≤ 5 / 8 := by
  calc
    _ ≤ (2 : ENNReal)^128*(poissonEnvelope meanCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^234) :=
      mul_le_mul' le_rfl (forest_binomial_first_bound (1/2^31) (by norm_num) proposalLength)
    _ = (2 : ENNReal)^128*poissonEnvelope meanCoeffs (proposalLength/2^31)/2^234 := by
      simp only [div_eq_mul_inv,mul_one,one_mul,mul_assoc]
    _ ≤ _ := poisson_mean_bound

theorem uniform_history_excess_bound :
    (2 : ENNReal)^225*binomialAverage (1/2^31) proposalLength (fun steps =>
      expectedValue ($ᵗ (Fin 7 → Fin steps → Fin 16) : ProbComp _) (fun table => forestEnvelope table^2))/1 ≤
        18400/100000000 := by
  calc
    _ ≤ (2 : ENNReal)^225*(poissonEnvelope varianceCoeffs ((proposalLength : ENNReal)*(1/2^31))/2^496)/1 := by
      exact ENNReal.div_le_div_right (mul_le_mul' le_rfl
        (forest_binomial_second_bound (1/2^31) (by norm_num) proposalLength)) _
    _ = (2 : ENNReal)^225*poissonEnvelope varianceCoeffs (proposalLength/2^31)/(1*2^496) := by
      simp only [div_eq_mul_inv, mul_one, one_mul, inv_one]
      ring
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
