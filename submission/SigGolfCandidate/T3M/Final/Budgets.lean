import SigGolfCandidate.T3M.Final.Completeness

/-!
# Compression budgets: `submission.CompressionBounds` from CLOSURE's moments (MACH-PLAN §4.2)

* keygen: under every fixed oracle keygen costs exactly 1,047,038 compressions (`KeygenRunWith`), so the moment is
  `2^(1047038/2^20) ≤ 2`;
* sign, expand: under every fixed oracle the organizer's recorded cost of the phase is the count of CLOSURE's counted
  source program (`honestSignCount`, `honestJointCounts`) realized by the same oracle (`costs_sign_eval`,
  `costs_expand_eval`: the refinements are exact in compressions, and `mrealize_countBlocks` matches the organizer's
  blocks with Core's weights), so both have the same law under the lazy oracle (`randomOracle_congr`), which on the
  organizer's oracle is CLOSURE's `roRun` (`withRandomOracle_mrealize`). CLOSURE's moments close it.
-/

open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen sign expand verify Cache Digest Signature realize privateInput)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SigGolfCandidate.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

/-! ## Realized compressions are Core's weights -/

theorem mrealize_query_coin (sk : BitVec 256) (n : ℕ) :
    mrealize sk (liftM (Spec.query (.inl (.inl n))) : M (Fin (n + 1))) = pure 0 := by
  simp [mrealize, machineHandler]

theorem mrealize_query_public (sk : BitVec 256) (input : List UInt8) :
    mrealize sk (liftM (Spec.query (.inl (.inr input))) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ input)) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]

theorem mrealize_query_private (sk : BitVec 256) (c : T3.Coordinate) :
    mrealize sk (liftM (Spec.query (.inr c)) : M _) =
      (liftM (OracleSpec.query (spec := HashSpec) (toQ (privateInput sk c))) : OracleComp HashSpec _) := by
  simp [mrealize, machineHandler]

theorem countBlocks_query_bind {α : Type} (x : Query) (g : BitVec 256 → OracleComp HashSpec α) :
    countBlocks ((liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= g) =
      (liftM (OracleSpec.query (spec := HashSpec) x) : OracleComp HashSpec _) >>= fun a =>
        (fun r => (r.1, x.blocks + r.2)) <$> countBlocks (g a) := by
  unfold countBlocks
  rw [countWith_bind, countWith_query, bind_map_left]

/-- The organizer's compression count of a realized Core program is Core's weight count. -/
theorem mrealize_countBlocks {α : Type} (sk : BitVec 256) {p : M α}
    (h : AllQueriesSatisfy p T3.Cost.GoodQuery) :
    countBlocks (mrealize sk p) = mrealize sk (T3.Cost.countBlocks p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [mrealize_bind]
    unfold T3.Cost.countBlocks
    rw [T3.Cost.countWith_bind, T3.Cost.countWith_query, mrealize_bind, mrealize_map, bind_map_left]
    rcases q with (n | input) | c
    · rw [mrealize_query_coin, pure_bind, pure_bind]
      simp only [mrealize_map]
      rw [show T3.Cost.countWith T3.Cost.weight (k (0 : Fin (n + 1))) = T3.Cost.countBlocks (k (0 : Fin (n + 1)))
        from rfl, ← ih (0 : Fin (n + 1)) (h.2 _)]
      simp only [T3.Cost.weight, Nat.zero_add]
      exact (id_map _).symm
    · rw [mrealize_query_public, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show T3.Cost.countWith T3.Cost.weight (k a) = T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ h.1]
      rfl
    · rw [mrealize_query_private, countBlocks_query_bind]
      refine bind_congr fun a => ?_
      simp only [mrealize_map]
      rw [show T3.Cost.countWith T3.Cost.weight (k a) = T3.Cost.countBlocks (k a) from rfl, ← ih a (h.2 a),
        blocks_toQ (privateInput_aligned sk c), T3.Cost.private_realization_weight]

/-! ## Query shapes of the counted source programs -/

theorem allQ_countWith {α : Type} {Q : Spec.Domain → Prop} (wt : T3.Cost.Query → ℕ) {p : M α}
    (h : AllQueriesSatisfy p Q) : AllQueriesSatisfy (T3.Cost.countWith wt p) Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [T3.Cost.countWith_bind, T3.Cost.countWith_query, bind_map_left]
    exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨h.1, fun u => T3M.allQ_map _ (ih u (h.2 u))⟩

set_option maxRecDepth 100000 in
theorem allQ_honestSignCount {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (m : T3.Message) :
    AllQueriesSatisfy (honestSignCount m) Q :=
  T3M.allQ_bind hk fun _ => allQ_countWith _ (hs _ _)

set_option maxRecDepth 100000 in
theorem allQ_honestJointCounts {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (m : T3.Message) : AllQueriesSatisfy (honestJointCounts m) Q := by
  unfold honestJointCounts jointCounts
  refine T3M.allQ_bind hk fun keys => T3M.allQ_bind (allQ_countWith _ (hs _ _)) fun signed => ?_
  rcases signed with ⟨_ | sig, n⟩
  · exact T3M.allQ_pure _
  · exact T3M.allQ_bind (allQ_countWith _ (he _ _ _)) fun _ => T3M.allQ_pure _

set_option maxRecDepth 100000 in
/-- On the organizer's oracle, a realized hash-only Core program with aligned queries is the source experiment
`roRun` (its output component). -/
theorem withRandomOracle_mrealize {α : Type} (sk : SecretKey) {Y : M α}
    (hgood : AllQueriesSatisfy Y T3.Cost.GoodQuery) (hhash : AllQueriesSatisfy Y isHash) :
    withRandomOracle (mrealize sk Y) = Prod.fst <$> T3.Sampling.roRun sk Y ∅ := by
  unfold withRandomOracle T3.Sampling.roRun
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right, StateT.run'_eq]

/-! ## Under a fixed oracle -/

theorem eval_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) (hash : Hash) :
    (evalWithAnswerFn hash run).value = F (evalWithAnswerFn hash X) ∧
      (evalWithAnswerFn hash run).hashCompressions = (evalWithAnswerFn hash (countBlocks X)).2 := by
  have h1 := congrArg (evalWithAnswerFn hash) h
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map] at h1
  simp only [Prod.mk.injEq] at h1
  have h2 := congrArg (evalWithAnswerFn hash) (fst_countBoth X)
  rw [evalWithAnswerFn_map] at h2
  have h3 := congrArg (evalWithAnswerFn hash) (countBoth_blocks X)
  rw [evalWithAnswerFn_map] at h3
  refine ⟨h1.1.trans (by rw [h2]), h1.2.2.trans ?_⟩
  rw [← h3]

theorem eval_cost_fst {α : Type} (answers : T3.Correctness.Answers) (wt : T3.Cost.Query → ℕ) (p : M α) :
    (evalWithAnswerFn answers (T3.Cost.countWith wt p)).1 = evalWithAnswerFn answers p := by
  have := congrArg (evalWithAnswerFn answers) (T3.Cost.fst_countWith wt p)
  rw [evalWithAnswerFn_map] at this
  exact this

theorem countWith_map' {α β : Type} (wt : T3.Cost.Query → ℕ) (f : α → β) (p : M α) :
    T3.Cost.countWith wt (f <$> p) = (fun q => (f q.1, q.2)) <$> T3.Cost.countWith wt p := by
  rw [map_eq_bind_pure_comp, T3.Cost.countWith_bind, map_eq_bind_pure_comp]
  refine bind_congr fun q => ?_
  simp

theorem eval_expand_blocks (answers : T3.Correctness.Answers) (m : T3.Message) (pk : Digest) (σ : Signature) :
    (evalWithAnswerFn answers (T3.Cost.countBlocks (expand m pk σ))).2 =
      (evalWithAnswerFn answers (T3.Cost.countBlocks (expandN m pk σ))).2 := by
  unfold T3.Cost.countBlocks
  rw [expand_eq_expandN, countWith_map', evalWithAnswerFn_map]

set_option maxRecDepth 100000 in
theorem costs_keygen_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .keygen) <$> submission.honest sk m) =
      evalWithAnswerFn hash (pure 1047038 : OracleComp HashSpec ℕ) := by
  rw [evalWithAnswerFn_map, eval_costs_keygen, P.keygen_runWith]
  rfl

set_option maxRecDepth 100000 in
theorem costs_sign_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> submission.honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (honestSignCount m)) := by
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map, eval_costs_sign, P.keygen_runWith]
  simp only [Submission.runWith]
  rw [(eval_of_counts (F := Option.map sigB) (P.sign_refines sk _ m) hash).2, cacheDec_cacheB,
    mrealize_countBlocks sk (T3M.goodQ_sign _ _), honestSignCount, mrealize_bind, evalWithAnswerFn_bind]

set_option maxRecDepth 100000 in
theorem costs_expand_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> submission.honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (honestJointCounts m)) := by
  rw [evalWithAnswerFn_map, evalWithAnswerFn_map, eval_costs_expand, P.keygen_runWith]
  simp only [Submission.runWith]
  rw [(eval_of_counts (F := Option.map sigB) (P.sign_refines sk _ m) hash).1, cacheDec_cacheB]
  rw [eval_mrealize hash sk (honestJointCounts m)]
  unfold honestJointCounts jointCounts
  simp only [evalWithAnswerFn_bind]
  rw [← eval_mrealize hash sk keygen]
  generalize evalWithAnswerFn hash (mrealize sk keygen) = e
  have hsig : (evalWithAnswerFn (machineAnswers hash sk) (T3.Cost.countBlocks (sign e.2 m))).1 =
      evalWithAnswerFn hash (mrealize sk (sign e.2 m)) := by
    rw [T3.Cost.countBlocks, eval_cost_fst, eval_mrealize]
  generalize hS : evalWithAnswerFn (machineAnswers hash sk) (T3.Cost.countBlocks (sign e.2 m)) = signed at hsig
  rcases signed with ⟨_ | σ, n⟩
  · simp only at hsig
    rw [← hsig]
    rfl
  · simp only at hsig
    rw [← hsig]
    simp only [Option.map_some]
    rw [(eval_of_counts (F := Option.map (fun x : T3.HashOutput × T3.Witness => witEnc x.1 x.2))
      (P.expand_refines m _ _) hash).2, sigDec_sigB,
      mrealize_public 0 sk (T3M.publicOnly_expandN _ _ _), mrealize_countBlocks sk (T3M.goodQ_expandN _ _ _),
      eval_mrealize]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    rw [eval_expand_blocks]

/-! ## The three moments -/

theorem two_rpow_eq' (x : ℝ) : (2 : ℝ≥0∞) ^ x = ENNReal.ofReal (Real.rpow 2 x) := by
  rw [Real.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp

theorem withRandomOracle_pure {α : Type} (a : α) : withRandomOracle (pure a : OracleComp HashSpec α) = pure a := by
  simp [withRandomOracle]

theorem keygen_bound (P : Pending) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  have h := randomOracle_congr _ _ (costs_keygen_eval P sk m)
  calc expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .keygen) <$> submission.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle (pure 1047038 : OracleComp HashSpec ℕ))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = ENNReal.ofReal (Real.rpow 2 (((1047038 : ℕ) : ℝ) / (Phase.keygen.budget : ℝ))) := by
        rw [withRandomOracle_pure, expectedValue_pure]
    _ ≤ ENNReal.ofReal (Real.rpow 2 1) := by
        refine ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
        rw [show Phase.keygen.budget = 2 ^ 20 from rfl]
        rw [div_le_one (by positivity)]
        norm_num
    _ = 2 := by rw [Real.rpow_eq_pow, Real.rpow_one]; simp

set_option maxRecDepth 100000 in
theorem sign_bound (P : Pending) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (honestSignCount m) T3.Cost.GoodQuery :=
    allQ_honestSignCount T3M.goodQ_keygen T3M.goodQ_sign m
  have hhash : AllQueriesSatisfy (honestSignCount m) isHash :=
    allQ_honestSignCount S.hashOnly_keygen S.hashOnly_sign m
  have h := randomOracle_congr _ _ (costs_sign_eval P sk m)
  calc expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .sign) <$> submission.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$> mrealize sk (honestSignCount m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (T3.Sampling.roRun sk (honestSignCount m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.sign.budget = 2 ^ 17 from rfl]
        norm_num
    _ ≤ 2 := S.honest_sign_exponential_budget sk m

set_option maxRecDepth 100000 in
theorem expand_bound (P : Pending) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (honestJointCounts m) T3.Cost.GoodQuery :=
    allQ_honestJointCounts T3M.goodQ_keygen T3M.goodQ_sign T3M.goodQ_expand m
  have hhash : AllQueriesSatisfy (honestJointCounts m) isHash :=
    allQ_honestJointCounts S.hashOnly_keygen S.hashOnly_sign S.hashOnly_expand m
  have h := randomOracle_congr _ _ (costs_expand_eval P sk m)
  calc expectedValue (withRandomOracle (submission.honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .expand) <$> submission.honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$> mrealize sk (honestJointCounts m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (T3.Sampling.roRun sk (honestJointCounts m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.expand.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := S.honest_expand_exponential_budget sk m

/-- **Compression budgets** of the T3 submission. -/
theorem submission_compressionBounds (P : Pending) (S : SourceFacts) : submission.CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m => ?_
  simp only [Phase.budgeted, List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with rfl | rfl | rfl
  · exact keygen_bound P sk m
  · exact sign_bound P S sk m
  · exact expand_bound P S sk m

end SigGolfCandidate.T3M.Final
