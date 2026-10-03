import SigGolfCandidate.T3M.Final.Completeness

/-!
# Compression budgets: `submission.CompressionBounds` from CLOSURE's moments (MACH-PLAN §4.2)

* keygen: under every fixed oracle keygen costs exactly 1,048,576 compressions (`KeygenRunWith`), so the moment is
  `2^(1048576/2^20) ≤ 2`;
* sign, expand: under every fixed oracle the organizer's recorded cost of the phase is the count of CLOSURE's counted
  source program (`honestSignCount`, `honestJointCounts`) realized by the same oracle (`costs_sign_eval`,
  `costs_expand_eval`: the refinements are exact in compressions, and `mrealize_countBlocks` matches the organizer's
  blocks with Core's weights), so both have the same law under the lazy oracle (`randomOracle_congr`), which on the
  organizer's oracle is CLOSURE's `roRun` (`withRandomOracle_mrealize`). CLOSURE's moments close it.
-/

set_option Elab.async false

open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen sign expand verify Cache Digest Signature realize privateInput)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SigGolfCandidate.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

/- Keep source programs and cache codecs abstract during rewrite matching. -/
attribute [local irreducible] T3.keygen T3.keygenPayload T3.privateMac T3.sign cacheB cacheDec T3.cacheBytes

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

theorem abstract_count_refinement {α β : Type} (sk : SecretKey) (hash : Hash)
    (X : M α) (run : OracleComp HashSpec (RunResult β)) (F : α → Option β)
    (h : (fun r => (r.value,r.hashCalls,r.hashCompressions)) <$> run =
      (fun p => (F p.1,p.2.1,p.2.2)) <$> countBoth (mrealize sk X))
    (hg : AllQueriesSatisfy X T3.Cost.GoodQuery) :
    (evalWithAnswerFn hash run).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (T3.Cost.countBlocks X))).2 := by
  exact (eval_of_counts h hash).2.trans
    (congrArg (fun p => (evalWithAnswerFn hash p).2) (mrealize_countBlocks sk hg))





theorem abstract_sign_raw (P : Pending) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .sign (sk,cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (T3.Cost.countBlocks (sign (cacheDec cache) m)))).2 := by
  exact abstract_count_refinement sk hash (sign (cacheDec cache) m)
    (submission.run .sign (sk,cache,m)) (Option.map sigB)
    (P.sign_refines sk cache m) (T3M.goodQ_sign _ _)


theorem abstract_sign_encoded (P : Pending) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .sign (sk,cacheB cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (T3.Cost.countBlocks (sign cache m)))).2 := by
  have h := abstract_sign_raw P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h



theorem abstract_sign_raw_value (P : Pending) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .sign (sk,cache,m))).value =
      Option.map sigB (evalWithAnswerFn hash (mrealize sk (sign (cacheDec cache) m))) := by
  exact (eval_of_counts (F := Option.map sigB) (P.sign_refines sk cache m) hash).1

theorem abstract_sign_encoded_value (P : Pending) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .sign (sk,cacheB cache,m))).value =
      Option.map sigB (evalWithAnswerFn hash (mrealize sk (sign cache m))) := by
  have h := abstract_sign_raw_value P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h

theorem abstract_expand_raw_cost (P : Pending) (m : Message) (pk : PublicKey)
    (sig : Bytes 5728) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .expand (m,pk,sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (T3.Cost.countBlocks (expandN m pk (sigDec sig))))).2 := by
  exact abstract_count_refinement 0 hash (expandN m pk (sigDec sig))
    (submission.run .expand (m,pk,sig))
    (Option.map (fun x : T3.HashOutput × T3.Witness => witEnc x.1 x.2))
    (P.expand_refines m pk sig) (T3M.goodQ_expandN _ _ _)

theorem abstract_expand_encoded_cost (P : Pending) (m : Message) (pk : PublicKey)
    (sig : Signature) (hash : Hash) :
    (evalWithAnswerFn hash (submission.run .expand (m,pk,sigB sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (T3.Cost.countBlocks (expandN m pk sig)))).2 := by
  have h := abstract_expand_raw_cost P m pk (sigB sig) hash
  rw [sigDec_sigB] at h
  exact h

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

/-- Assemble signing costs while both the key generator and counted signer remain abstract. -/
theorem generic_outer_sign_cost {κ : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encode : κ → PublicKey × Bytes sub.sizes.cache)
    (counts : κ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encode (evalWithAnswerFn hash keys)))
    (hcounts : ∀ key, (sub.runWith hash .sign (sk, (encode key).2, message)).hashCompressions =
      evalWithAnswerFn hash (counts key)) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= counts) := by
  rw [evalWithAnswerFn_map, eval_costs_sign, hkeys, evalWithAnswerFn_bind]
  exact hcounts (evalWithAnswerFn hash keys)

/-- Distribute a counted source pipeline before specializing its expensive key generator. -/
theorem generic_count_pipeline {κ α : Type} (sk : SecretKey) (keys : T3.M κ)
    (signer : κ → T3.M α) (charge : α → Nat) :
    mrealize sk keys >>= (fun key => charge <$> mrealize sk (signer key)) =
      charge <$> mrealize sk (keys >>= signer) := by
  rw [mrealize_bind, map_bind]

/-- Assemble expansion costs without reducing the key generator or signing computation. -/
theorem generic_outer_expand_cost {κ σ α : Type} (sub : Submission) (hash : Hash)
    (sk : SecretKey) (message : Message) (keys : OracleComp HashSpec κ)
    (encodeKey : κ → PublicKey × Bytes sub.sizes.cache)
    (signer : κ → OracleComp HashSpec α) (selected : α → Option σ)
    (encodeSig : σ → Bytes sub.sizes.signature)
    (counts : κ → σ → OracleComp HashSpec Nat)
    (hkeys : (sub.runWith hash .keygen sk).value = some (encodeKey (evalWithAnswerFn hash keys)))
    (hsign : ∀ key, (sub.runWith hash .sign (sk, (encodeKey key).2, message)).value =
      (selected (evalWithAnswerFn hash (signer key))).map encodeSig)
    (hexpand : ∀ key sig, (sub.runWith hash .expand (message, (encodeKey key).1, encodeSig sig)).hashCompressions =
      evalWithAnswerFn hash (counts key sig)) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> sub.honest sk message) =
      evalWithAnswerFn hash (keys >>= fun key => signer key >>= fun signed =>
        match selected signed with
        | none => pure 0
        | some sig => counts key sig) := by
  rw [evalWithAnswerFn_map, eval_costs_expand, hkeys, evalWithAnswerFn_bind]
  simp only
  rw [hsign, evalWithAnswerFn_bind]
  cases selected (evalWithAnswerFn hash (signer (evalWithAnswerFn hash keys))) with
  | none => rfl
  | some sig => exact hexpand _ sig

/-- The expansion count projection distributes through a fully abstract joint pipeline. -/
theorem generic_joint_count_pipeline {κ σ ω : Type} (sk : SecretKey)
    (initial : T3.M κ) (signer : κ → T3.M (Option σ)) (expander : κ → σ → T3.M ω) :
    (mrealize sk initial >>= fun key => mrealize sk (T3.Cost.countBlocks (signer key)) >>= fun signed =>
      match signed.1 with
      | none => pure 0
      | some sig => Prod.snd <$> mrealize sk (T3.Cost.countBlocks (expander key sig))) =
      Prod.snd <$> mrealize sk (jointCounts initial signer expander) := by
  unfold jointCounts
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro key
  rw [mrealize_bind, map_bind]
  apply bind_congr
  intro signed
  rcases signed with ⟨_ | sig, count⟩
  · simp only [mrealize_pure, map_pure]
  · simp only [mrealize_bind, map_bind, mrealize_pure, map_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]


set_option maxRecDepth 100000 in
theorem sign_count_value (P : Pending) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (submission.runWith hash .sign (sk,cacheB cache,m)).value =
      Option.map sigB (evalWithAnswerFn hash
        (mrealize sk (T3.Cost.countBlocks (sign cache m)))).1 := by
  have h := abstract_sign_encoded_value P sk cache m hash
  rw [eval_mrealize hash sk (T3.Cost.countBlocks (sign cache m)), T3.Cost.countBlocks,
    eval_cost_fst, ← eval_mrealize hash sk (sign cache m)]
  exact h

set_option maxRecDepth 100000 in
theorem expand_count_cost (P : Pending) (sk : SecretKey) (m : Message)
    (pk : PublicKey) (sig : Signature) (hash : Hash) :
    (submission.runWith hash .expand (m,pk,sigB sig)).hashCompressions =
      evalWithAnswerFn hash (Prod.snd <$> mrealize sk (T3.Cost.countBlocks (expand m pk sig))) := by
  have h := abstract_expand_encoded_cost P m pk sig hash
  have hp : AllQueriesSatisfy (T3.Cost.countBlocks (expandN m pk sig)) isPublic :=
    allQ_countWith T3.Cost.weight (T3M.publicOnly_expandN m pk sig)
  rw [mrealize_public 0 sk hp, eval_mrealize] at h
  rw [evalWithAnswerFn_map, eval_mrealize, eval_expand_blocks]
  exact h


set_option maxRecDepth 100000 in
theorem costs_keygen_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .keygen) <$> submission.honest sk m) =
      evalWithAnswerFn hash (pure 1048576 : OracleComp HashSpec ℕ) := by
  rw [evalWithAnswerFn_map, eval_costs_keygen, P.keygen_runWith]
  rfl

set_option maxRecDepth 100000 in
theorem costs_sign_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> submission.honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (honestSignCount m)) := by
  have hk : (submission.runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    congrArg RunResult.value (P.keygen_runWith hash sk)
  have h := generic_outer_sign_cost submission hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => Prod.snd <$> mrealize sk (T3.Cost.countBlocks (sign key.2 m))) hk
    (fun key => (abstract_sign_encoded P sk key.2 m hash).trans
      (evalWithAnswerFn_map hash Prod.snd _).symm)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_count_pipeline sk keygen (fun key => T3.Cost.countBlocks (sign key.2 m)) Prod.snd))

set_option maxRecDepth 100000 in
theorem costs_expand_eval (P : Pending) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> submission.honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (honestJointCounts m)) := by
  have hk : (submission.runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    congrArg RunResult.value (P.keygen_runWith hash sk)
  have h := generic_outer_expand_cost submission hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => mrealize sk (T3.Cost.countBlocks (sign key.2 m))) Prod.fst sigB
    (fun key sig => Prod.snd <$> mrealize sk (T3.Cost.countBlocks (expand m key.1 sig)))
    hk (fun key => sign_count_value P sk key.2 m hash)
    (fun key sig => expand_count_cost P sk m key.1 sig hash)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_joint_count_pipeline sk keygen (fun key => sign key.2 m)
      (fun key sig => expand m key.1 sig)))

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
    _ = expectedValue (withRandomOracle (pure 1048576 : OracleComp HashSpec ℕ))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.keygen.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = ENNReal.ofReal (Real.rpow 2 (((1048576 : ℕ) : ℝ) / (Phase.keygen.budget : ℝ))) := by
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
