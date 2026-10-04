import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.ClaudeWCT.WCT9.Cost
import SigGolfCandidate.ClaudeWCT.W9.New.F1a.Clean

section



open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize mrealize_bind mrealize_map cacheB cacheDec cacheDec_cacheB isHash toQ toQ_injOn
  Aligned)
open SigGolfCandidate.T3M.Final (successPipe success_honest_eq foldAll foldAll_cons evalWithAnswerFn_foldAll
  randomOracle_congr probOutput_congr_evalSPMF mrealize_public mrealize_eq_relabel run'_relabel_on allQ_hrealize
  realize_eq_liftM)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
theorem goodQ_sign (cache : Cache) (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (sign cache m) SigGolfCandidate.T3.Cost.GoodQuery :=
  SigGolfCandidate.T3M.allQ_of_bound (ClaudeWCT.WCT9.Cost.bound_sign cache m)
theorem goodQ_expand (m : SigGolfCandidate.T3.Message) (pk : Digest) (σ : Signature) :
    AllQueriesSatisfy (expand m pk σ) SigGolfCandidate.T3.Cost.GoodQuery :=
  SigGolfCandidate.T3M.allQ_of_bound (ClaudeWCT.WCT9.Cost.bound_expand m pk σ)
theorem goodQ_verify (m : SigGolfCandidate.T3.Message) (pk : Digest) (w : Witness) :
    AllQueriesSatisfy (verify m pk w) SigGolfCandidate.T3.Cost.GoodQuery :=
  SigGolfCandidate.T3M.allQ_of_bound (ClaudeWCT.WCT9.Cost.bound_verify m pk w)
variable {I : Images}
set_option maxRecDepth 100000 in
theorem keygen_value (P : Pending I) (sk : SecretKey) :
    (fun r => r.value) <$> (submission I).run .keygen sk =
      (fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) <$> mrealize sk keygen :=
  value_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) (P.keygen_run_counts sk)
set_option maxRecDepth 100000 in
theorem sign_value (P : Pending I) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => r.value) <$> (submission I).run .sign (sk, cache, m) =
      Option.map sigB <$> mrealize sk (sign (cacheDec cache) m) :=
  value_of_counts (F := Option.map sigB) (P.sign_refines sk cache m)
set_option maxRecDepth 100000 in
theorem expand_value (P : Pending I) (m : Message) (pk : PublicKey) (s : Bytes 5456) :
    (fun r => r.value) <$> (submission I).run .expand (m, pk, s) = mrealize 0 (expandB m pk (sigDec s)) := by
  rw [value_of_counts (F := Option.map (fun x : SigGolfCandidate.T3.HashOutput × Witness => witEnc x.1 x.2))
    (P.expand_refines m pk s), expandB, mrealize_map]
set_option maxRecDepth 100000 in
theorem verify_value (P : Pending I) (m : Message) (pk : PublicKey) (w : Bytes 24264) :
    (fun r => r.value.isSome) <$> (submission I).run .verify (m, pk, w) = mrealize 0 (verifyP m pk w) := by
  have h := congrArg (fun x => (fun p : Option Unit × Nat => p.1.isSome) <$> x) (P.verify_refines m pk w)
  simp only [Functor.map_map] at h
  refine h.trans ?_
  have e : (fun p : Bool × Nat => ((if p.1 then some () else none : Option Unit)).isSome) = Prod.fst := by
    funext p; rcases p with ⟨_ | _, n⟩ <;> rfl
  rw [e, SigGolfCandidate.T3M.fst_countCalls]
set_option maxRecDepth 100000 in
theorem successPipe_eq (P : Pending I) (sk : SecretKey) (m : Message) :
    successPipe (submission I) sk m = mrealize sk (honestProgramB m) := by
  unfold successPipe honestProgramB
  rw [keygen_value P, bind_map_left, mrealize_bind]
  refine bind_congr fun kp => ?_
  simp only
  rw [sign_value P, bind_map_left, cacheDec_cacheB, mrealize_bind]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · simp only [Option.map_some]
    rw [expand_value P, sigDec_sigB, mrealize_bind, mrealize_public 0 sk (publicOnly_expandB m kp.1 σ)]
    refine bind_congr fun e => ?_
    rcases e with _ | w
    · rfl
    · exact (verify_value P m _ w).trans (mrealize_public 0 sk (publicOnly_verifyP m kp.1 w))
noncomputable def foldB : M Bool := foldAll msgs honestProgramB true
noncomputable def foldC : M Bool := foldAll msgs honestProgramCore true
theorem allSucceed_eq (P : Pending I) (sk : SecretKey) :
    HonestSummary.allSucceed <$> (submission I).allMessages sk = mrealize sk foldB := by
  rw [allSucceed_allMessages, foldB, mrealize_foldAll]
  exact congrArg (fun F => foldAll msgs F true) (funext fun m => by rw [success_honest_eq, successPipe_eq P])
theorem eval_foldAll_B (L : List SigGolfCandidate.T3.Message) (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk (foldAll L honestProgramB true)) =
      evalWithAnswerFn hash (mrealize sk (foldAll L honestProgramCore true)) := by
  rw [eval_mrealize, eval_mrealize, evalWithAnswerFn_foldAll, evalWithAnswerFn_foldAll]
  simp only [honestB_eval]
theorem eval_foldB (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk foldB) = evalWithAnswerFn hash (mrealize sk foldC) :=
  eval_foldAll_B msgs sk hash
theorem everyMessageProgram_eq : ClaudeWCT.W9.T3.Completeness.everyMessageProgram = foldC := by
  unfold ClaudeWCT.W9.T3.Completeness.everyMessageProgram foldC foldAll msgs
  refine congrArg (fun f => List.foldlM f true (Finset.univ : Finset SigGolfCandidate.T3.Message).toList) ?_
  funext b m
  rw [map_eq_bind_pure_comp]
  rfl
set_option maxRecDepth 100000 in
theorem allQ_honestProgramCore {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (hv : ∀ m pk w, AllQueriesSatisfy (verify m pk w) Q) (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (honestProgramCore m) Q := by
  unfold honestProgramCore
  refine SigGolfCandidate.T3M.allQ_bind hk fun keys => SigGolfCandidate.T3M.allQ_bind (hs _ _) fun sig => ?_
  rcases sig with _ | sig
  · exact SigGolfCandidate.T3M.allQ_pure _
  refine SigGolfCandidate.T3M.allQ_bind (he _ _ _) fun w => ?_
  rcases w with _ | w
  · exact SigGolfCandidate.T3M.allQ_pure _
  exact hv _ _ _
set_option maxRecDepth 100000 in
theorem withRandomOracle_core (S : SourceFacts) (sk : SecretKey) :
    withRandomOracle (mrealize sk foldC) =
      (simulateQ SphincsSecurity.romImpl (realize sk ClaudeWCT.W9.T3.Completeness.everyMessageProgram)).run' ∅ := by
  have hgood : AllQueriesSatisfy foldC SigGolfCandidate.T3.Cost.GoodQuery := by
    unfold foldC
    exact allQ_foldAll' msgs honestProgramCore (allQ_honestProgramCore (Q := SigGolfCandidate.T3.Cost.GoodQuery)
      SigGolfCandidate.T3M.goodQ_keygen goodQ_sign goodQ_expand goodQ_verify) true
  have hhash : AllQueriesSatisfy foldC isHash := by
    unfold foldC
    exact allQ_foldAll' msgs honestProgramCore (allQ_honestProgramCore (Q := isHash) S.hashOnly_keygen
      S.hashOnly_sign S.hashOnly_expand S.hashOnly_verify) true
  unfold withRandomOracle
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), everyMessageProgram_eq, realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right]
theorem submission_complete (P : Pending I) (S : SourceFacts) : (submission I).Complete := by
  intro sk
  have hP : Pr[fun summary => summary.allSucceed = true | withRandomOracle ((submission I).allMessages sk)] =
      Pr[= true | withRandomOracle (mrealize sk foldB)] := by
    rw [← allSucceed_eq P sk, withRandomOracle_map', ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  have hB : Pr[= true | withRandomOracle (mrealize sk foldB)] =
      Pr[= true | withRandomOracle (mrealize sk foldC)] :=
    probOutput_congr_evalSPMF (randomOracle_congr _ _ (eval_foldB sk)) true
  rw [hP, hB, withRandomOracle_core S sk]
  exact S.source_completeness sk
end ClaudeWCT.W9.T3M.Final
end

section

set_option Elab.async false
open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge ENNReal OracleComp.EvalDist
namespace ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen Cache Digest realize privateInput)
open ClaudeWCT.WCT9 (Signature Witness)
open ClaudeWCT.WCT9.Rev3 (sign expand verify)
open SigGolfCandidate.T3M (mrealize cacheB cacheDec cacheDec_cacheB isHash isPublic)
open SigGolfCandidate.T3M.Final (mrealize_public randomOracle_congr expectedValue_congr_evalSPMF)
open ClaudeWCT.W9.T3M (Images submission)
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits ClaudeWCT.W9.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input
attribute [local irreducible] SigGolfCandidate.T3.keygen SigGolfCandidate.T3.keygenPayload
  SigGolfCandidate.T3.privateMac ClaudeWCT.WCT9.Rev3.sign cacheB cacheDec SigGolfCandidate.T3.cacheBytes
set_option maxRecDepth 100000 in
theorem allQ_honestSignCount {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m) Q :=
  SigGolfCandidate.T3M.allQ_bind hk fun _ => allQ_countWith _ (hs _ _)
set_option maxRecDepth 100000 in
theorem allQ_honestJointCounts {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (m : SigGolfCandidate.T3.Message) :
    AllQueriesSatisfy (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m) Q := by
  unfold ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts SigGolfCandidate.T3.ExpansionClosure.jointCounts
  refine SigGolfCandidate.T3M.allQ_bind hk fun keys =>
    SigGolfCandidate.T3M.allQ_bind (allQ_countWith _ (hs _ _)) fun signed => ?_
  rcases signed with ⟨_ | sig, n⟩
  · exact SigGolfCandidate.T3M.allQ_pure _
  · exact SigGolfCandidate.T3M.allQ_bind (allQ_countWith _ (he _ _ _)) fun _ => SigGolfCandidate.T3M.allQ_pure _
variable {I : Images}
theorem abstract_sign_raw (P : Pending I) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign (cacheDec cache) m)))).2 := by
  exact abstract_count_refinement sk hash (sign (cacheDec cache) m)
    ((submission I).run .sign (sk,cache,m)) (Option.map sigB)
    (P.sign_refines sk cache m) (goodQ_sign _ _)
theorem abstract_sign_encoded (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cacheB cache,m))).hashCompressions =
      (evalWithAnswerFn hash (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)))).2 := by
  have h := abstract_sign_raw P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h
theorem abstract_sign_raw_value (P : Pending I) (sk : SecretKey) (cache : Bytes 131072)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cache,m))).value =
      Option.map sigB (evalWithAnswerFn hash (mrealize sk (sign (cacheDec cache) m))) := by
  exact (eval_of_counts (F := Option.map sigB) (P.sign_refines sk cache m) hash).1
theorem abstract_sign_encoded_value (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .sign (sk,cacheB cache,m))).value =
      Option.map sigB (evalWithAnswerFn hash (mrealize sk (sign cache m))) := by
  have h := abstract_sign_raw_value P sk (cacheB cache) m hash
  rw [cacheDec_cacheB] at h
  exact h
theorem abstract_expand_raw_cost (P : Pending I) (m : Message) (pk : PublicKey)
    (sig : Bytes 5456) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .expand (m,pk,sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk (sigDec sig))))).2 := by
  exact abstract_count_refinement 0 hash (expandN m pk (sigDec sig))
    ((submission I).run .expand (m,pk,sig))
    (Option.map (fun x : SigGolfCandidate.T3.HashOutput × Witness => witEnc x.1 x.2))
    (P.expand_refines m pk sig) (goodQ_expandN _ _ _)
theorem abstract_expand_encoded_cost (P : Pending I) (m : Message) (pk : PublicKey)
    (sig : Signature) (hash : Hash) :
    (evalWithAnswerFn hash ((submission I).run .expand (m,pk,sigB sig))).hashCompressions =
      (evalWithAnswerFn hash (mrealize 0 (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk sig)))).2 := by
  have h := abstract_expand_raw_cost P m pk (sigB sig) hash
  rw [sigDec_sigB] at h
  exact h
theorem eval_expand_blocks (answers : SigGolfCandidate.T3.Correctness.Answers) (m : SigGolfCandidate.T3.Message)
    (pk : Digest) (σ : Signature) :
    (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countBlocks (expand m pk σ))).2 =
      (evalWithAnswerFn answers (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk σ))).2 := by
  unfold SigGolfCandidate.T3.Cost.countBlocks
  rw [expand_eq_expandN, countWith_map', evalWithAnswerFn_map]
set_option maxRecDepth 100000 in
theorem sign_count_value (P : Pending I) (sk : SecretKey) (cache : Cache)
    (m : Message) (hash : Hash) :
    ((submission I).runWith hash .sign (sk,cacheB cache,m)).value =
      Option.map sigB (evalWithAnswerFn hash
        (mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)))).1 := by
  have h := abstract_sign_encoded_value P sk cache m hash
  rw [eval_mrealize hash sk (SigGolfCandidate.T3.Cost.countBlocks (sign cache m)), SigGolfCandidate.T3.Cost.countBlocks,
    eval_cost_fst, ← eval_mrealize hash sk (sign cache m)]
  exact h
set_option maxRecDepth 100000 in
theorem expand_count_cost (P : Pending I) (sk : SecretKey) (m : Message)
    (pk : PublicKey) (sig : Signature) (hash : Hash) :
    ((submission I).runWith hash .expand (m,pk,sigB sig)).hashCompressions =
      evalWithAnswerFn hash (Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expand m pk sig))) := by
  have h := abstract_expand_encoded_cost P m pk sig hash
  have hp : AllQueriesSatisfy (SigGolfCandidate.T3.Cost.countBlocks (expandN m pk sig)) isPublic :=
    allQ_countWith SigGolfCandidate.T3.Cost.weight (publicOnly_expandN m pk sig)
  rw [mrealize_public 0 sk hp, eval_mrealize] at h
  rw [evalWithAnswerFn_map, eval_mrealize, eval_expand_blocks]
  exact h
set_option maxRecDepth 100000 in
theorem costs_keygen_eval (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .keygen) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash (pure 1048576 : OracleComp HashSpec ℕ) := by
  rw [evalWithAnswerFn_map, SigGolfCandidate.T3M.Final.eval_costs_keygen, P.keygen_runWith]
  rfl
set_option maxRecDepth 100000 in
theorem costs_sign_eval (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .sign) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$> mrealize sk (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m)) := by
  have hk : ((submission I).runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    congrArg RunResult.value (P.keygen_runWith hash sk)
  have h := generic_outer_sign_cost (submission I) hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m))) hk
    (fun key => (abstract_sign_encoded P sk key.2 m hash).trans
      (evalWithAnswerFn_map hash Prod.snd _).symm)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_count_pipeline sk keygen (fun key => SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m)) Prod.snd))
set_option maxRecDepth 100000 in
theorem costs_expand_eval (P : Pending I) (sk : SecretKey) (m : Message) (hash : Hash) :
    evalWithAnswerFn hash ((fun r => r.costs .expand) <$> (submission I).honest sk m) =
      evalWithAnswerFn hash ((fun r => r.2) <$>
        mrealize sk (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m)) := by
  have hk : ((submission I).runWith hash .keygen sk).value =
      some ((evalWithAnswerFn hash (mrealize sk keygen)).1,
        cacheB (evalWithAnswerFn hash (mrealize sk keygen)).2) :=
    congrArg RunResult.value (P.keygen_runWith hash sk)
  have h := generic_outer_expand_cost (submission I) hash sk m (mrealize sk keygen)
    (fun key => (key.1, cacheB key.2))
    (fun key => mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (sign key.2 m))) Prod.fst sigB
    (fun key sig => Prod.snd <$> mrealize sk (SigGolfCandidate.T3.Cost.countBlocks (expand m key.1 sig)))
    hk (fun key => sign_count_value P sk key.2 m hash)
    (fun key sig => expand_count_cost P sk m key.1 sig hash)
  exact h.trans (congrArg (evalWithAnswerFn hash)
    (generic_joint_count_pipeline sk keygen (fun key => sign key.2 m)
      (fun key sig => expand m key.1 sig)))
theorem keygen_bound (P : Pending I) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  have h := randomOracle_congr _ _ (costs_keygen_eval P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .keygen) <$> (submission I).honest sk m))
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
theorem sign_bound (P : Pending I) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_honestSignCount SigGolfCandidate.T3M.goodQ_keygen goodQ_sign m
  have hhash : AllQueriesSatisfy (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m) isHash :=
    allQ_honestSignCount S.hashOnly_keygen S.hashOnly_sign m
  have h := randomOracle_congr _ _ (costs_sign_eval P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .sign) <$> (submission I).honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.sign.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk (ClaudeWCT.W9.T3.BudgetClosure.honestSignCount m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 131072)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.sign.budget = 2 ^ 17 from rfl]
        norm_num
    _ ≤ 2 := S.honest_sign_exponential_budget sk m
set_option maxRecDepth 100000 in
theorem expand_bound (P : Pending I) (S : SourceFacts) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  have hgood : AllQueriesSatisfy (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m)
      SigGolfCandidate.T3.Cost.GoodQuery :=
    allQ_honestJointCounts SigGolfCandidate.T3M.goodQ_keygen goodQ_sign goodQ_expand m
  have hhash : AllQueriesSatisfy (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m) isHash :=
    allQ_honestJointCounts S.hashOnly_keygen S.hashOnly_sign S.hashOnly_expand m
  have h := randomOracle_congr _ _ (costs_expand_eval P sk m)
  calc expectedValue (withRandomOracle ((submission I).honest sk m)) (fun result => ENNReal.ofReal
        (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ))))
      = expectedValue (withRandomOracle ((fun r => r.costs .expand) <$> (submission I).honest sk m))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) := by
        rw [withRandomOracle_map', expectedValue_map]
    _ = expectedValue (withRandomOracle ((fun r => r.2) <$>
          mrealize sk (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m)))
          (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (Phase.expand.budget : ℝ)))) :=
        expectedValue_congr_evalSPMF h _
    _ = expectedValue (SigGolfCandidate.T3.Sampling.roRun sk
          (ClaudeWCT.W9.T3.ExpansionClosure.honestJointCounts m) ∅)
          (fun result => (2 : ℝ≥0∞) ^ ((result.1.2 : ℝ) / 1048576)) := by
        rw [withRandomOracle_map', withRandomOracle_mrealize sk hgood hhash, Functor.map_map, expectedValue_map]
        refine congrArg _ (funext fun r => ?_)
        rw [two_rpow_eq', show Phase.expand.budget = 2 ^ 20 from rfl]
        norm_num
    _ ≤ 2 := S.honest_expand_exponential_budget sk m
theorem submission_compressionBounds (P : Pending I) (S : SourceFacts) : (submission I).CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m => ?_
  simp only [Phase.budgeted, List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with rfl | rfl | rfl
  · exact keygen_bound P sk m
  · exact sign_bound P S sk m
  · exact expand_bound P S sk m
end ClaudeWCT.W9.T3M.Final
end
