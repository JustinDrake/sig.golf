import SigGolfCandidate.T3M.Final.Pending
import SigGolfCandidate.T3M.Final.Relabel
import SigGolfCandidate.T3M.Final.RO
import SigGolfCandidate.T3M.Final.Pipeline
import SigGolfCandidate.T3M.Witness.Queries

/-!
# Completeness: `submission.Complete` from source completeness (MACH-PLAN §4.2)

1. The organizer's `allSucceed` bit is the conjunction fold of the honest pipelines' success bits
   (`allSucceed_allMessages`), and each success bit is, by the four value refinements and the codec round trips,
   `mrealize sk (honestProgramB m)` (`successPipe_eq`): the machine pipeline is the source pipeline with the
   machine's witness bytes (`expandB`, `verifyP`).
2. Under every fixed oracle the byte pipeline evaluates like Core's (`honestB_eval`, stream W), so the organizer's
   lazy oracle gives both folds the same law (`randomOracle_congr`).
3. Core's fold is CLOSURE's `everyMessageProgram`; on the organizer's oracle it is, by the injective relabeling `toQ`
   on aligned queries and hash-only realization, CLOSURE's realized source experiment (`withRandomOracle_core`).
4. `source_completeness` closes it; `FAILURE = 2^-128`.
-/

open OracleComp OracleSpec SigGolfCandidate.Legacy SigGolfCandidate.Bridge

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3 (M Spec keygen sign expand verify Cache Digest Signature realize)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SigGolfCandidate.T3M.submission
  SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

/-! ## Values from the refinements -/

theorem value_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)} {X : OracleComp HashSpec γ}
    {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => r.value) <$> run = F <$> X := by
  have h2 := congrArg (fun x => Prod.fst <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2]
  conv_rhs => rw [← fst_countBoth X]
  rw [Functor.map_map]

set_option maxRecDepth 100000 in
theorem keygen_value (P : Pending) (sk : SecretKey) :
    (fun r => r.value) <$> submission.run .keygen sk =
      (fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) <$> mrealize sk keygen :=
  value_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2)) (P.keygen_run_counts sk)

set_option maxRecDepth 100000 in
theorem sign_value (P : Pending) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => r.value) <$> submission.run .sign (sk, cache, m) =
      Option.map sigB <$> mrealize sk (sign (cacheDec cache) m) :=
  value_of_counts (F := Option.map sigB) (P.sign_refines sk cache m)

set_option maxRecDepth 100000 in
theorem expand_value (P : Pending) (m : Message) (pk : PublicKey) (s : Bytes 5728) :
    (fun r => r.value) <$> submission.run .expand (m, pk, s) = mrealize 0 (expandB m pk (sigDec s)) := by
  rw [value_of_counts (F := Option.map (fun x : T3.HashOutput × T3.Witness => witEnc x.1 x.2))
    (P.expand_refines m pk s), expandB, mrealize_map]

set_option maxRecDepth 100000 in
theorem verify_value (P : Pending) (m : Message) (pk : PublicKey) (w : Bytes 25240) :
    (fun r => r.value.isSome) <$> submission.run .verify (m, pk, w) = mrealize 0 (verifyP m pk w) := by
  have h := congrArg (fun x => (fun p : Option Unit × Nat => p.1.isSome) <$> x) (P.verify_refines m pk w)
  simp only [Functor.map_map] at h
  refine h.trans ?_
  have e : (fun p : Bool × Nat => ((if p.1 then some () else none : Option Unit)).isSome) = Prod.fst := by
    funext p; rcases p with ⟨_ | _, n⟩ <;> rfl
  rw [e, fst_countCalls]

/-! ## The success bit is the byte pipeline -/

set_option maxRecDepth 100000 in
theorem successPipe_eq (P : Pending) (sk : SecretKey) (m : Message) :
    successPipe submission sk m = mrealize sk (honestProgramB m) := by
  unfold successPipe honestProgramB
  rw [keygen_value P, bind_map_left, mrealize_bind]
  refine bind_congr fun kp => ?_
  simp only
  rw [sign_value P, bind_map_left, cacheDec_cacheB, mrealize_bind]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · simp only [Option.map_some]
    rw [expand_value P, sigDec_sigB, mrealize_bind,
      mrealize_public 0 sk (T3M.allQ_mono (T3M.pubGood_expandB m kp.1 σ) fun _ h => h.1)]
    refine bind_congr fun e => ?_
    rcases e with _ | w
    · rfl
    · exact (verify_value P m _ w).trans (mrealize_public 0 sk (T3M.publicOnly_verifyP m kp.1 w))

/-! ## The fold -/

theorem allSucceed_foldlM (Pr : Message → OracleComp HashSpec HonestResult) (L : List Message)
    (s : HonestSummary) :
    HonestSummary.allSucceed <$> L.foldlM (fun summary message => do
        let result ← Pr message
        return (⟨summary.allSucceed && result.success,
          fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) s =
      foldAll L (fun m => HonestResult.success <$> Pr m) s.allSucceed := by
  induction L generalizing s with
  | nil => simp [foldAll]
  | cons m L ih =>
    rw [List.foldlM_cons, foldAll_cons, map_bind, bind_assoc, bind_map_left]
    refine bind_congr fun r => ?_
    rw [pure_bind, ih]

theorem allSucceed_allMessages (sub : Submission) (sk : SecretKey) :
    HonestSummary.allSucceed <$> sub.allMessages sk =
      foldAll (Finset.univ : Finset Message).toList
        (fun m => HonestResult.success <$> sub.honest sk m) true := by
  unfold Submission.allMessages
  exact allSucceed_foldlM _ _ {}

theorem mrealize_foldAll {κ : Type} (sk : BitVec 256) (L : List κ) (Pr : κ → M Bool) (b : Bool) :
    mrealize sk (foldAll L Pr b) = foldAll L (fun k => mrealize sk (Pr k)) b := by
  induction L generalizing b with
  | nil => rfl
  | cons k L ih =>
    rw [foldAll_cons, foldAll_cons, mrealize_bind]
    exact bind_congr fun c => ih _

/-- All messages, in `Finset.univ` order (the organizer's `allMessages` order). -/
noncomputable def msgs : List T3.Message := (Finset.univ : Finset T3.Message).toList

/-- The machine pipelines of all messages, as one source program on the byte objects. -/
noncomputable def foldB : M Bool := foldAll msgs honestProgramB true

/-- Core's pipelines of all messages. -/
noncomputable def foldC : M Bool := foldAll msgs honestProgramCore true

theorem allSucceed_eq (P : Pending) (sk : SecretKey) :
    HonestSummary.allSucceed <$> submission.allMessages sk = mrealize sk foldB := by
  rw [allSucceed_allMessages, foldB, mrealize_foldAll]
  exact congrArg (fun F => foldAll msgs F true) (funext fun m => by rw [success_honest_eq, successPipe_eq P])

/-! ## Under every fixed oracle the byte pipeline is Core's -/

/-- The answer function a fixed organizer oracle induces on Core's queries. -/
def machineAnswers (hash : Hash) (sk : BitVec 256) : T3.Correctness.Answers :=
  fun q => evalWithAnswerFn hash (machineHandler sk q)

theorem eval_mrealize {α : Type} (hash : Hash) (sk : BitVec 256) (p : M α) :
    evalWithAnswerFn hash (mrealize sk p) = evalWithAnswerFn (machineAnswers hash sk) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [mrealize_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind]
    have hq : evalWithAnswerFn hash (mrealize sk (liftM (Spec.query q) : M _)) = machineAnswers hash sk q := by
      rw [mrealize, simulateQ_spec_query]; rfl
    have hq' : evalWithAnswerFn (machineAnswers hash sk) (liftM (Spec.query q) : M _) =
        machineAnswers hash sk q := simulateQ_spec_query _ _
    rw [hq, hq']
    exact ih _

theorem eval_foldAll_B (L : List T3.Message) (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk (foldAll L honestProgramB true)) =
      evalWithAnswerFn hash (mrealize sk (foldAll L honestProgramCore true)) := by
  rw [eval_mrealize, eval_mrealize, evalWithAnswerFn_foldAll, evalWithAnswerFn_foldAll]
  simp only [honestB_eval]

theorem eval_foldB (sk : SecretKey) (hash : Hash) :
    evalWithAnswerFn hash (mrealize sk foldB) = evalWithAnswerFn hash (mrealize sk foldC) :=
  eval_foldAll_B msgs sk hash

/-! ## Core's fold on the organizer's oracle is CLOSURE's experiment -/

theorem everyMessageProgram_eq : everyMessageProgram = foldC := by
  unfold everyMessageProgram foldC foldAll msgs
  refine congrArg (fun f => List.foldlM f true (Finset.univ : Finset T3.Message).toList) ?_
  funext b m
  rw [map_eq_bind_pure_comp]
  rfl

theorem allQ_foldAll' {κ : Type} {Q : Spec.Domain → Prop} (L : List κ) (Pr : κ → M Bool)
    (h : ∀ k, AllQueriesSatisfy (Pr k) Q) (b : Bool) : AllQueriesSatisfy (foldAll L Pr b) Q := by
  unfold foldAll
  exact T3M.allQ_foldlM _ _ (fun _ k => T3M.allQ_map _ (h k)) _

set_option maxRecDepth 100000 in
theorem allQ_honestProgramCore {Q : Spec.Domain → Prop} (hk : AllQueriesSatisfy keygen Q)
    (hs : ∀ c m, AllQueriesSatisfy (sign c m) Q) (he : ∀ m pk σ, AllQueriesSatisfy (expand m pk σ) Q)
    (hv : ∀ m pk w, AllQueriesSatisfy (verify m pk w) Q) (m : T3.Message) :
    AllQueriesSatisfy (honestProgramCore m) Q := by
  unfold honestProgramCore
  refine T3M.allQ_bind hk fun keys => T3M.allQ_bind (hs _ _) fun sig => ?_
  rcases sig with _ | sig
  · exact T3M.allQ_pure _
  refine T3M.allQ_bind (he _ _ _) fun w => ?_
  rcases w with _ | w
  · exact T3M.allQ_pure _
  exact hv _ _ _

set_option maxRecDepth 100000 in
theorem withRandomOracle_core (S : SourceFacts) (sk : SecretKey) :
    withRandomOracle (mrealize sk foldC) =
      (simulateQ SphincsSecurity.romImpl (realize sk everyMessageProgram)).run' ∅ := by
  have hgood : AllQueriesSatisfy foldC T3.Cost.GoodQuery := by
    unfold foldC
    exact allQ_foldAll' msgs honestProgramCore (allQ_honestProgramCore (Q := T3.Cost.GoodQuery)
      T3M.goodQ_keygen T3M.goodQ_sign T3M.goodQ_expand T3M.goodQ_verify) true
  have hhash : AllQueriesSatisfy foldC isHash := by
    unfold foldC
    exact allQ_foldAll' msgs honestProgramCore (allQ_honestProgramCore (Q := isHash) S.hashOnly_keygen
      S.hashOnly_sign S.hashOnly_expand S.hashOnly_verify) true
  unfold withRandomOracle
  rw [mrealize_eq_relabel, ← run'_relabel_on toQ {l | Aligned l} toQ_injOn _ (allQ_hrealize sk hgood) ∅ ∅
    (fun _ _ => rfl), everyMessageProgram_eq, realize_eq_liftM sk hhash, SphincsSecurity.romImpl,
    QueryImpl.simulateQ_add_liftM_right]

theorem withRandomOracle_map' {α β : Type} (f : α → β) (oa : OracleComp HashSpec α) :
    withRandomOracle (f <$> oa) = f <$> withRandomOracle oa := by
  unfold withRandomOracle
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

/-- **Completeness** of the T3 submission. -/
theorem submission_complete (P : Pending) (S : SourceFacts) : submission.Complete := by
  intro sk
  have hP : Pr[fun summary => summary.allSucceed = true | withRandomOracle (submission.allMessages sk)] =
      Pr[= true | withRandomOracle (mrealize sk foldB)] := by
    rw [← allSucceed_eq P sk, withRandomOracle_map', ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  have hB : Pr[= true | withRandomOracle (mrealize sk foldB)] =
      Pr[= true | withRandomOracle (mrealize sk foldC)] :=
    probOutput_congr_evalSPMF (randomOracle_congr _ _ (eval_foldB sk)) true
  rw [hP, hB, withRandomOracle_core S sk]
  exact S.source_completeness sk

end SigGolfCandidate.T3M.Final
