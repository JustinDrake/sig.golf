import SigGolfCandidate.T3M.Witness.CanonicalHonest
import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Final.CanonicalWitnessRom
import SigGolfCandidate.T3M.Final.CanonicalRomMono

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Bridge
open SigGolfCandidate.T3M.Final CanonicalAdapter

theorem verifyC_adapted_counted_eval (answers : Correctness.Answers)
    (m : Message) (pk : Digest) (w : WBytes) :
    evalWithAnswerFn answers (Cost.countCalls (verifyC m pk w))=
      evalWithAnswerFn answers (Cost.countCalls (adaptedOld m pk w)) := by
  unfold verifyC adaptedOld
  rw [counted_bind_eval,counted_bind_eval]
  generalize hd : evalWithAnswerFn answers (Cost.countCalls (digestP m w))=r
  obtain ⟨o,n⟩ := r
  cases o with
  | none => rfl
  | some a =>
    dsimp only
    rw [verifyP_eq_tail,counted_bind_eval,counted_bind_eval,digestP_normalize,hd]
    simp only [ne_eq,not_true_eq_false,if_false]

theorem pubGood_digestP (m : Message) (w : WBytes) :
    AllQueriesSatisfy (digestP m w) PubGood := by
  unfold digestP
  exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))

theorem pubGood_verifyTailP (pk : Digest) (w : WBytes) (a : HashOutput) :
    AllQueriesSatisfy (verifyTailP pk w a) PubGood := by
  unfold verifyTailP
  refine allQ_ite _ (allQ_pure _) (allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_ftsP _ _ _) fun r => ?_))
  cases r with
  | none => exact allQ_pure _
  | some root =>
    refine allQ_bind (pubGood_layersP _ _ _ _) fun r => ?_
    cases r <;> exact allQ_pure _

theorem pubGood_verifyC (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyC m pk w) PubGood := by
  unfold verifyC
  refine allQ_bind (pubGood_digestP _ _) fun r => ?_
  cases r with
  | none => exact allQ_pure _
  | some a =>
    refine allQ_bind (pubGood_digestP _ _) fun r => ?_
    cases r with
    | none => exact allQ_pure _
    | some b => exact allQ_ite _ (allQ_pure _) (pubGood_verifyTailP _ _ _)

noncomputable def checkForgeryC (pk : Digest) (log : QueryLog T3.Security.Requests) : ForgeryP → M Bool := by
  classical
  exact fun f => match f with
  | .witness m w => do
    let b ← verifyC m pk w
    pure (decide (¬∃ e∈log,e.1.message=m ∧ e.2.isSome=true) && b)
  | .signature m sig => do
    let some w ← expandB m pk sig | pure false
    let b ← verifyC m pk w
    pure (decide (¬∃ e∈log,e.1.message=m ∧ e.2=some sig) && b)

/-- The signature branch spends one public hash call and keeps the same signature.
Its value is unused; this matches the new verifier's extra charged replay. -/
def adaptForgery : ForgeryP → M (Option ForgeryP)
  | .witness m w => do
    let some a ← digestP m w | pure none
    pure (some (.witness m (normalize (selections a) w)))
  | .signature m sig => do
    let _ ← digest sig.rho m 0
    pure (some (.signature m sig))

noncomputable def adaptedCheck (pk : Digest) (log : QueryLog T3.Security.Requests) (f : ForgeryP) : M Bool := do
  let some g ← adaptForgery f | pure false
  checkForgeryP pk log g

theorem adapt_witness_check (pk : Digest) (log : QueryLog T3.Security.Requests) (m : Message) (w : WBytes) :
    adaptedCheck pk log (.witness m w)=
      (fun b => decide (¬∃ e∈log,e.1.message=m ∧ e.2.isSome=true) && b) <$> adaptedOld m pk w := by
  classical
  unfold adaptedCheck adaptForgery adaptedOld checkForgeryP
  simp only [bind_assoc,map_bind,pure_bind,map_pure]
  congr 1
  funext r
  cases r <;> simp [map_eq_bind_pure_comp]

theorem counted_map_eval {α β : Type} (answers : Correctness.Answers) (p : M α) (f : α → β) :
    evalWithAnswerFn answers (Cost.countCalls (f <$> p))=
      let r := evalWithAnswerFn answers (Cost.countCalls p)
      (f r.1,r.2) := by
  rw [map_eq_bind_pure_comp,counted_bind_eval]
  simp only [Cost.countCalls,Cost.countWith_pure,evalWithAnswerFn_pure,Nat.add_zero,Function.comp_def]

theorem check_witness_eval (answers : Correctness.Answers) (pk : Digest)
    (log : QueryLog T3.Security.Requests) (m : Message) (w : WBytes) :
    evalWithAnswerFn answers (Cost.countCalls (checkForgeryC pk log (.witness m w)))=
      evalWithAnswerFn answers (Cost.countCalls (adaptedCheck pk log (.witness m w))) := by
  classical
  rw [adapt_witness_check,counted_map_eval,←verifyC_adapted_counted_eval]
  unfold checkForgeryC
  rw [counted_bind_eval]
  simp only [Cost.countCalls,Cost.countWith_pure,evalWithAnswerFn_pure,Nat.add_zero]

theorem counted_digest_call (answers : Correctness.Answers) (rho : Digest) (m : Message) (dc : BitVec 32) :
    evalWithAnswerFn answers (Cost.countCalls (digest rho m dc))=
      (evalWithAnswerFn answers (digest rho m dc),1) := by
  simp only [digest,publicHash,Cost.countCalls,Cost.countWith_query,evalWithAnswerFn_map]
  rw [Cost.countWith_query,evalWithAnswerFn_map]

theorem adapt_signature_check (pk : Digest) (log : QueryLog T3.Security.Requests) (m : Message) (sig : Signature) :
    adaptedCheck pk log (.signature m sig)=(do
      let _ ← digest sig.rho m 0
      checkForgeryP pk log (.signature m sig)) := by
  unfold adaptedCheck adaptForgery
  simp only [bind_assoc,pure_bind]

theorem check_signature_eval (answers : Correctness.Answers) (pk : Digest)
    (log : QueryLog T3.Security.Requests) (m : Message) (sig : Signature) :
    WinCount (evalWithAnswerFn answers (Cost.countCalls (checkForgeryC pk log (.signature m sig))))
      (evalWithAnswerFn answers (Cost.countCalls (adaptedCheck pk log (.signature m sig)))) := by
  classical
  have hR : evalWithAnswerFn answers (Cost.countCalls (adaptedCheck pk log (.signature m sig)))=
      let r := evalWithAnswerFn answers (Cost.countCalls (checkForgeryP pk log (.signature m sig)))
      (r.1,1+r.2) := by
    rw [adapt_signature_check,counted_bind_eval,counted_digest_call]
  rw [hR]
  unfold checkForgeryC checkForgeryP
  change WinCount (evalWithAnswerFn answers (Cost.countCalls (do
      let some w ← expandB m pk sig | pure false
      let b ← verifyC m pk w
      pure (decide (¬∃ e∈log,e.1.message=m ∧ e.2=some sig) && b))))
    (let r := evalWithAnswerFn answers (Cost.countCalls (do
      let some w ← expandB m pk sig | pure false
      let b ← verifyP m pk w
      pure (decide (¬∃ e∈log,e.1.message=m ∧ e.2=some sig) && b)))
    (r.1,1+r.2))
  rw [counted_bind_eval,counted_bind_eval]
  unfold expandB
  simp only [counted_map_eval]
  generalize he : evalWithAnswerFn answers (Cost.countCalls (expandN m pk sig))=r
  obtain ⟨o,n⟩ := r
  cases o with
  | none =>
    simp [WinCount,Cost.countCalls]
  | some pair =>
    obtain ⟨a,w⟩ := pair
    have hex : evalWithAnswerFn answers (expandN m pk sig)=some (a,w) := by
      have hh := congrArg Prod.fst he
      simpa only [eval_countCalls_fst] using hh
    simp only [Option.map_some]
    rw [counted_bind_eval,counted_bind_eval,verifyC_witEnc_counted_eval answers m pk sig a w hex]
    simp only [Cost.countCalls,Cost.countWith_pure,evalWithAnswerFn_pure,Nat.add_zero]
    intro hb
    refine ⟨hb,?_⟩
    omega

#print axioms check_signature_eval
theorem check_counted_eval (answers : Correctness.Answers) (pk : Digest)
    (log : QueryLog T3.Security.Requests) (f : ForgeryP) :
    WinCount (evalWithAnswerFn answers (Cost.countCalls (checkForgeryC pk log f)))
      (evalWithAnswerFn answers (Cost.countCalls (adaptedCheck pk log f))) := by
  cases f with
  | witness m w =>
    rw [check_witness_eval]
    exact fun h => ⟨h,le_rfl⟩
  | signature m sig => exact check_signature_eval answers pk log m sig

theorem pubGood_checkC (pk : Digest) (log : QueryLog T3.Security.Requests) (f : ForgeryP) :
    AllQueriesSatisfy (checkForgeryC pk log f) PubGood := by
  cases f with
  | witness m w =>
    unfold checkForgeryC
    exact allQ_bind (pubGood_verifyC _ _ _) fun _ => allQ_pure _
  | signature m sig =>
    unfold checkForgeryC
    refine allQ_bind (pubGood_expandB _ _ _) fun r => ?_
    cases r with
    | none => exact allQ_pure _
    | some w => exact allQ_bind (pubGood_verifyC _ _ _) fun _ => allQ_pure _

theorem pubGood_checkP (pk : Digest) (log : QueryLog T3.Security.Requests) (f : ForgeryP) :
    AllQueriesSatisfy (checkForgeryP pk log f) PubGood := by
  cases f with
  | witness m w =>
    unfold checkForgeryP
    exact allQ_bind (pubGood_verifyP _ _ _) fun _ => allQ_pure _
  | signature m sig =>
    unfold checkForgeryP
    refine allQ_bind (pubGood_expandB _ _ _) fun r => ?_
    cases r with
    | none => exact allQ_pure _
    | some w => exact allQ_bind (pubGood_verifyP _ _ _) fun _ => allQ_pure _

theorem pubGood_adaptForgery (f : ForgeryP) : AllQueriesSatisfy (adaptForgery f) PubGood := by
  cases f with
  | witness m w =>
    unfold adaptForgery
    refine allQ_bind (pubGood_digestP _ _) fun r => ?_
    cases r <;> exact allQ_pure _
  | signature m sig =>
    unfold adaptForgery
    exact allQ_bind (pubGood_digest _ _ _) fun _ => allQ_pure _

theorem pubGood_adaptedCheck (pk : Digest) (log : QueryLog T3.Security.Requests) (f : ForgeryP) :
    AllQueriesSatisfy (adaptedCheck pk log f) PubGood := by
  unfold adaptedCheck
  refine allQ_bind (pubGood_adaptForgery _) fun r => ?_
  cases r with
  | none => exact allQ_pure _
  | some g => exact pubGood_checkP _ _ _

#print axioms verifyC_adapted_counted_eval
#print axioms check_witness_eval
end SigGolfCandidate.T3M.CanonicalSource
