import SigGolfCandidate.T3M.Witness.CanonicalSource
import SigGolfCandidate.T3M.Witness.Honest

/-! Pointwise replay of successful expansions through the new source verifier.
The repeated digest call is charged, even when its answer is cached. -/
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3
open CanonicalAdapter
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false

theorem counted_bind_eval {α β : Type} (answers : Correctness.Answers)
    (p : M α) (k : α → M β) :
    evalWithAnswerFn answers (Cost.countCalls (p >>= k))=
      let a := evalWithAnswerFn answers (Cost.countCalls p)
      let b := evalWithAnswerFn answers (Cost.countCalls (k a.1))
      (b.1,a.2+b.2) := by
  unfold Cost.countCalls
  rw [Cost.countWith_bind,evalWithAnswerFn_bind,evalWithAnswerFn_map]

theorem counted_digest_eval (answers : Correctness.Answers) (m : Message) (w : WBytes)
    (N : HashOutput) (hd : (wdc w).toNat<attemptLimit)
    (hn : evalWithAnswerFn answers (digest (wrho w) m (wdc w))=N) :
    evalWithAnswerFn answers (Cost.countCalls (digestP m w))=(some N,1) := by
  unfold digestP
  rw [if_neg (by omega)]
  unfold Cost.countCalls
  rw [map_eq_bind_pure_comp,Cost.countWith_bind]
  simp only [Cost.countWith_pure,
    digest,publicHash,Cost.countWith_query,evalWithAnswerFn_bind,evalWithAnswerFn_map,
    evalWithAnswerFn_pure,Nat.add_zero,Function.comp_def]
  rw [Cost.countWith_query]
  simp only [evalWithAnswerFn_map]
  simpa only [digest,publicHash] using congrArg (fun x => (some x,1)) hn

theorem verifyC_counted_eval (answers : Correctness.Answers) (m : Message) (pk : Digest)
    (w : WBytes) (N : HashOutput) (hd : (wdc w).toNat<attemptLimit)
    (hn : evalWithAnswerFn answers (digest (wrho w) m (wdc w))=N) :
    evalWithAnswerFn answers (Cost.countCalls (verifyC m pk w))=
      let r := evalWithAnswerFn answers
        (Cost.countCalls (verifyTailP pk (normalize (selections N) w) N))
      (r.1,2+r.2) := by
  have hD := counted_digest_eval answers m w N hd hn
  unfold verifyC
  rw [counted_bind_eval,hD]
  dsimp only
  rw [counted_bind_eval,hD]
  dsimp only
  simp only [ne_eq,not_true_eq_false,if_false]
  congr 1
  omega

theorem verifyC_witEnc_counted_eval (answers : Correctness.Answers) (m : Message)
    (pk : Digest) (sig : Signature) (N : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (expandN m pk sig)=some (N,w)) :
    evalWithAnswerFn answers (Cost.countCalls (verifyC m pk (witEnc N w)))=
      let r := evalWithAnswerFn answers (Cost.countCalls (verifyP m pk (witEnc N w)))
      (r.1,r.2+1) := by
  have F := expandN_facts answers m pk sig N w he
  have hs := selectionsOk_of_admissible N F.adm
  have hc := chosenOk_of N hs
  have hf := slotBase_seven_le N hc F.adm
  have hdc : (wdc (witEnc N w)).toNat<attemptLimit := by rw [wdc_witEnc]; exact F.dc
  have hN : evalWithAnswerFn answers (digest (wrho (witEnc N w)) m (wdc (witEnc N w)))=N := by
    rw [wrho_witEnc,wdc_witEnc,F.sig]; exact F.digest
  have hD := counted_digest_eval answers m (witEnc N w) N hdc hN
  rw [verifyC_counted_eval answers m pk (witEnc N w) N hdc hN,
    normalize_witEnc N w hc hf,verifyP_eq_tail,counted_bind_eval,hD]
  dsimp only
  congr 1
  omega

theorem verifyC_witEnc_eval (answers : Correctness.Answers) (m : Message)
    (pk : Digest) (sig : Signature) (N : HashOutput) (w : Witness)
    (he : evalWithAnswerFn answers (expandN m pk sig)=some (N,w)) :
    evalWithAnswerFn answers (verifyC m pk (witEnc N w))=
      evalWithAnswerFn answers (verifyP m pk (witEnc N w)) := by
  have hh := congrArg Prod.fst (verifyC_witEnc_counted_eval answers m pk sig N w he)
  simpa only [eval_countCalls_fst] using hh

def honestProgramC (m : Message) : M Bool := do
  let keys ← keygen
  let sig ← sign keys.2 m
  let some sig := sig | return false
  let wb ← expandB m keys.1 sig
  let some wb := wb | return false
  verifyC m keys.1 wb

theorem honestC_eval (answers : Correctness.Answers) (m : Message) :
    evalWithAnswerFn answers (honestProgramC m)=evalWithAnswerFn answers (honestProgramCore m) := by
  rw [← honestB_eval answers m]
  unfold honestProgramC honestProgramB
  simp only [evalWithAnswerFn_bind]
  cases hsign : evalWithAnswerFn answers (sign (evalWithAnswerFn answers keygen).2 m) with
  | none => rfl
  | some sig =>
    dsimp only
    simp only [evalWithAnswerFn_bind]
    rw [eval_expandB]
    cases hex : evalWithAnswerFn answers (expandN m (evalWithAnswerFn answers keygen).1 sig) with
    | none => rfl
    | some pair =>
      obtain ⟨N,w⟩ := pair
      try dsimp only
      exact verifyC_witEnc_eval answers m _ sig N w hex

#print axioms verifyC_witEnc_counted_eval
#print axioms honestC_eval
end SigGolfCandidate.T3M.CanonicalSource
