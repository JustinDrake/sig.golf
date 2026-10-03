import SigGolfCandidate.T3M.Final.CanonicalSecurityTail

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Bridge
open SigGolfCandidate.T3M.Final

def hashAnswers (hash : QueryImpl AHash Id) (sk : BitVec 256) : Correctness.Answers :=
  fun q => evalWithAnswerFn hash (hHandler sk q)

theorem eval_hrealize {α : Type} (hash : QueryImpl AHash Id) (sk : BitVec 256) (p : M α) :
    evalWithAnswerFn hash (hrealize sk p)=evalWithAnswerFn (hashAnswers hash sk) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [hrealize_query_bind,evalWithAnswerFn_bind,evalWithAnswerFn_bind]
    have he : evalWithAnswerFn (hashAnswers hash sk) (Spec.query q : M _)=
        evalWithAnswerFn hash (hHandler sk q) := evalWithAnswerFn_query _ q
    rw [he,ih]

theorem hrealize_count_one {α : Type} (sk : BitVec 256) (p : M α)
    (hp : AllQueriesSatisfy p isHash) (c : Nat) :
    hrealize sk (countFrom (fun _ => 1) p c)=
      countFrom (fun _ => 1) (hrealize sk p) c := by
  induction p using OracleComp.inductionOn generalizing c with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hp
    rw [countFrom_query_bind,hrealize_query_bind,hrealize_query_bind]
    cases q with
    | inl x =>
      cases x with
      | inl n => exact hp.1.elim
      | inr input =>
        change ((AHash.query input : OracleComp AHash _) >>= _) =
          countFrom (fun _ => 1) ((AHash.query input : OracleComp AHash _) >>= _) c
        rw [countFrom_query_bind]
        exact bind_congr fun a => ih a (hp.2 a) (c+1)
    | inr coord =>
      change ((AHash.query (privateInput sk coord) : OracleComp AHash _) >>= _) =
        countFrom (fun _ => 1) ((AHash.query (privateInput sk coord) : OracleComp AHash _) >>= _) c
      rw [countFrom_query_bind]
      exact bind_congr fun a => ih a (hp.2 a) (c+1)

theorem hrealize_count_calls {α : Type} (sk : BitVec 256) (p : M α)
    (hp : AllQueriesSatisfy p isHash) :
    hrealize sk (Cost.countCalls p)=Bridge.countCalls (hrealize sk p) :=
  hrealize_count_one sk p hp 0

theorem check_hash_event (sk : BitVec 256) (pk : Digest) (log : QueryLog T3.Security.Requests)
    (f : ForgeryP) (c q : Nat) (cache : QueryCache AHash) :
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ randomOracle (countFrom (fun _ => 1) (hrealize sk (checkForgeryC pk log f)) c)).run' cache] ≤
    Pr[fun r => r.1=true ∧ r.2≤q |
      (simulateQ randomOracle (countFrom (fun _ => 1) (hrealize sk (adaptedCheck pk log f)) c)).run' cache] := by
  apply randomOracle_event_mono_cache
  intro hash he
  rw [countFrom_shift,evalWithAnswerFn_map] at he ⊢
  change (evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (checkForgeryC pk log f)))).1=true ∧
      c+(evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (checkForgeryC pk log f)))).2≤q at he
  change (evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (adaptedCheck pk log f)))).1=true ∧
      c+(evalWithAnswerFn hash (Bridge.countCalls (hrealize sk (adaptedCheck pk log f)))).2≤q
  rw [←hrealize_count_calls sk _ (T3M.allQ_mono (pubGood_checkC pk log f) (fun _ h => h.hashGood.1)),eval_hrealize] at he
  rw [←hrealize_count_calls sk _ (T3M.allQ_mono (pubGood_adaptedCheck pk log f) (fun _ h => h.hashGood.1)),eval_hrealize]
  have hh := check_counted_eval (hashAnswers hash sk) pk log f he.1
  exact ⟨hh.1,by omega⟩

#print axioms check_hash_event
end SigGolfCandidate.T3M.CanonicalSource
