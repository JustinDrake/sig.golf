import SigGolfCandidate.T3M.Final.Pending
import SigGolfCandidate.T3M.Final.Relabel
import SigGolfCandidate.Legacy.Security

/-!
# Bridge setup: the implementation equations on the source oracle

The machine statements (`Pending`) relate each program run to `countBoth`/`countCalls` of `mrealize`. Here they
are restated in the form the security bridge uses: the organizer program's `(value, hashCalls)` is the bridge's
`countCalls` of the **relabeled source program** `relabel toQ (hrealize sk p)` (`keygen_eq`, `sign_eq`, `expand_eq`,
`verify_eq`), and relabeling back by `ofQ` gives the source program itself (`ofQ_countCalls`), because every query is
aligned. `QFacts` collects the query-shape facts this needs; `Main` proves it from `SourceFacts` and stream W.

Also: `costW` (hash calls cost one, coins zero), `countHashQueries_eq` (`SphincsSecurity.countHashQueries` is
`countFrom costW · 0`), `derivation_realize` (the Derivation realization of `realExperiment` is Core's `realize`),
`sampleSecretKey_eq` (the organizer's secret-key sampler is the master-seed sampler).
-/

namespace SigGolfCandidate.T3M.Final
open SigGolfCandidate.Legacy OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec keygen sign Signature Cache Digest privateInput realize)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits

/-- The query-shape facts of the four programs the security bridge relates (hash-only, public, aligned). -/
structure QFacts : Prop where
  hashOnly_keygen : AllQueriesSatisfy keygen isHash
  hashOnly_sign : ∀ (c : Cache) (m : T3.Message), AllQueriesSatisfy (sign c m) isHash
  hashOnly_expandB : ∀ (m : T3.Message) (pk : Digest) (σ : Signature), AllQueriesSatisfy (expandB m pk σ) isHash
  hashOnly_verifyP : ∀ (m : T3.Message) (pk : Digest) (w : WBytes), AllQueriesSatisfy (verifyP m pk w) isHash
  public_expandB : ∀ (m : T3.Message) (pk : Digest) (σ : Signature), AllQueriesSatisfy (expandB m pk σ) isPublic
  public_verifyP : ∀ (m : T3.Message) (pk : Digest) (w : WBytes), AllQueriesSatisfy (verifyP m pk w) isPublic
  good_keygen : AllQueriesSatisfy keygen T3.Cost.GoodQuery
  good_sign : ∀ (c : Cache) (m : T3.Message), AllQueriesSatisfy (sign c m) T3.Cost.GoodQuery
  good_expandB : ∀ (m : T3.Message) (pk : Digest) (σ : Signature),
    AllQueriesSatisfy (expandB m pk σ) T3.Cost.GoodQuery
  good_verifyP : ∀ (m : T3.Message) (pk : Digest) (w : WBytes),
    AllQueriesSatisfy (verifyP m pk w) T3.Cost.GoodQuery

/-! ## From the joint counter to calls -/

/-- A refinement with the joint counter gives the bridge's call counter of the same program. -/
theorem calls_of_counts {β γ : Type} {run : OracleComp HashSpec (RunResult β)}
    {X : OracleComp HashSpec γ} {F : γ → Option β}
    (h : (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> run =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth X) :
    (fun r => (r.value, r.hashCalls)) <$> run = (fun p => (F p.1, p.2)) <$> Bridge.countCalls X := by
  have h2 := congrArg (fun x => (fun t : Option β × Nat × Nat => (t.1, t.2.1)) <$> x) h
  simp only [Functor.map_map] at h2
  rw [h2, ← countCalls_eq, ← countBoth_calls, Functor.map_map]

theorem ofQ_countCalls {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (Bridge.countCalls (relabel toQ X)) = Bridge.countCalls X := by
  rw [relabel_countCalls, relabel_ofQ_toQ h]

/-! ## The implementation equations -/

section eqs

set_option maxRecDepth 100000 in
theorem keygen_eq (P : Pending) (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .keygen sk =
      (fun p => (some ((p.1.1 : PublicKey), cacheB p.1.2), p.2)) <$>
        Bridge.countCalls (relabel toQ (hrealize sk keygen)) := by
  have h := calls_of_counts (F := fun p : Digest × Cache => some ((p.1 : PublicKey), cacheB p.2))
    (P.keygen_run_counts sk)
  rw [mrealize_eq_relabel] at h
  exact h

set_option maxRecDepth 100000 in
theorem sign_eq (P : Pending) (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, m) =
      (fun p => (p.1.map sigB, p.2)) <$>
        Bridge.countCalls (relabel toQ (hrealize sk (sign (cacheDec cache) m))) := by
  have h := calls_of_counts (F := Option.map sigB) (P.sign_refines sk cache m)
  rw [mrealize_eq_relabel] at h
  exact h

set_option maxRecDepth 100000 in
theorem expand_eq (P : Pending) (m : Message) (pk : PublicKey) (s : Bytes 5664) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (m, pk, s) =
      Bridge.countCalls (relabel toQ (hrealize 0 (expandB m pk (sigDec s)))) := by
  have h := calls_of_counts (F := Option.map (fun x : T3.HashOutput × T3.Witness => witEnc x.1 x.2))
    (P.expand_refines m pk s)
  rw [mrealize_eq_relabel] at h
  refine h.trans ?_
  rw [expandB, hrealize_map, relabel_map]
  unfold Bridge.countCalls
  rw [countFrom_map]

set_option maxRecDepth 100000 in
theorem verify_eq (P : Pending) (m : Message) (pk : PublicKey) (w : Bytes 25240) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$>
        Bridge.countCalls (relabel toQ (hrealize 0 (verifyP m pk w))) := by
  rw [P.verify_refines m pk w, countCalls_eq, mrealize_eq_relabel]

end eqs

/-! ## The source experiment's ingredients -/

/-- Hash calls cost one, coins zero. -/
def costW : AW.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem countHashQueries_eq {α : Type} (X : OracleComp SphincsSecurity.OracleWorld α) :
    SphincsSecurity.countHashQueries X = countFrom costW X 0 := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    rw [SphincsSecurity.countHashQueries_query_bind, countFrom_query_bind]
    refine bind_congr fun u => ?_
    rw [ih u, countFrom_shift _ _ (0 + costW t)]
    rcases t with n | x <;> simp [costW]

theorem derivation_realize {α : Type} (secret : BitVec 256) (p : M α) :
    T3.Derivation.realize (privateInput secret) p = realize secret p := by
  unfold T3.Derivation.realize realize
  congr 1
  funext q
  rcases q with q | c <;> rfl

theorem sampleSecretKey_eq : (sampleSecretKey : ProbComp SecretKey) = SphincsSecurity.sampleMasterSeed := rfl

end SigGolfCandidate.T3M.Final
