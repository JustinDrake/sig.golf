import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Witness.Honest
import SigGolfCandidate.Bridge.Basic

namespace SigGolfCandidate.T3M.Final
open OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec privateInput realize realHandler Coordinate)
abbrev AHash := List UInt8 →ₒ BitVec 256
abbrev AW := unifSpec + AHash
def hHandler (sk : BitVec 256) : QueryImpl Spec (OracleComp AHash)
  | .inl (.inl n) => (Pure.pure (0 : Fin (n + 1)) : OracleComp AHash (Fin (n + 1)))
  | .inl (.inr input) => (AHash.query input : OracleComp AHash _)
  | .inr c => (AHash.query (privateInput sk c) : OracleComp AHash _)
def hrealize {α : Type} (sk : BitVec 256) (p : M α) : OracleComp AHash α :=
  simulateQ (hHandler sk) p
section basic
variable {α β : Type} (sk : BitVec 256)
@[simp] theorem hrealize_pure (a : α) : hrealize sk (Pure.pure a : M α) = Pure.pure a := rfl
theorem hrealize_bind (p : M α) (f : α → M β) :
    hrealize sk (p >>= f) = hrealize sk p >>= fun a => hrealize sk (f a) := by
  simp only [hrealize, simulateQ_bind]
theorem hrealize_map (f : α → β) (p : M α) : hrealize sk (f <$> p) = f <$> hrealize sk p := by
  simp only [hrealize, simulateQ_map]
theorem hrealize_query_bind (q : Spec.Domain) (k : Spec.Range q → M α) :
    hrealize sk ((liftM (Spec.query q) : M _) >>= k) = hHandler sk q >>= fun a => hrealize sk (k a) := by
  rw [hrealize_bind]
  congr 1
  simp [hrealize]
end basic
theorem mrealize_eq_relabel {α : Type} (sk : BitVec 256) (p : M α) :
    mrealize sk p = relabel toQ (hrealize sk p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [mrealize_bind, hrealize_query_bind, relabel_bind]
    have hq : mrealize sk (liftM (Spec.query q) : M _) = relabel toQ (hHandler sk q) := by
      rcases q with (n | input) | c
      · rfl
      · have e1 : mrealize sk (liftM (Spec.query (.inl (.inr input))) : M _) =
            (liftM (OracleSpec.query (spec := Legacy.HashSpec) (toQ input)) : OracleComp Legacy.HashSpec _) := by
          simp [mrealize, machineHandler]; exact id_map _
        exact e1.trans (relabel_query toQ input).symm
      · have e1 : mrealize sk (liftM (Spec.query (.inr c)) : M _) =
            (liftM (OracleSpec.query (spec := Legacy.HashSpec) (toQ (privateInput sk c))) :
              OracleComp Legacy.HashSpec _) := by
          simp [mrealize, machineHandler]
        exact e1.trans (relabel_query toQ (privateInput sk c)).symm
    rw [hq]
    exact bind_congr fun a => ih a
theorem relabel_ofQ_toQ {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (relabel toQ X) = X := by
  rw [relabel_relabel]
  exact relabel_eq_self_of_allQ Aligned _ (fun x hx => ofQ_toQ hx) h
theorem allQ_hrealize {α : Type} (sk : BitVec 256) {p : M α}
    (h : AllQueriesSatisfy p T3.Cost.GoodQuery) : AllQ Aligned (hrealize sk p) := by
  induction p using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind]
    rcases q with (n | input) | c
    · exact ih _ (h.2 _)
    · refine allQ_bind Aligned ((allQ_query Aligned input).mpr ?_) fun a => ih a (h.2 a)
      exact h.1
    · exact allQ_bind Aligned ((allQ_query Aligned _).mpr (privateInput_aligned sk c))
        fun a => ih a (h.2 a)
theorem realize_eq_liftM {α : Type} (sk : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isHash) :
    @Eq (OracleComp AW α) (realize sk p) (liftM (hrealize sk p)) := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind, liftM_bind]
    simp only [realize, simulateQ_bind, simulateQ_spec_query]
    rcases q with (n | input) | c
    · exact h.1.elim
    · exact bind_congr fun a => ih a (h.2 a)
    · exact bind_congr fun a => ih a (h.2 a)
theorem hrealize_public {α : Type} (sk sk' : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isPublic) :
    hrealize sk p = hrealize sk' p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at h
    rw [hrealize_query_bind, hrealize_query_bind]
    rcases q with (n | input) | c
    · exact h.1.elim
    · exact bind_congr fun a => ih a (h.2 a)
    · exact h.1.elim
theorem mrealize_public {α : Type} (sk sk' : BitVec 256) {p : M α} (h : AllQueriesSatisfy p isPublic) :
    mrealize sk p = mrealize sk' p := by
  rw [mrealize_eq_relabel, mrealize_eq_relabel, hrealize_public sk sk' h]
theorem countCalls_eq {α : Type} (X : OracleComp Legacy.HashSpec α) :
    countCalls X = Bridge.countCalls X := by
  induction X using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q k ih =>
    rw [countCalls_bind, countCalls_query]
    unfold Bridge.countCalls
    rw [countFrom_query_bind]
    simp only [bind_map_left]
    refine bind_congr fun a => ?_
    rw [ih a, Bridge.countCalls, countFrom_shift _ _ (0 + 1)]
end SigGolfCandidate.T3M.Final
