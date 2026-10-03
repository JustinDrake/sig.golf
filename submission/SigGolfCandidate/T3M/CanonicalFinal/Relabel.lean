import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Witness.Honest
import SigGolfCandidate.Bridge.Basic

/-!
# Core's programs on the source oracle, and the relabeling to the organizer's (MACH-PLAN §1.2–1.3)

`hrealize sk p` runs a Core program `p : T3.M α` on the source hash oracle `AHash = List UInt8 →ₒ BitVec 256`:
public inputs as they are, private coordinates realized by the secret (`privateInput sk`), coins answered by
`0` (Core's programs are hash-only, so this branch is never taken on them). Then

* `mrealize_eq_relabel : mrealize sk p = relabel toQ (hrealize sk p)` (M0's machine reference is the
  relabeling of `hrealize` by `toQ`);
* `relabel_ofQ_toQ` : on aligned queries, `ofQ` undoes `toQ`;
* `allQ_hrealize` : a program whose public queries are nonempty and 64-aligned (`Cost.GoodQuery`) makes only
  aligned source queries;
* `realize_eq_liftM` : on a hash-only program, Core's `realize` (into `OracleWorld = unifSpec + HashSpec`) is
  the lift of `hrealize`;
* `hrealize_public` : a public-only program does not depend on the secret;
* `countCalls_eq` : M0's `countCalls` is the bridge's `countCalls`.
-/

namespace SigGolfCandidate.T3M.CanonicalFinal
open OracleComp OracleSpec SigGolfCandidate.Bridge
open SigGolfCandidate.T3 (M Spec privateInput realize realHandler Coordinate)

/-- The source hash oracle with the literal output width (definitionally `SphincsSecurity.HashSpec`). -/
abbrev AHash := List UInt8 →ₒ BitVec 256

/-- The source world (definitionally `SphincsSecurity.OracleWorld`). -/
abbrev AW := unifSpec + AHash

/-- Core's queries on the source oracle. -/
def hHandler (sk : BitVec 256) : QueryImpl Spec (OracleComp AHash)
  | .inl (.inl n) => (Pure.pure (0 : Fin (n + 1)) : OracleComp AHash (Fin (n + 1)))
  | .inl (.inr input) => (AHash.query input : OracleComp AHash _)
  | .inr c => (AHash.query (privateInput sk c) : OracleComp AHash _)

/-- A Core program on the source oracle, private coordinates realized by `sk`. -/
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

/-! ## `mrealize` is the relabeling of `hrealize` by `toQ` -/

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

/-! ## Aligned queries -/

theorem relabel_ofQ_toQ {α : Type} {X : OracleComp AHash α} (h : AllQ Aligned X) :
    relabel ofQ (relabel toQ X) = X := by
  rw [relabel_relabel]
  exact relabel_eq_self_of_allQ Aligned _ (fun x hx => ofQ_toQ hx) h

/-- A Core program's queries all satisfying `Cost.GoodQuery` (public inputs nonempty and 64-aligned)
realize to aligned source queries. -/
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

/-! ## Hash-only programs: `realize` is the lift of `hrealize` -/

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

/-! ## Public-only programs do not depend on the secret -/

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

/-! ## Counters -/

/-- M0's call counter is the bridge's. -/
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

end SigGolfCandidate.T3M.CanonicalFinal
