import SigGolfCandidate.T3M.Witness.CanonicalSource
import SigGolfCandidate.T3M.Final.CanonicalRel
import SigGolfCandidate.T3M.Final.BridgeSetup

/-! The counted witness reduction after private-coordinate realization and
lazy random-oracle simulation, at any initial counter and cache. -/
namespace SigGolfCandidate.T3M.CanonicalSource
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.Bridge
open SigGolfCandidate.T3M.Final

def costS : Spec.Domain → Nat
  | .inl (.inl _) => 0
  | _ => 1

theorem realize_countFrom {α : Type} (sk : BitVec 256) (p : M α) (c : Nat) :
    realize sk (countFrom costS p c)=countFrom costW (realize sk p) c := by
  induction p using OracleComp.inductionOn generalizing c with
  | pure a => rfl
  | query_bind q k ih =>
    rw [countFrom_query_bind]
    simp only [realize,simulateQ_bind,simulateQ_query]
    rcases q with (n | input) | coord
    · change ((SphincsSecurity.OracleWorld.query (.inl n) : OracleComp SphincsSecurity.OracleWorld _) >>= fun a =>
        realize sk (countFrom costS (k a) (c+0))) =
        countFrom costW ((SphincsSecurity.OracleWorld.query (.inl n) : OracleComp SphincsSecurity.OracleWorld _) >>=
          fun a => realize sk (k a)) c
      rw [countFrom_query_bind]
      simp only [costW,Nat.add_zero]
      exact bind_congr fun a => ih a c
    · change ((SphincsSecurity.OracleWorld.query (.inr input) : OracleComp SphincsSecurity.OracleWorld _) >>= fun a =>
        realize sk (countFrom costS (k a) (c+1))) =
        countFrom costW ((SphincsSecurity.OracleWorld.query (.inr input) : OracleComp SphincsSecurity.OracleWorld _) >>=
          fun a => realize sk (k a)) c
      rw [countFrom_query_bind]
      exact bind_congr fun a => ih a (c+1)
    · change ((SphincsSecurity.OracleWorld.query (.inr (privateInput sk coord)) : OracleComp SphincsSecurity.OracleWorld _) >>= fun a =>
        realize sk (countFrom costS (k a) (c+1))) =
        countFrom costW ((SphincsSecurity.OracleWorld.query (.inr (privateInput sk coord)) : OracleComp SphincsSecurity.OracleWorld _) >>=
          fun a => realize sk (k a)) c
      rw [countFrom_query_bind]
      exact bind_congr fun a => ih a (c+1)

theorem witness_rom (sk : BitVec 256) (m : Message) (pk : Digest) (w : WBytes)
    (c q : Nat) (cache : QueryCache SphincsSecurity.HashSpec) :
    Pr[fun r => r.1=true ∧ r.2 ≤ q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (verifyC m pk w)) c)).run' cache] ≤
    Pr[fun r => r.1=true ∧ r.2 ≤ q |
      (simulateQ SphincsSecurity.romImpl (countFrom costW (realize sk (adaptedOld m pk w)) c)).run' cache] := by
  have hh := (witness_reduction costS m pk w c).simulateQ (realHandler sk)
  change Rel (realize sk (countFrom costS (verifyC m pk w) c))
    (realize sk (countFrom costS (adaptedOld m pk w) c)) WinCount at hh
  rw [realize_countFrom,realize_countFrom] at hh
  apply hh.probEvent_le SphincsSecurity.romImpl
      (fun r => r.1=true ∧ r.2 ≤ q) (fun r => r.1=true ∧ r.2 ≤ q) _ cache
  intro a b hab ha
  have hb := hab ha.1
  exact ⟨hb.1,le_trans hb.2 ha.2⟩

#print axioms witness_rom
end SigGolfCandidate.T3M.CanonicalSource
