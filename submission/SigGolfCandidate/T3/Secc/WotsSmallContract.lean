import SigGolfCandidate.T3.Secc.SeccClosing
import SigGolfCandidate.T3.Secc.WotsTransportSplit
import SigGolfCandidate.T3.Secc.PairGuessWorld

/-!
# Stream A: the case-(C) small-route contract (`CaseCSmallBound`)

The hypothesis the small route takes from stream CC (BP-B §1.3, on F2's pinned event `CaseCFreshPinned`): a clean fresh
case-(C) sample costs `(1 + cache)/2^128` per expected digest-class charge of the shared law, plus the flat crude-budget
BPORS excess `r·q·e/2^128`, the near-certificate-plus-one-guess term, B-PAIR's pair term and the proposal-prefix tail.

* `IsDigestQuery` / `digestClass`: class M (BP-B §1.2), a public digest input `pad64 (digestInput rho m ctr)`.
* `signRatio = 201`, `nearPrice = 203`, `nearTerm` (the designer's `exact.py` terms, as in BP-B's prototype).
* `CaseCSmallBound`: only for `1 ≤ q ≤ budgetSplit` (weaker than BP-B's `∀ q ≤ 2^127` form).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final

/-- Class M (BP-B §1.2): a public digest input. -/
def IsDigestQuery (input : T3.Spec.Domain) : Prop :=
  ∃ (rho : Digest) (message : Message) (counter : BitVec 32),
    input = .inl (.inr (pad64 (digestInput rho message counter)))

/-- Class M as a shared-law sample class (it reads no completion). -/
def digestClass : SeccLaw.SampleClass := fun _ input => IsDigestQuery input

/-- Crude-budget multiplier of the designer's model (T3 counts every hash call in `q`; kept as slack). -/
def signRatio : Nat := 201

/-- `near` = `fullNearPrice_bound` (sum over the 21 missing slots). -/
noncomputable def nearPrice : ENNReal := 203

/-- Near certificate + one guessed secret: `q/(n−q) · (near·q/n + 21·r·q·cache/n + 21·2^-700)`. -/
noncomputable def nearTerm (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (nearPrice * q / 2 ^ 128 + 21 * (signRatio * q : Nat) * SeccClosing.cacheRate / 2 ^ 128 +
      21 * (2 : ENNReal)⁻¹ ^ 700)

/-- **Case-(C) small-route contract** (BP-B §1.3 on the pinned event; stream CC). -/
def CaseCSmallBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosing.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosing.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq digestClass +
        ((signRatio * q : Nat) : ENNReal) * SeccClosing.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700

end SigGolfCandidate.T3.Security.Wots
