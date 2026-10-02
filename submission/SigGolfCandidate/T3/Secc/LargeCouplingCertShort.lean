import SigGolfCandidate.T3.Secc.LargeCouplingShort
import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs

/-!
# LR-34 (certificate coupling, short congruence): `CertR` reads its table only on short queries

`routerFold_short`, **`certR_short`**: for tables agreeing on every short query (F2's `ShortAgree`), the router fold
and the real certificate event coincide.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingCertShort : DecidableEq T3.Cache := Classical.decEq _

theorem routerStep_world (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : T3.Cache)
    (st : RouterState) (e : FirstHit.QueryEvent) : routerStep U A nv published st (.world e) = routerEvent U st e := rfl

theorem routerStep_sign (U : Finset HashInput) (A : Answers) (nv : Message → Digest) (published : T3.Cache)
    (st : RouterState) (request : Security.Request) (out : Option Signature) (events : List FirstHit.QueryEvent) :
    routerStep U A nv published st (.sign request out events) = signedState A nv published st request := rfl

section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT

theorem honestNonce_short : honestNonce A = honestNonce T := by
  funext m
  unfold honestNonce
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
  rw [hAT.priv]

theorem routeOk_short : RouteOk A = RouteOk T := by
  funext index
  apply propext
  unfold RouteOk
  simp only [Wots.Ref.referenceSearch_short hAT]

theorem signedState_short (nv : Message → Digest) (published : T3.Cache) (st : RouterState)
    (request : Security.Request) :
    signedState A nv published st request = signedState T nv published st request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  unfold signedState LargeResidual.signItems
  rw [signDigest_short hAT, hd, routeOk_short hAT]

theorem routerStep_short (U : Finset HashInput) (published : T3.Cache) (st : RouterState) (s : TaggedStep) :
    routerStep U A (honestNonce A) published st s = routerStep U T (honestNonce T) published st s := by
  cases s with
  | world e => rw [routerStep_world, routerStep_world]
  | sign request out events =>
      rw [routerStep_sign, routerStep_sign, honestNonce_short hAT, signedState_short hAT]

theorem steps_router_short (U : Finset HashInput) (published : T3.Cache) (steps : List TaggedStep) :
    ∀ st, steps.foldl (routerStep U A (honestNonce A) published) st =
      steps.foldl (routerStep U T (honestNonce T) published) st := by
  induction steps with
  | nil => intro st; rw [List.foldl_nil, List.foldl_nil]
  | cons s rest ih =>
      intro st
      rw [List.foldl_cons, List.foldl_cons, routerStep_short hAT, ih]

theorem routerFold_short (U : Finset HashInput) (published : T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    routerFold U A published steps verdict = routerFold U T published steps verdict := by
  unfold routerFold
  rw [steps_router_short hAT]

end Short

/-- **The real certificate event under short-agreeing tables.** -/
theorem certR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : CertR adversary q result A ↔ CertR adversary q result T := by
  unfold CertR
  simp only [monitorRun_short hAT, routerFold_short hAT]

end SigGolfCandidate.T3.Security.LargeCoupling
