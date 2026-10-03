import SigGolfCandidate.T3.Secc.LargeCouplingKeygen
import SigGolfCandidate.T3.Secc.SeccSufRoute

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingShort : DecidableEq T3.Cache := Classical.decEq _
section Short
variable {A T : Answers} (hAT : Wots.Ref.ShortAgree A T)
include hAT
theorem secretsOf_short : secretsOf A = secretsOf T := by
  funext s
  cases s with
  | inl x => exact Wots.Ref.leafSeed_short hAT _ _ _ _
  | inr f =>
      change ftsSecretOf A f = ftsSecretOf T f
      unfold ftsSecretOf
      dsimp only
      rw [Wots.Ref.ShortRespects.privatePair 8 f.coord.val f.index.val 0 (f.leaf.val / 2) A T hAT]
theorem honestValue_short : LargeResidual.honestValue A = LargeResidual.honestValue T := by
  funext c
  cases c with
  | inl N =>
      change (A (.inl (.inr (Extract.honestInput A N.toPos)))).extractLsb' 0 128 =
        (T (.inl (.inr (Extract.honestInput T N.toPos)))).extractLsb' 0 128
      rw [Wots.Ref.honestInput_short hAT _ (toPos_bounded N),
        hAT.public _ (Wots.Ref.honestInput_length T N.toPos)]
  | inr s =>
      change secretsOf A s = secretsOf T s
      rw [secretsOf_short hAT]
theorem contactTest_short (K : Coord → Prop) (X : HashInput) (y : HashOutput) :
    ContactTest A K X y ↔ ContactTest T K X y := by
  have hin : ∀ N : CanonGraph.Node, Extract.honestInput A N.toPos = Extract.honestInput T N.toPos :=
    fun N => Wots.Ref.honestInput_short hAT _ (toPos_bounded N)
  unfold ContactTest StructuralContact EncodingContact
  simp only [honestValue_short hAT, hin, Wots.Ref.referenceInput_short hAT, Wots.Ref.referenceDigits_short hAT]
theorem publicHash_respects (input : HashInput) (h : (pad64 input).length ≤ SeccLaw.maxInputLength) :
    Wots.Ref.ShortRespects (publicHash input) := by
  intro A' T' hAT'
  unfold publicHash
  change A' (.inl (.inr (pad64 input))) = T' (.inl (.inr (pad64 input)))
  exact hAT'.public _ h
theorem digestSearch_short (rho : Digest) (m : Message) :
    ∀ fuel c, evalWithAnswerFn A (digestSearch rho m c fuel) = evalWithAnswerFn T (digestSearch rho m c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; rfl
  | succ fuel ih =>
      intro c
      simp only [digestSearch, digest, evalWithAnswerFn_bind]
      have hlen : (pad64 (digestInput rho m (BitVec.ofNat 32 c))).length ≤ SeccLaw.maxInputLength := by
        rw [BPB.pad64_digestInput, BPB.digestInput_length]
        unfold SeccLaw.maxInputLength
        omega
      rw [publicHash_respects hAT _ hlen A T hAT]
      split_ifs
      · rfl
      · exact ih (c + 1)
theorem signDigest_short (m : Message) : LargeResidual.signDigest A m = LargeResidual.signDigest T m := by
  unfold LargeResidual.signDigest
  have hn : evalWithAnswerFn A (T3.privateNonce m) = evalWithAnswerFn T (T3.privateNonce m) := by
    simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    change (A (.inr (.inr (.inl m)))).extractLsb' 0 128 = (T (.inr (.inr (.inl m)))).extractLsb' 0 128
    rw [hAT.priv]
  rw [hn]
  exact digestSearch_short hAT _ _ _ _
theorem signDisclosed_short (published : T3.Cache) (request : Security.Request) :
    signDisclosed A published request = signDisclosed T published request := by
  have hd : Wots.referenceDigits A = Wots.referenceDigits T := funext (Wots.Ref.referenceDigits_short hAT)
  have hok : ∀ index, RouteOk A index ↔ RouteOk T index := by
    intro index
    unfold RouteOk
    simp only [Wots.Ref.referenceSearch_short hAT]
  unfold signDisclosed LargeResidual.signItems
  rw [signDigest_short hAT, hd]
  split_ifs
  · rcases LargeResidual.signDigest T request.message with _ | ⟨c, N⟩
    · rfl
    · simp only [hok]
  · rfl
theorem query_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (X : HashInput) (y : HashOutput) :
    mon.query U A q X y = mon.query U T q X y := by
  unfold Monitor.query
  simp only [contactTest_short hAT]
theorem event_short (U : Finset HashInput) (q : Nat) (mon : Monitor) (e : FirstHit.QueryEvent) :
    mon.event U A q e = mon.event U T q e := by
  rcases e with ⟨before, (n | X) | c, answer⟩
  · rfl
  · exact query_short hAT U q mon X answer
  · rfl
theorem events_short (U : Finset HashInput) (q : Nat) (events : List FirstHit.QueryEvent) (mon : Monitor) :
    events.foldl (Monitor.event U A q) mon = events.foldl (Monitor.event U T q) mon := by
  induction events generalizing mon with
  | nil => rfl
  | cons e rest ih => rw [List.foldl_cons, List.foldl_cons, event_short hAT, ih]
theorem steps_short (U : Finset HashInput) (q : Nat) (published : T3.Cache) (steps : List TaggedStep) (mon : Monitor) :
    steps.foldl (Monitor.step U A q published) mon = steps.foldl (Monitor.step U T q published) mon := by
  induction steps generalizing mon with
  | nil => rfl
  | cons s rest ih =>
      rw [List.foldl_cons, List.foldl_cons]
      have h1 : Monitor.step U A q published mon s = Monitor.step U T q published mon s := by
        cases s with
        | world e => exact event_short hAT U q mon e
        | sign request out events =>
            simp only [Monitor.step, Monitor.sign, signDisclosed_short hAT]
      rw [h1, ih]
theorem monitorRun_short (U : Finset HashInput) (q : Nat) (published : T3.Cache) (steps : List TaggedStep)
    (verdict : List FirstHit.QueryEvent) :
    monitorRun U A q published steps verdict = monitorRun U T q published steps verdict := by
  unfold monitorRun
  rw [steps_short hAT, events_short hAT]
end Short
def ContactR (adversary : AdversaryP) (q : Nat) (result : FirstHit.Recorded Bool) (A : Answers) : Prop :=
  ∀ generated tagged checked, TaggedSplit adversary result generated tagged checked →
    (monitorRun (Wots.referenceInputs adversary) A q generated.value.2 tagged.steps checked.events).contact = true
theorem contact_eq_contactR (adversary : AdversaryP) (q : Nat) (z : PaddedGame.TraceResult × Answers) :
    Contact adversary q z = ContactR adversary q (QueryRecorded.recordedTrace z.1) z.2 := rfl
theorem contactR_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (adversary : AdversaryP) (q : Nat)
    (result : FirstHit.Recorded Bool) : ContactR adversary q result A ↔ ContactR adversary q result T := by
  unfold ContactR
  simp only [monitorRun_short hAT]
end SigGolfCandidate.T3.Security.LargeCoupling
