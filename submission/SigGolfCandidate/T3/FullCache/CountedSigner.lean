import SigGolfCandidate.T3.FullCache.KeySplit

namespace SiggolfT3Mac4.Source
open OracleComp OracleSpec ENNReal SphincsSecurity
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] tagRegion macTag macTagOf
abbrev T3M := SigGolfCandidate.T3.M
abbrev T3Spec := SigGolfCandidate.T3.Spec
abbrev T3Message := SigGolfCandidate.T3.Message
abbrev T3Signature := SigGolfCandidate.T3.Signature
abbrev CountState (S : Type) := Nat × S
def privateMacKey : T3M MacKey := do
  let k0 ← SigGolfCandidate.T3.privateHash (keyCoordinate 0)
  let k1 ← SigGolfCandidate.T3.privateHash (keyCoordinate 1)
  pure (fun i => if i = 0 then k0 else k1)
def privateMac (region : Region) : T3M MacTag := do
  let key ← privateMacKey
  pure (tagRegion key region)
noncomputable def sign (payload : Request T3Message → T3M (Option T3Signature))
    (request : Request T3Message) : T3M (Option T3Signature) := do
  let tag ← privateMac request.cache.region
  if tag = request.cache.tag then payload request else pure none
variable {S : Type}
noncomputable def tableHandler (world : Adaptive.Public (CountState S)) (table : FullTable) :
    QueryImpl T3Spec (StateT (CountState S) ProbComp)
  | .inl input => world input
  | .inr coordinate => StateT.mk fun state => pure (table coordinate,(state.1+1,state.2))
noncomputable def baseHandler (world : Adaptive.Public (CountState S)) (other : OtherTable) :
    QueryImpl T3Spec (StateT (CountState S) ProbComp) := tableHandler world (joinTable other (fun _ => 0))
theorem key_cases (key : MacKey) : (fun i : Fin 2 => if i = 0 then key 0 else key 1) = key := by
  funext i
  fin_cases i <;> simp
theorem privateMacKey_run (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (state : CountState S) :
    (simulateQ (tableHandler world (joinTable other key)) privateMacKey).run state =
      pure (key,(state.1+2,state.2)) := by
  simp [privateMacKey,SigGolfCandidate.T3.privateHash,simulateQ_bind,simulateQ_spec_query,
    tableHandler,StateT.run_bind,joinTable_key,key_cases,Nat.add_assoc]
theorem key_input_length (secret : BitVec 256) (i : Fin 2) :
    (SigGolfCandidate.T3.privateInput secret (keyCoordinate i)).length = 64 := by
  simp [SigGolfCandidate.T3.privateInput,keyCoordinate,SigGolfCandidate.T3.pad64,
    SigGolfCandidate.T3.zero16,bytesLE_length]
def NonMac : T3Spec.Domain → Prop
  | .inl _ => True
  | .inr c => c ≠ keyCoordinate 0 ∧ c ≠ keyCoordinate 1
theorem tableHandler_agrees (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (input : T3Spec.Domain) (h : NonMac input) :
    tableHandler world (joinTable other key) input = baseHandler world other input := by
  cases input with
  | inl input => rfl
  | inr coordinate =>
      have hk := joinTable_other other key (⟨coordinate,h⟩ : OtherCoordinate)
      have hz := joinTable_other other (fun _ => 0) (⟨coordinate,h⟩ : OtherCoordinate)
      simp only [baseHandler,tableHandler]
      rw [hk,hz]
theorem simulate_no_mac {α : Type} (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (program : T3M α) (h : AllQueriesSatisfy program NonMac) :
    simulateQ (tableHandler world (joinTable other key)) program = simulateQ (baseHandler world other) program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      obtain ⟨hinput,htail⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      rw [simulateQ_bind,simulateQ_bind,simulateQ_spec_query,simulateQ_spec_query,
        tableHandler_agrees world other key input hinput]
      exact congrArg (fun continuation => baseHandler world other input >>= continuation)
        (funext fun answer => ih answer (htail answer))
def keyCharge (_request : Request T3Message) : StateT (CountState S) ProbComp Unit :=
  StateT.mk fun state => pure ((),(state.1+2,state.2))
theorem sign_interpretation (world : Adaptive.Public (CountState S)) (other : OtherTable)
    (key : MacKey) (payload : Request T3Message → T3M (Option T3Signature))
    (hpayload : ∀ request, AllQueriesSatisfy (payload request) NonMac) (request : Request T3Message) :
    simulateQ (tableHandler world (joinTable other key)) (sign payload request) =
      Adaptive.realSigner keyCharge (fun request => simulateQ (baseHandler world other) (payload request))
        key request := by
  apply StateT.ext
  intro state
  unfold sign privateMac
  rw [bind_assoc]
  simp only [pure_bind,simulateQ_bind,StateT.run_bind,privateMacKey_run]
  by_cases ht : tagRegion key request.cache.region = request.cache.tag
  · simp only [if_pos ht,Adaptive.realSigner,keyCharge,StateT.run_bind,pure_bind]
    exact congrArg (fun p : StateT (CountState S) ProbComp (Option T3Signature) => p.run (state.1+2,state.2))
      (simulate_no_mac world other key _ (hpayload request))
  · simp only [if_neg ht,Adaptive.realSigner,keyCharge,StateT.run_bind,pure_bind]
    rfl
end SiggolfT3Mac4.Source
