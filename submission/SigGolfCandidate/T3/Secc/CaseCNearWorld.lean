import SigGolfCandidate.T3.Secc.PairGuessLazyDefs
import SigGolfCandidate.T3.Secc.CaseCNearMem

/-!
# Stream CC: supermartingales over B-PAIR's lazy world programs (handler-level induction)

For any implementation `impl` of B-PAIR's lazy world spec `WSpecL` (e.g. `forcedImpl envL slot`) and any potential
`Φ : WStateL → ENNReal`, `SuperProg impl Φ W` says that running `W` from any state does not raise `Φ` in expectation.
It is closed under `pure`/`bind`, and the world programs inherit it from their handlers:

* `interactionL_super`: the interaction, from `coinReqL`, `hashL` and `signL`;
* `programL_super`: the verdict, from `coinReqL` and `hashL`;
* `worldGameCore_super`: the whole world game.
-/

namespace SigGolfCandidate.T3.Security.CaseC
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

section Generic
variable {Mem : Type}
variable (impl : QueryImpl BPair.WSpecL (StateT (SecretGuessObservation.State BPair.FtsCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State BPair.FtsCoord Digest Mem → ENNReal)

/-- Running `W` from any state does not raise `Φ` in expectation. -/
def SuperProg {β : Type} (W : OracleComp BPair.WSpecL β) : Prop :=
  ∀ s, expectedValue (SecretGuessObservation.runWith impl W s) (fun r => Φ r.2) ≤ Φ s

theorem runWith_bind' {β γ : Type} (W : OracleComp BPair.WSpecL β) (K : β → OracleComp BPair.WSpecL γ)
    (s : SecretGuessObservation.State BPair.FtsCoord Digest Mem) :
    SecretGuessObservation.runWith impl (W >>= K) s =
      SecretGuessObservation.runWith impl W s >>= fun r => SecretGuessObservation.runWith impl (K r.1) r.2 := by
  simp only [SecretGuessObservation.runWith, simulateQ_bind, StateT.run_bind]

theorem runWith_pure' {β : Type} (b : β) (s : SecretGuessObservation.State BPair.FtsCoord Digest Mem) :
    SecretGuessObservation.runWith impl (pure b) s = pure (b, s) := by
  simp only [SecretGuessObservation.runWith, simulateQ_pure, StateT.run_pure]

theorem superProg_pure {β : Type} (b : β) : SuperProg impl Φ (pure b : OracleComp BPair.WSpecL β) := by
  intro s
  rw [runWith_pure', expectedValue_pure]

theorem superProg_bind {β γ : Type} {W : OracleComp BPair.WSpecL β} {K : β → OracleComp BPair.WSpecL γ}
    (hW : SuperProg impl Φ W) (hK : ∀ b, SuperProg impl Φ (K b)) : SuperProg impl Φ (W >>= K) := by
  intro s
  rw [runWith_bind', expectedValue_bind]
  exact (expectedValue_mono _ fun (r : β × SecretGuessObservation.State BPair.FtsCoord Digest Mem) =>
    hK r.1 r.2).trans (hW s)

end Generic

section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U) {Mem : Type}
variable (impl : QueryImpl BPair.WSpecL (StateT (SecretGuessObservation.State BPair.FtsCoord Digest Mem) SPMF))
  (Φ : SecretGuessObservation.State BPair.FtsCoord Digest Mem → ENNReal)
noncomputable local instance instDecidableEqCache_caseCNearWorld : DecidableEq T3.Cache := Classical.decEq _

theorem interactionL_pure (ω : BPair.Omega U) (published : T3.Cache) {α : Type} (value : α) :
    BPair.interactionL hU ω published (pure value : OracleComp LazyPrivate.Interaction α) = pure (value, [], []) := rfl

theorem interactionL_coin (ω : BPair.Omega U) (published : T3.Cache) {α : Type} (n : Nat)
    (next : Fin (n + 1) → OracleComp LazyPrivate.Interaction α) :
    BPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inl n))) >>= next) =
      (BPair.coinReqL n >>= fun coin => BPair.interactionL hU ω published (next coin)) := rfl

theorem interactionL_public (ω : BPair.Omega U) (published : T3.Cache) {α : Type} (x : HashInput)
    (next : HashOutput → OracleComp LazyPrivate.Interaction α) :
    BPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inl (.inr x))) >>= next) =
      (BPair.hashL hU ω x >>= fun answer => BPair.interactionL hU ω published (next answer) >>= fun rest =>
        pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)) := rfl

theorem interactionL_request (ω : BPair.Omega U) (published : T3.Cache) {α : Type} (request : Request)
    (next : Option Signature → OracleComp LazyPrivate.Interaction α) :
    BPair.interactionL hU ω published (liftM (LazyPrivate.Interaction.query (.inr request)) >>= next) =
      (BPair.signL hU ω published request >>= fun signature => BPair.interactionL hU ω published (next signature) >>=
        fun rest => pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2)) := rfl

theorem programL_pure (ω : BPair.Omega U) {β : Type} (value : β) :
    BPair.programL hU ω (pure value : M β) = pure (value, []) := rfl

theorem programL_coin (ω : BPair.Omega U) {β : Type} (n : Nat) (next : Fin (n + 1) → M β) :
    BPair.programL hU ω (liftM (T3.Spec.query (.inl (.inl n))) >>= next) =
      (BPair.coinReqL n >>= fun coin => BPair.programL hU ω (next coin)) := rfl

theorem programL_public (ω : BPair.Omega U) {β : Type} (x : HashInput) (next : HashOutput → M β) :
    BPair.programL hU ω (liftM (T3.Spec.query (.inl (.inr x))) >>= next) =
      (BPair.hashL hU ω x >>= fun answer => BPair.programL hU ω (next answer) >>= fun rest =>
        pure (rest.1, (x, answer) :: rest.2)) := rfl

/-- **The interaction inherits the supermartingale property from its handlers.** -/
theorem interactionL_super (ω : BPair.Omega U) (published : T3.Cache)
    (hcoin : ∀ n, SuperProg impl Φ (BPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (BPair.hashL hU ω x))
    (hsign : ∀ request, SuperProg impl Φ (BPair.signL hU ω published request)) {α : Type}
    (oa : OracleComp LazyPrivate.Interaction α) : SuperProg impl Φ (BPair.interactionL hU ω published oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value =>
      rw [interactionL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | request
      · rw [interactionL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [interactionL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [interactionL_request]
        exact superProg_bind impl Φ (hsign request) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _

theorem programL_private (ω : BPair.Omega U) {β : Type} (c : Coordinate) (next : HashOutput → M β) :
    BPair.programL hU ω (liftM (T3.Spec.query (.inr c)) >>= next) = BPair.programL hU ω (next 0) := rfl

/-- **The verdict program inherits the supermartingale property from its handlers.** -/
theorem programL_super (ω : BPair.Omega U)
    (hcoin : ∀ n, SuperProg impl Φ (BPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (BPair.hashL hU ω x)) {β : Type}
    (program : M β) : SuperProg impl Φ (BPair.programL hU ω program) := by
  induction program using OracleComp.inductionOn with
  | pure value =>
      rw [programL_pure]
      exact superProg_pure impl Φ _
  | query_bind input next ih =>
      rcases input with (n | x) | c
      · rw [programL_coin]
        exact superProg_bind impl Φ (hcoin n) ih
      · rw [programL_public]
        exact superProg_bind impl Φ (hhash x) fun a =>
          superProg_bind impl Φ (ih a) fun _ => superProg_pure impl Φ _
      · rw [programL_private]
        exact ih (0 : HashOutput)

/-- **The world game inherits the supermartingale property from its handlers.** -/
theorem worldGameCore_super (ω : BPair.Omega U) (adversary : AdversaryP)
    (hcoin : ∀ n, SuperProg impl Φ (BPair.coinReqL n))
    (hhash : ∀ x, SuperProg impl Φ (BPair.hashL hU ω x))
    (hsign : ∀ published request, SuperProg impl Φ (BPair.signL hU ω published request)) :
    SuperProg impl Φ (BPair.worldGameCore hU ω adversary) := by
  unfold BPair.worldGameCore
  exact superProg_bind impl Φ (interactionL_super hU impl Φ ω _ hcoin hhash (hsign _) _) fun _ =>
    superProg_bind impl Φ (programL_super hU impl Φ ω hcoin hhash _) fun _ => superProg_pure impl Φ _

end World

end SigGolfCandidate.T3.Security.CaseC
