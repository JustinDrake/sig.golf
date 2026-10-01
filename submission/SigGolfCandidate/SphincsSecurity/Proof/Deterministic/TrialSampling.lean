import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TrialLoop
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000

attribute [local irreducible] Concrete.signAttempt

variable {State : Type}

noncomputable def worldHandler (hash : QueryImpl HashSpec (StateT State ProbComp)) :
    QueryImpl OracleWorld (StateT State ProbComp) :=
  ((QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT State ProbComp)) + hash

theorem worldHandler_lift_prob {α : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (computation : ProbComp α) :
    simulateQ (worldHandler hash) (liftM computation : OracleComp OracleWorld α) =
      (liftM computation : StateT State ProbComp α) := by
  rw [worldHandler, QueryImpl.simulateQ_add_liftM_left, simulateQ_liftTarget, simulateQ_ofLift_eq_self]

theorem worldHandler_sampling_bind {α β : Type} (hash : QueryImpl HashSpec (StateT State ProbComp))
    (sampler : ProbComp α) (next : α → OracleComp OracleWorld β) (state : State) :
    (simulateQ (worldHandler hash) ((liftM sampler : OracleComp OracleWorld α) >>= next)).run state =
      (sampler >>= fun value => (simulateQ (worldHandler hash) (next value)).run state) := by
  rw [simulateQ_bind, worldHandler_lift_prob]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]

def trialKernel (_ : Trial) (output : HashOutput) : StateT State ProbComp HashOutput := pure output

theorem trialTableRun_eq (handler : QueryImpl OracleWorld (StateT State ProbComp)) (tape : TrialTape)
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) :
    tableRun handler trialKernel tape (trialLoop secretKey message attempts trial) =
      simulateQ handler (liftM (tableDigestLoop (fun position => tape position.2) secretKey message attempts trial :
        OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult) := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
      simp only [trialLoop, tableDigestLoop, tableRun, simulateQ_bind, simulateQ_spec_query,
        liftM_bind]
      change (pure (tape (BitVec.ofNat 32 trial)) >>= fun output =>
        simulateQ (handler + fun input => trialKernel input (tape input))
          (baseLift (liftM (Concrete.signAttempt secretKey message (truncateHash output) : OracleComp HashSpec _) :
            OracleComp OracleWorld _) : OracleComp TrialWorld _) >>= _) = _
      rw [pure_bind, simulateQ_baseLift]
      apply congrArg (fun k => simulateQ handler
        (liftM (Concrete.signAttempt secretKey message (truncateHash (tape (BitVec.ofNat 32 trial)))) :
          OracleComp OracleWorld _) >>= k)
      funext attempt
      cases attempt with
      | none => exact ih _
      | some result => rfl

theorem evalDist_randomizer :
    𝒮[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] = 𝒮[Concrete.sampleRandomness] := by
  apply Eq.trans evalDist_truncate_uniform
  simp only [Concrete.sampleRandomness_eq, evalSPMF_uniformSample]

theorem run_freshTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    (freshRun (worldHandler hash) trialKernel (trialLoop secretKey message (attempts + 1) trial)).run state = (do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.signAttempt secretKey message (truncateHash output) : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (freshRun (worldHandler hash) trialKernel (match result.1 with
        | none => trialLoop secretKey message attempts (trial + 1)
        | some (index, leaves) => pure (some (truncateHash output, index, leaves)))).run result.2) := by
  rw [trialLoop, freshRun_request_bind]
  simp only [trialKernel, pure_bind]
  simp_rw [freshRun_baseLift_bind]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem run_randomTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts : Nat) (state : State) :
    (simulateQ (worldHandler hash) (Concrete.signDigestLoop (attempts + 1) secretKey message)).run state = (do
      let randomness ← Concrete.sampleRandomness
      let result ← (simulateQ (worldHandler hash) (liftM
        (Concrete.signAttempt secretKey message randomness : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      (simulateQ (worldHandler hash) (match result.1 with
        | none => Concrete.signDigestLoop attempts secretKey message
        | some (index, leaves) => pure (some (randomness, index, leaves)))).run result.2) := by
  rw [Concrete.signDigestLoop, worldHandler_sampling_bind]
  apply bind_congr
  intro randomness
  simp only [simulateQ_bind, StateT.run_bind]
  apply bind_congr
  intro result
  cases result.1 <;> rfl

theorem evalDist_freshTrialLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    𝒮[(freshRun (worldHandler hash) trialKernel (trialLoop secretKey message attempts trial)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.signDigestLoop attempts secretKey message)).run state] := by
  induction attempts generalizing trial state with
  | zero => rfl
  | succ attempts ih =>
      rw [run_freshTrialLoop_succ, run_randomTrialLoop_succ]
      conv_rhs => rw [evalSPMF_bind, ← evalDist_randomizer, ← evalSPMF_bind, bind_map_left]
      apply evalSPMF_bind_congr'
      intro output
      apply evalSPMF_bind_congr'
      intro result
      cases result.1 with
      | none => exact ih (trial + 1) result.2
      | some indices => rfl

noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType

theorem evalDist_tableDigestLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat)
    (hbound : trial + attempts ≤ 2 ^ 32) (state : State) :
    𝒮[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableDigestLoop (fun position => tape position.2)
        secretKey message attempts trial : OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.signDigestLoop attempts secretKey message)).run state] := by
  simp_rw [← trialTableRun_eq]
  exact ((freshRequests_trialLoop secretKey message attempts trial hbound).evalDist_tableRun
    (worldHandler hash) trialKernel state).trans
      (evalDist_freshTrialLoop hash secretKey message attempts trial state)

end SphincsSecurity.Seeded


open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

attribute [local irreducible] Concrete.signAttempt


/-- A paired digest loop exposing only its full-answer requests to `FreshRequests`. -/
def pairedTrialLoop (secretKey : SphincsSecurity.SecretKey) (message : Message) :
    Nat → Nat → OracleComp TrialWorld TrialResult
  | 0, _ => pure none
  | attempts + 1, trial => do
      let output ← liftM (TrialWorld.query (.inr (BitVec.ofNat 32 trial)))
      let pair := splitSecrets output
      let first ← baseLift (liftM
        (Concrete.signAttempt secretKey message pair.1 : OracleComp HashSpec _) : OracleComp OracleWorld _)
      match first with
      | some (index, leaves) => return some (pair.1, index, leaves)
      | none =>
          let second ← baseLift (liftM
            (Concrete.signAttempt secretKey message pair.2 : OracleComp HashSpec _) : OracleComp OracleWorld _)
          match second with
          | some (index, leaves) => return some (pair.2, index, leaves)
          | none => pairedTrialLoop secretKey message attempts (trial + 1)

theorem freshRequests_pairedTrialLoop (secretKey : SphincsSecurity.SecretKey) (message : Message)
    (attempts trial : Nat) (hbound : trial + attempts ≤ 2 ^ 32) :
    FreshRequests (earlierTrials trial) (pairedTrialLoop secretKey message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      rw [pairedTrialLoop]
      have htrial : trial < 2 ^ 32 := by omega
      apply FreshRequests.request (used := earlierTrials trial) (BitVec.ofNat 32 trial)
        (by
          change ¬ (BitVec.ofNat 32 trial).toNat < trial
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htrial]
          exact Nat.lt_irrefl _)
      intro output
      dsimp only
      apply freshRequests_base_bind (base := OracleWorld) (Request := Trial) (Answer := HashOutput)
      intro first
      cases first with
      | some result => exact .pure _
      | none =>
          apply freshRequests_base_bind (base := OracleWorld) (Request := Trial) (Answer := HashOutput)
          intro second
          cases second with
          | some result => exact .pure _
          | none =>
              rw [← earlierTrials_succ trial htrial]
              exact ih (trial + 1) (by omega)

variable {State : Type}

theorem pairedTrialTableRun_eq (handler : QueryImpl OracleWorld (StateT State ProbComp)) (tape : TrialTape)
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) :
    tableRun handler trialKernel tape (pairedTrialLoop secretKey message attempts trial) =
      simulateQ handler (liftM (pairedTableDigestLoop (fun position => tape position.2)
        secretKey message attempts trial : OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult) := by
  induction attempts generalizing trial with
  | zero => rfl
  | succ attempts ih =>
      simp only [pairedTrialLoop, pairedTableDigestLoop, tableRun, simulateQ_bind,
        simulateQ_spec_query, liftM_bind]
      change (pure (tape (BitVec.ofNat 32 trial)) >>= fun output =>
        simulateQ (handler + fun input => trialKernel input (tape input))
          (baseLift (liftM (Concrete.signAttempt secretKey message (splitSecrets output).1 : OracleComp HashSpec _) :
            OracleComp OracleWorld _) : OracleComp TrialWorld _) >>= _) = _
      rw [pure_bind, simulateQ_baseLift]
      apply congrArg (fun k => simulateQ handler
        (liftM (Concrete.signAttempt secretKey message (splitSecrets (tape (BitVec.ofNat 32 trial))).1) :
          OracleComp OracleWorld _) >>= k)
      funext first
      cases first with
      | some result => rfl
      | none =>
          simp only [simulateQ_bind, simulateQ_baseLift, liftM_bind]
          apply congrArg (fun k => simulateQ handler
            (liftM (Concrete.signAttempt secretKey message (splitSecrets (tape (BitVec.ofNat 32 trial))).2) :
              OracleComp OracleWorld _) >>= k)
          funext second
          cases second with
          | some result => rfl
          | none => exact ih _

/-- The two halves of one uniform answer are two independent uniform randomizers. -/
theorem evalDist_randomizerPair :
    𝒮[splitSecrets <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[do
        let low ← Concrete.sampleRandomness
        let high ← Concrete.sampleRandomness
        pure (low, high)] := by
  change 𝒮[outputHalves <$> ($ᵗ HashOutput : ProbComp HashOutput)] = _
  rw [evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Digest × Digest)
    outputHalves outputHalves.bijective]
  simp only [Concrete.sampleRandomness_eq]
  simpa only [evalSPMF_bind, evalSPMF_uniformSample] using
    (evalDist_independent_uniform_pair (α := Digest) (β := Digest)).symm

/-- Continuations may use both halves, not just their marginal distributions. -/
theorem evalDist_splitRandomizerPair_bind {α : Type} (next : Randomness → Randomness → ProbComp α) :
    𝒮[do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      next (splitSecrets output).1 (splitSecrets output).2] =
    𝒮[do
      let low ← Concrete.sampleRandomness
      let high ← Concrete.sampleRandomness
      next low high] := by
  calc
    _ = 𝒮[(splitSecrets <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun pair => next pair.1 pair.2] := by
      rw [bind_map_left]
    _ = _ := by
      rw [evalSPMF_bind, evalDist_randomizerPair, ← evalSPMF_bind]
      simp only [bind_assoc, pure_bind]

theorem run_freshPairedTrialLoop_succ (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    (freshRun (worldHandler hash) trialKernel (pairedTrialLoop secretKey message (attempts + 1) trial)).run state = (do
      let output ← ($ᵗ HashOutput : ProbComp HashOutput)
      let first ← (simulateQ (worldHandler hash) (liftM
        (Concrete.signAttempt secretKey message (splitSecrets output).1 : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
      match first.1 with
      | some (index, leaves) => pure (some ((splitSecrets output).1, index, leaves), first.2)
      | none => do
          let second ← (simulateQ (worldHandler hash) (liftM
            (Concrete.signAttempt secretKey message (splitSecrets output).2 : OracleComp HashSpec _) : OracleComp OracleWorld _)).run first.2
          (freshRun (worldHandler hash) trialKernel (match second.1 with
            | none => pairedTrialLoop secretKey message attempts (trial + 1)
            | some (index, leaves) => pure (some ((splitSecrets output).2, index, leaves)))).run second.2) := by
  rw [pairedTrialLoop, freshRun_request_bind]
  simp only [trialKernel, pure_bind]
  simp_rw [freshRun_baseLift_bind]
  simp only [StateT.run_bind, StateT.run_liftM, bind_assoc, pure_bind]
  apply bind_congr
  intro output
  apply bind_congr
  intro first
  cases first.1 with
  | some result => rfl
  | none =>
      rw [freshRun_baseLift_bind, StateT.run_bind]
      apply bind_congr
      intro second
      cases second.1 <;> rfl

/-- Pairing preserves the joint law of the result and arbitrary hash-handler state.
No independence or admissibility hypothesis is imposed on the hash handler. -/
theorem evalDist_freshPairedTrialLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat) (state : State) :
    𝒮[(freshRun (worldHandler hash) trialKernel (pairedTrialLoop secretKey message attempts trial)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.signDigestLoop (2 * attempts) secretKey message)).run state] := by
  induction attempts generalizing trial state with
  | zero => rfl
  | succ attempts ih =>
      rw [run_freshPairedTrialLoop_succ, show 2 * (attempts + 1) = (2 * attempts + 1) + 1 by omega,
        run_randomTrialLoop_succ]
      let next (low high : Randomness) : ProbComp (TrialResult × State) := do
        let first ← (simulateQ (worldHandler hash) (liftM
          (Concrete.signAttempt secretKey message low : OracleComp HashSpec _) : OracleComp OracleWorld _)).run state
        match first.1 with
        | some (index, leaves) => pure (some (low, index, leaves), first.2)
        | none => do
            let second ← (simulateQ (worldHandler hash) (liftM
              (Concrete.signAttempt secretKey message high : OracleComp HashSpec _) : OracleComp OracleWorld _)).run first.2
            (freshRun (worldHandler hash) trialKernel (match second.1 with
              | none => pairedTrialLoop secretKey message attempts (trial + 1)
              | some (index, leaves) => pure (some (high, index, leaves)))).run second.2
      change 𝒮[do
        let output ← ($ᵗ HashOutput : ProbComp HashOutput)
        next (splitSecrets output).1 (splitSecrets output).2] = _
      rw [evalDist_splitRandomizerPair_bind next]
      dsimp only [next]
      apply evalSPMF_bind_congr'
      intro low
      rw [evalSPMF_bind_bind_swap]
      apply evalSPMF_bind_congr'
      intro first
      cases hfirst : first.1 with
      | some result =>
          simp only
          apply evalSPMF_ext
          intro target
          simp [Concrete.sampleRandomness_eq]
      | none =>
          simp only
          rw [run_randomTrialLoop_succ]
          apply evalSPMF_bind_congr'
          intro high
          apply evalSPMF_bind_congr'
          intro second
          cases second.1 with
          | none => exact ih (trial + 1) second.2
          | some result => rfl

noncomputable local instance : SampleableType TrialTape := trialTapeSampleableType

/-- Sampling a `TrialTape` and trying both halves per entry is equivalent to twice
as many consecutive iterations of `Concrete.signDigestLoop`, including final state. -/
theorem evalDist_pairedTableDigestLoop (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (attempts trial : Nat)
    (hbound : trial + attempts ≤ 2 ^ 32) (state : State) :
    𝒮[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (pairedTableDigestLoop (fun position => tape position.2)
        secretKey message attempts trial : OracleComp HashSpec TrialResult) : OracleComp OracleWorld TrialResult)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.signDigestLoop (2 * attempts) secretKey message)).run state] := by
  simp_rw [← pairedTrialTableRun_eq]
  exact ((freshRequests_pairedTrialLoop secretKey message attempts trial hbound).evalDist_tableRun
    (worldHandler hash) trialKernel state).trans
      (evalDist_freshPairedTrialLoop hash secretKey message attempts trial state)

end SphincsSecurity.Seeded
