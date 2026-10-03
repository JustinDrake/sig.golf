import SigGolfCandidate.T3.Secc.PairGuessFinal

section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld)
open SphincsSecurity.Concrete
open OracleComp.DeferredSampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Avg
attribute [local instance] instSampleableTypeSeeds_pairGuessFinal instSampleableTypeForallFtsCoordDigest_pairGuessFinal
  CanonGraph.instSampleableTypeSecrets CanonGraph.instSampleableTypeOtherHalves CanonGraph.instSampleableTypeLabels_1
noncomputable def omegaLaw (adversary : AdversaryP) : ProbComp (Omega (Wots.referenceInputs adversary)) :=
  ($ᵗ ChainGraph.Seeds : ProbComp _) >>= fun seeds =>
    ($ᵗ CanonGraph.OtherHalves : ProbComp _) >>= fun other =>
    ($ᵗ CanonGraph.Labels : ProbComp _) >>= fun labels =>
    (@uniformSample (Wots.referenceInputs adversary → HashOutput)
      (CanonGraph.instSampleableTypeForallSubtypeHashInputMemFinsetHashOutput_canonGraph_1 _) : ProbComp _) >>=
      fun residual => pure ⟨seeds, other, labels, residual⟩
noncomputable def ftsPart (adversary : AdversaryP) (ω : Omega (Wots.referenceInputs adversary)) :
    ProbComp (Answers × QueryLog Requests × List Wots.Entry) :=
  ($ᵗ (FtsCoord → Digest) : ProbComp _) >>= fun fts =>
    (fun (run : Bool × QueryLog Requests × List Wots.Entry) =>
        (Omega.answers (canon_subset adversary) ω fts, run.2.1, run.2.2)) <$>
      pairRun (Omega.answers (canon_subset adversary) ω fts) adversary
theorem pairExperiment_omega (adversary : AdversaryP) :
    𝒮[pairExperiment adversary] = 𝒮[omegaLaw adversary >>= ftsPart adversary] := by
  rw [pairExperiment_eq]
  unfold omegaLaw ftsPart
  simp only [bind_assoc, pure_bind]
theorem pairExperiment_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop) :
    Pr[E | pairExperiment adversary] = ∑' ω, Pr[= ω | omegaLaw adversary] *
      Pr[fun x => E (Omega.answers (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
        ftsRun (canon_subset adversary) ω adversary] := by
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (pairExperiment_omega adversary), probEvent_bind_eq_tsum]
  apply tsum_congr
  intro ω
  rw [← inner_fts_eq (canon_subset adversary) ω adversary E]
  rfl
theorem pairExperiment_event_le_avg (adversary : AdversaryP) (E : Answers × QueryLog Requests × List Wots.Entry → Prop)
    (bound : Omega (Wots.referenceInputs adversary) → ENNReal)
    (h : ∀ ω, Pr[fun x => E (Omega.answers (canon_subset adversary) ω x.1, x.2.2.1, x.2.2.2) |
      ftsRun (canon_subset adversary) ω adversary] ≤ bound ω) :
    Pr[E | pairExperiment adversary] ≤ ∑' ω, Pr[= ω | omegaLaw adversary] * bound ω := by
  rw [pairExperiment_avg]
  exact ENNReal.tsum_le_tsum fun ω => mul_le_mul' le_rfl (h ω)
end Avg
end SigGolfCandidate.T3.Security.BPair
end

section

namespace SigGolfCandidate.T3.Security.BPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (OracleWorld bytesLE bytesLE_length)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
set_option warn.classDefReducibility false in
noncomputable def digestKeyFintype : Fintype (Digest × Message × BitVec 32) := inferInstance
attribute [irreducible] digestKeyFintype
theorem digestInputs_exists :
    ∃ S : Finset HashInput, ∀ x, x ∈ S ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  refine ⟨(@Finset.univ _ digestKeyFintype).image fun k => pad64 (digestInput k.1 k.2.1 k.2.2), fun x => ?_⟩
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, -, rfl⟩
    exact ⟨k.1, k.2.1, k.2.2, rfl⟩
  · rintro ⟨rho, m, ctr, rfl⟩
    exact ⟨(rho, m, ctr), @Finset.mem_univ _ digestKeyFintype _, rfl⟩
noncomputable def digestInputs : Finset HashInput := Classical.choose digestInputs_exists
attribute [irreducible] digestInputs
noncomputable instance (priority := high) digestInputs_decidable (x : HashInput) : Decidable (x ∈ digestInputs) :=
  Classical.propDecidable _
theorem mem_digestInputs {x : HashInput} : x ∈ digestInputs ↔ ∃ rho m ctr, x = pad64 (digestInput rho m ctr) := by
  rw [digestInputs]
  exact Classical.choose_spec digestInputs_exists x
theorem digestInput_mem (rho : Digest) (m : Message) (ctr : BitVec 32) : pad64 (digestInput rho m ctr) ∈ digestInputs :=
  mem_digestInputs.mpr ⟨rho, m, ctr, rfl⟩
theorem digestInput_length (rho : Digest) (m : Message) (ctr : BitVec 32) : (digestInput rho m ctr).length = 64 := by
  simp [digestInput, bytesLE_length]
theorem digestInputs_subset_publicUniverse : digestInputs ⊆ SeccLaw.publicUniverse := by
  intro x hx
  obtain ⟨rho, m, ctr, rfl⟩ := mem_digestInputs.mp hx
  apply SeccLaw.mem_publicUniverse
  rw [Cost.pad64_length, digestInput_length]
  unfold SeccLaw.maxInputLength
  omega
noncomputable def rowVal (D : digestInputs → HashOutput) (x : HashInput) : HashOutput :=
  if h : x ∈ digestInputs then D ⟨x, h⟩ else 0
inductive AuxL where
  | coin (n : Nat)
  | birth (x : HashInput)
  | trial (x : HashInput)
  | nonce (m : Message)
  | expose (o : Option HashOutput)
abbrev AuxSpecL : OracleSpec AuxL
  | .coin n => Fin (n + 1)
  | .birth _ => HashOutput
  | .trial _ => HashOutput
  | .nonce _ => Digest
  | .expose _ => Unit
abbrev WSpecL := SecretGuessObservation.World AuxSpecL FtsCoord Digest
structure LazyMem where
  rows : Sampling.RCache
  nonces : Message → Option Digest
  births : List HashOutput
  trials : List HashInput
  exposures : List HashOutput
def LazyMem.empty : LazyMem := ⟨∅, fun _ => none, [], [], []⟩
abbrev WStateL := SecretGuessObservation.State FtsCoord Digest LazyMem
def initL : WStateL := SecretGuessObservation.initialState LazyMem.empty
def LazyMem.readRow (mem : LazyMem) (x : HashInput) (a : HashOutput) (isBirth : Bool) : LazyMem :=
  { mem with rows := mem.rows.cacheQuery x a,
             births := if isBirth then mem.births ++ [a] else mem.births,
             trials := if isBirth then mem.trials else mem.trials ++ [x] }
def LazyMem.replayRow (mem : LazyMem) (x : HashInput) (isBirth : Bool) : LazyMem :=
  if isBirth then mem else { mem with trials := mem.trials ++ [x] }
def LazyMem.drawNonce (mem : LazyMem) (m : Message) (v : Digest) : LazyMem :=
  { mem with nonces := Function.update mem.nonces m (some v) }
def LazyMem.expose (mem : LazyMem) (o : Option HashOutput) : LazyMem :=
  { mem with exposures := mem.exposures ++ o.toList }
noncomputable def rowStep (mem : LazyMem) (x : HashInput) (isBirth : Bool) (fresh : PMF HashOutput) :
    PMF (HashOutput × LazyMem) :=
  match mem.rows x with
  | some a => pure (a, mem.replayRow x isBirth)
  | none => if x ∈ digestInputs then (fun a => (a, mem.readRow x a isBirth)) <$> fresh
      else pure (0, mem.replayRow x isBirth)
noncomputable def nonceStep (mem : LazyMem) (m : Message) (fresh : PMF Digest) : PMF (Digest × LazyMem) :=
  match mem.nonces m with
  | some v => pure (v, mem)
  | none => (fun v => (v, mem.drawNonce m v)) <$> fresh
noncomputable def auxWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest)
    (state : WStateL) : (input : AuxSpecL.Domain) → PMF (AuxSpecL.Range input × LazyMem)
  | .coin n => (fun c => (c, state.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))
  | .birth x => rowStep state.memory x true (rowSrc x)
  | .trial x => rowStep state.memory x false (rowSrc x)
  | .nonce m => nonceStep state.memory m (nonceSrc m)
  | .expose o => pure ((), state.memory.expose o)
noncomputable def envWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem where
  auxiliary := auxWith rowSrc nonceSrc
  trial mem _ _ _ := mem
  disclosure mem _ _ := mem
noncomputable def envL : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)
noncomputable def envE (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
def coinReqL (n : Nat) : OracleComp WSpecL (Fin (n + 1)) := liftM (WSpecL.query (.inl (.coin n)))
def birthReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.birth x)))
def trialReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.trial x)))
def nonceReq (m : Message) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inl (.nonce m)))
def exposeReq (o : Option HashOutput) : OracleComp WSpecL Unit := liftM (WSpecL.query (.inl (.expose o)))
def guessReq (p : FtsCoord × Digest) : OracleComp WSpecL Bool := liftM (WSpecL.query (.inr (.inl p)))
def discloseReq (f : FtsCoord) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inr (.inr f)))
noncomputable def searchL (rho : Digest) (m : Message) (counter : Nat) : Nat → OracleComp WSpecL (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← trialReq (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))
      if digestAdmissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else searchL rho m (counter + 1) fuel
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyDefs : DecidableEq T3.Cache := Classical.decEq _
noncomputable def hashL (ω : Omega U) (x : HashInput) : OracleComp WSpecL HashOutput :=
  match decodeProbe x with
  | some p => do
      let hit ← guessReq p
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else finiteHashAnswer ∅ U ω.residual x)
  | none => if x ∈ digestInputs then birthReq x else pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))
noncomputable def finishL (ω : Omega U) (request : Request) (rho : Digest) :
    Option (BitVec 32 × HashOutput) → OracleComp WSpecL (Option Signature)
  | none => pure none
  | some (_, output) =>
      match signerLayers hU ω request output with
      | none => pure none
      | some pieces => do
          let values ← (openedPositions output).mapM discloseReq
          pure (some (Correctness.assembledSignature rho
            (openedValues (overwrite (openedPositions output) values) output,
              (signerForest hU ω output).2.1, (signerForest hU ω output).2.2) pieces))
noncomputable def signL (ω : Omega U) (published : T3.Cache) (request : Request) : OracleComp WSpecL (Option Signature) :=
  if request.cache = published then do
    let rho ← nonceReq request.message
    let found ← searchL rho request.message 0 attemptLimit
    exposeReq (found.map Prod.snd)
    finishL hU ω request rho found
  else pure none
noncomputable def interactionL (ω : Omega U) (published : T3.Cache) {α : Type} :
    OracleComp LazyPrivate.Interaction α → OracleComp WSpecL (α × QueryLog Requests × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, [], []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← coinReqL n
          next coin
      | .inl (.inr x) => do
          let answer ← hashL hU ω x
          let rest ← next answer
          pure (rest.1, rest.2.1, (x, answer) :: rest.2.2)
      | .inr request => do
          let signature ← signL hU ω published request
          let rest ← next signature
          pure (rest.1, ⟨request, signature⟩ :: rest.2.1, rest.2.2))
noncomputable def programL (ω : Omega U) {β : Type} : M β → OracleComp WSpecL (β × List Wots.Entry) :=
  OracleComp.construct (fun value => pure (value, []))
    (fun input _ next => match input with
      | .inl (.inl n) => do
          let coin ← coinReqL n
          next coin
      | .inl (.inr x) => do
          let answer ← hashL hU ω x
          let rest ← next answer
          pure (rest.1, (x, answer) :: rest.2)
      | .inr _ => next (0 : HashOutput))
noncomputable def worldGameCore (ω : Omega U) (adversary : AdversaryP) :
    OracleComp WSpecL (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen
  let interaction ← interactionL hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programL hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
end World
end SigGolfCandidate.T3.Security.BPair
end
