import SigGolfCandidate.ClaudeWCT.W9.New.G6.PairFinal
import SigGolfCandidate.T3.Secc.PairGuessLazyDefs
import SigGolfCandidate.ClaudeWCT.GuessV2.NearScore

namespace ClaudeWCT.W9.T3.Security.WPair
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Correctness (Answers)
open ClaudeWCT.W9.T3.Security.CanonGraph (WctAddr WctPoint)
open ClaudeWCT.W9.T3M.Final (AdversaryP)
open SigGolfCandidate.T3.Security.BPair (AuxL AuxSpecL LazyMem digestInputs rowVal rowStep nonceStep)
open SphincsSecurity.Concrete
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
abbrev WSpecL := SecretGuessObservation.World AuxSpecL Guess.GCoord Digest
abbrev WStateL := SecretGuessObservation.State Guess.GCoord Digest LazyMem
def initL : WStateL := SecretGuessObservation.initialState LazyMem.empty
noncomputable def auxWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest)
    (state : WStateL) : (input : AuxSpecL.Domain) → PMF (AuxSpecL.Range input × LazyMem)
  | .coin n => (fun c => (c, state.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))
  | .birth x => rowStep state.memory x true (rowSrc x)
  | .trial x => rowStep state.memory x false (rowSrc x)
  | .nonce m => nonceStep state.memory m (nonceSrc m)
  | .expose o => pure ((), state.memory.expose o)
noncomputable def envWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem where
  auxiliary := auxWith rowSrc nonceSrc
  trial mem _ _ _ := mem
  disclosure mem _ _ := mem
noncomputable def envL : SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem :=
  envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)
noncomputable def envE (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SecretGuessObservation.Environment AuxSpecL Guess.GCoord Digest LazyMem :=
  envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))
def coinReqL (n : Nat) : OracleComp WSpecL (Fin (n + 1)) := liftM (WSpecL.query (.inl (.coin n)))
def birthReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.birth x)))
def trialReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.trial x)))
def nonceReq (m : Message) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inl (.nonce m)))
def exposeReq (o : Option HashOutput) : OracleComp WSpecL Unit := liftM (WSpecL.query (.inl (.expose o)))
noncomputable def searchL (rho : Digest) (m : Message) (counter : Nat) :
    Nat → OracleComp WSpecL (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← trialReq (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))
      if WCT9.admissible output = true then pure (some (BitVec.ofNat 32 counter, output))
      else searchL rho m (counter + 1) fuel
section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_g6LazyDefs : DecidableEq SigGolfCandidate.T3.Cache :=
  Classical.decEq _
noncomputable def hashL (ω : CanonTable.Omega U) (x : HashInput) : OracleComp WSpecL HashOutput :=
  match Guess.decodeProbe x with
  | some q => Guess.probeW (auxSpec := AuxSpecL) (CanonTable.chainTable hU ω).step (CanonTable.chainTable hU ω).top
      ((CanonTable.chainTable hU ω).miss x) q.1.1 q.1.2 q.2
  | none => if x ∈ digestInputs then birthReq x else pure (wA hU ω 0 (.inl (.inr x)))
noncomputable def signerLayersW (ω : CanonTable.Omega U) (request : Request) (output : HashOutput) :
    Option (List Pieces) :=
  evalWithAnswerFn (wA hU ω 0) (signLayers request.cache (output.toNat % 2 ^ 31) 4
    (WCT9.honestForest (wA hU ω 0) (output.toNat % 2 ^ 31)))
noncomputable def finishL (ω : CanonTable.Omega U) (request : Request) (rho : Digest) :
    Option (BitVec 32 × HashOutput) → OracleComp WSpecL (Option Signature)
  | none => pure none
  | some (_, output) =>
      match signerLayersW hU ω request output with
      | none => pure none
      | some pieces => do
          let values ← Guess.discloseAll (auxSpec := AuxSpecL) (V := Digest) (revealedCoords output)
          pure (some (assembleWith (wA hU ω (overwrite (revealedCoords output) values)) (rho, output, pieces)))
noncomputable def signL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    OracleComp WSpecL (Option Signature) :=
  if request.cache = published then do
    let rho ← nonceReq request.message
    let found ← searchL rho request.message 0 WCT9.digestAttemptLimit
    exposeReq (found.map Prod.snd)
    finishL hU ω request rho found
  else pure none
noncomputable def interactionL (ω : CanonTable.Omega U) (published : SigGolfCandidate.T3.Cache) {α : Type} :
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
noncomputable def programL (ω : CanonTable.Omega U) {β : Type} : M β → OracleComp WSpecL (β × List Wots.Entry) :=
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
noncomputable def worldGameCore (ω : CanonTable.Omega U) (adversary : AdversaryP) :
    OracleComp WSpecL (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (wA hU ω 0) SigGolfCandidate.T3.keygen
  let interaction ← interactionL hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programL hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)
noncomputable abbrev worldGameL (ω : CanonTable.Omega U) (adversary : AdversaryP) := worldGameCore hU ω adversary
end World
noncomputable def nearPayoff (q : Nat) (r : (Bool × QueryLog Requests × List Wots.Entry) × WStateL) : ENNReal :=
  if r.2.memory.births.length ≤ q ∧ r.2.memory.exposures.length ≤ 2 ^ 32 ∧
      ∃ N ∈ r.2.memory.births, WCT9.admissible N = true ∧ Guess.NearCoveredBy r.2.memory.exposures N then 1 else 0
end ClaudeWCT.W9.T3.Security.WPair
