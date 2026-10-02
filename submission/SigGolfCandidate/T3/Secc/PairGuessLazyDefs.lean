import SigGolfCandidate.T3.Secc.PairGuessLazyAvg

/-!
# B-PAIR (CC-2, 2/5): the lazy world — digest rows and nonces as auxiliary oracles

The world program `worldGameL` is `worldGame` with every digest row (adversary/verifier reads: `birth`; the signer's
search: `trial`) and every signing nonce (`nonce`) read through the auxiliary oracle, plus a ghost `expose` of the
signer's accepted digest output. Two environments answer the auxiliary oracle:

* `envE D Nn` (eager): an uncached row answers the table `D`, an uncached nonce the table `Nn`;
* `envL` (lazy): an uncached row/nonce is uniform; both cache and replay.

Both record the same ghosts in `LazyMem` (rows cache, nonce cache, fresh births, signer trial rows, exposures).
`worldGameCore ω` reads `ω` only off its digest rows and nonce halves (`PairGuessLazyFree.worldGameL_congr`).
-/

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

/-! ## Digest rows -/

set_option warn.classDefReducibility false in
/-- A fixed (irreducible) enumeration of digest keys (unifying the product instance directly exhausts the recursion
limit, as for G's `encodingKeyFintype`). -/
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

/-- Every padded digest input. Chosen classically: the kernel must never unfold it (comparing it with another
`Finset` would otherwise enumerate `Digest × Message × BitVec 32`). -/
noncomputable def digestInputs : Finset HashInput := Classical.choose digestInputs_exists

attribute [irreducible] digestInputs

/-- Membership in `digestInputs` is decided classically, so that the kernel never evaluates the enumeration. -/
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

/-- The value of a digest-row table at an input (`0` off the digest rows). -/
noncomputable def rowVal (D : digestInputs → HashOutput) (x : HashInput) : HashOutput :=
  if h : x ∈ digestInputs then D ⟨x, h⟩ else 0

/-! ## The auxiliary oracle and the memory -/

/-- Auxiliary queries of the lazy world. -/
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

/-- The lazy-sampling caches and the bank ghosts. -/
structure LazyMem where
  rows : Sampling.RCache
  nonces : Message → Option Digest
  births : List HashOutput
  trials : List HashInput
  exposures : List HashOutput

def LazyMem.empty : LazyMem := ⟨∅, fun _ => none, [], [], []⟩

abbrev WStateL := SecretGuessObservation.State FtsCoord Digest LazyMem

def initL : WStateL := SecretGuessObservation.initialState LazyMem.empty

/-- Memory after a digest-row read answered `a` (`fresh`: the row was uncached; `isBirth`: an adversary/verifier read). -/
def LazyMem.readRow (mem : LazyMem) (x : HashInput) (a : HashOutput) (isBirth : Bool) : LazyMem :=
  { mem with rows := mem.rows.cacheQuery x a,
             births := if isBirth then mem.births ++ [a] else mem.births,
             trials := if isBirth then mem.trials else mem.trials ++ [x] }

/-- Memory after a cached digest-row read (a signer trial is still recorded). -/
def LazyMem.replayRow (mem : LazyMem) (x : HashInput) (isBirth : Bool) : LazyMem :=
  if isBirth then mem else { mem with trials := mem.trials ++ [x] }

def LazyMem.drawNonce (mem : LazyMem) (m : Message) (v : Digest) : LazyMem :=
  { mem with nonces := Function.update mem.nonces m (some v) }

def LazyMem.expose (mem : LazyMem) (o : Option HashOutput) : LazyMem :=
  { mem with exposures := mem.exposures ++ o.toList }

/-- A digest-row read with an eager value source `fresh` for uncached rows of `digestInputs`. -/
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

/-- The auxiliary oracle with value sources for fresh rows and nonces. -/
noncomputable def auxWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest)
    (state : WStateL) : (input : AuxSpecL.Domain) → PMF (AuxSpecL.Range input × LazyMem)
  | .coin n => (fun c => (c, state.memory)) <$> PMF.uniformOfFintype (Fin (n + 1))
  | .birth x => rowStep state.memory x true (rowSrc x)
  | .trial x => rowStep state.memory x false (rowSrc x)
  | .nonce m => nonceStep state.memory m (nonceSrc m)
  | .expose o => pure ((), state.memory.expose o)

/-- The environment of value sources (trials and disclosures keep the memory). -/
noncomputable def envWith (rowSrc : HashInput → PMF HashOutput) (nonceSrc : Message → PMF Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem where
  auxiliary := auxWith rowSrc nonceSrc
  trial mem _ _ _ := mem
  disclosure mem _ _ := mem

/-- **The lazy environment**: fresh digest rows and nonces are uniform. -/
noncomputable def envL : SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun _ => PMF.uniformOfFintype HashOutput) (fun _ => PMF.uniformOfFintype Digest)

/-- **The eager environment** of tables `D` (digest rows) and `Nn` (nonces). -/
noncomputable def envE (D : digestInputs → HashOutput) (Nn : Message → Digest) :
    SecretGuessObservation.Environment AuxSpecL FtsCoord Digest LazyMem :=
  envWith (fun x => pure (rowVal D x)) (fun m => pure (Nn m))

/-! ## Requests -/

def coinReqL (n : Nat) : OracleComp WSpecL (Fin (n + 1)) := liftM (WSpecL.query (.inl (.coin n)))
def birthReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.birth x)))
def trialReq (x : HashInput) : OracleComp WSpecL HashOutput := liftM (WSpecL.query (.inl (.trial x)))
def nonceReq (m : Message) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inl (.nonce m)))
def exposeReq (o : Option HashOutput) : OracleComp WSpecL Unit := liftM (WSpecL.query (.inl (.expose o)))
def guessReq (p : FtsCoord × Digest) : OracleComp WSpecL Bool := liftM (WSpecL.query (.inr (.inl p)))
def discloseReq (f : FtsCoord) : OracleComp WSpecL Digest := liftM (WSpecL.query (.inr (.inr f)))

/-! ## The world program -/

/-- The signer's digest search with every row a `trial` read (`digestSearch`'s loop). -/
noncomputable def searchL (rho : Digest) (m : Message) (counter : Nat) : Nat → OracleComp WSpecL (Option (BitVec 32 × HashOutput))
  | 0 => pure none
  | fuel + 1 => do
      let output ← trialReq (pad64 (digestInput rho m (BitVec.ofNat 32 counter)))
      if admissible (selections output) = true then pure (some (BitVec.ofNat 32 counter, output))
      else searchL rho m (counter + 1) fuel

section World
variable {U : Finset HashInput} (hU : CanonGraph.canonInputs ⊆ U)
noncomputable local instance instDecidableEqCache_pairGuessLazyDefs : DecidableEq T3.Cache := Classical.decEq _

/-- A public query: probes as in `hashW`; digest rows are `birth` reads; anything else from `ω`. -/
noncomputable def hashL (ω : Omega U) (x : HashInput) : OracleComp WSpecL HashOutput :=
  match decodeProbe x with
  | some p => do
      let hit ← guessReq p
      pure (if hit then ω.labels (.ftsLeaf (toLeafPos p.1)) else finiteHashAnswer ∅ U ω.residual x)
  | none => if x ∈ digestInputs then birthReq x else pure (Omega.answers hU ω (fun _ => 0) (.inl (.inr x)))

/-- The end of a signing: if the digest search and the common layers succeed, disclose the opened secrets and
return the assembled signature (`signWith`'s shape). -/
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

/-- The signer in the lazy world: nonce, digest search, exposure, then `finishL`. -/
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

/-- The world program on `ω` (`worldGameL`, defined in `PairGuessLazyCouple`, is this). -/
noncomputable def worldGameCore (ω : Omega U) (adversary : AdversaryP) :
    OracleComp WSpecL (Bool × QueryLog Requests × List Wots.Entry) := do
  let generated := evalWithAnswerFn (Omega.answers hU ω (fun _ => 0)) keygen
  let interaction ← interactionL hU ω generated.2 (adversary generated.1 generated.2)
  let verdict ← programL hU ω (GameWith.verdict PaddedGame.checker generated.1 (interaction.1, interaction.2.1))
  pure (verdict.1, interaction.2.1, interaction.2.2 ++ verdict.2)

end World

end SigGolfCandidate.T3.Security.BPair
