import SigGolfCandidate.AlternativeAlgorithms
import SigGolfCandidate.Bridge.Convenience
import SigGolfCandidate.Equiv.Honest
import SigGolfCandidate.AlternativeMachine

set_option profiler true
set_option profiler.threshold 1000

open OracleComp OracleSpec ENNReal

/-! Padded typed verification: the physical witness may contain arbitrary
padding. This explicitly extends the alternate typed verifier; security must
use this interface, whereas honest correctness uses its zero-pad equality. -/
namespace SigGolfCandidate.Base4Candidate.Ideal
open OracleComp OracleSpec

abbrev Pad := Digest × Digest
abbrev ChainPads := Layer → ChainIndex → Pad

namespace Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The payload of a chain step: the record's 16-byte value when `pad = 0`, otherwise the 48-byte
`pad ‖ value` (three digests, so still a canonical-graph payload at the same chain position). -/
def chainPayload (pad : Pad) (value : Digest) : HashInput :=
  if pad = 0 then bytesLE 16 value else bytesLE 16 pad.1 ++ bytesLE 16 pad.2 ++ bytesLE 16 value

/-- `chainWalk` with a constant pad on every step. -/
def chainWalkP (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (pad : Pad) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalkP parameter lay tree leaf chainIdx pad start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (chainPayload pad previous)
      else
        pure 0

/-- The verifier's half of a padded chain. -/
def recoverChainP (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (pad : Pad) (digit : Digit) (value : Digest) : m Digest :=
  chainWalkP parameter lay tree leaf chainIdx pad digit.val (chainLength - 1 - digit.val) value

/-- `otsLeaf` with per-chain pads. -/
def otsLeafP (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) (pads : ChainIndex → Pad) :
    m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChainP parameter lay tree leaf chainIdx (pads chainIdx) (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-- `verifyLayers` with the forgery's pads. -/
def verifyLayersP (parameter : PublicParameter) (index : Index) (signature : Signature)
    (pads : ChainPads) : Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeafP parameter lay tree leaf message part.counter part.chainValues (pads lay)
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayersP parameter index signature pads remaining root
      else
        pure none

/-- `verifyCore` with the forgery's pads: only the layer walk changes. -/
def verifyCoreP (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads) :
    m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬ Admissible digest then return false
  else
    let index := digestIndex digest
    let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath
    let some root ← verifyLayersP publicKey.parameter index signature pads numLayers ftsPublicKey
      | return false
    return decide (root = publicKey.root)

/-- **The padded verifier** `VerP(pk, m, σ, pads)`: `verify` with the forgery's chain pads. -/
def verifyP (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads) :
    m Bool :=
  if CountersInRange signature then verifyCoreP publicKey message signature pads else pure false

@[simp] theorem chainPayload_zero (value : Digest) : chainPayload 0 value = bytesLE 16 value := by
  simp [chainPayload]

theorem chainWalkP_zero (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    chainWalkP (m := m) parameter lay tree leaf chainIdx 0 start steps value =
      chainWalk parameter lay tree leaf chainIdx start steps value := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      simp only [chainWalkP, chainWalk, ih, chainPayload_zero]

theorem recoverChainP_zero (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    recoverChainP (m := m) parameter lay tree leaf chainIdx 0 digit value =
      recoverChain parameter lay tree leaf chainIdx digit value :=
  chainWalkP_zero parameter lay tree leaf chainIdx _ _ value

/-- An inactive chain: pad `0`, or digit `3` (no step is hashed). -/
theorem recoverChainP_eq_of_inactive (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (pad : Pad) (digit : Digit) (value : Digest)
    (h : pad = 0 ∨ digit.val = chainLength - 1) :
    recoverChainP (m := m) parameter lay tree leaf chainIdx pad digit value =
      recoverChain parameter lay tree leaf chainIdx digit value := by
  rcases h with h | h
  · subst h; exact recoverChainP_zero parameter lay tree leaf chainIdx digit value
  · unfold recoverChainP recoverChain
    rw [h, Nat.sub_self]
    rfl

theorem otsLeafP_zero (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    otsLeafP (m := m) parameter lay tree leaf message counter values (fun _ => 0) =
      otsLeaf parameter lay tree leaf message counter values := by
  unfold otsLeafP otsLeaf
  refine bind_congr fun result => ?_
  cases result with
  | none => rfl
  | some encoding => simp only [recoverChainP_zero]

theorem verifyLayersP_zero (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    verifyLayersP (m := m) parameter index signature (fun _ _ => 0) remaining message =
      verifyLayers parameter index signature remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      rw [verifyLayersP, verifyLayers]
      split
      · dsimp only
        rw [otsLeafP_zero]
        refine bind_congr fun result => ?_
        cases result with
        | none => rfl
        | some value => simp only [ih]
      · rfl


/-- Honest zero pads leave every oracle query and return value unchanged. -/
theorem verifyP_zero (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verifyP (m := m) publicKey message signature (fun _ _ => 0) =
      verify publicKey message signature := by
  unfold verifyP verify
  split
  · unfold verifyCoreP verifyCore
    refine bind_congr fun digest => ?_
    split
    · rfl
    · refine bind_congr fun key => ?_
      rw [verifyLayersP_zero]
  · rfl

/-- A nonzero padding value cannot be mistaken for an honest chain payload. -/
theorem chainPayload_length_of_ne {pad : Pad} (hpad : pad ≠ 0) (value : Digest) :
    (chainPayload pad value).length = 48 := by
  simp [chainPayload, hpad, bytesLE]

theorem chainPayload_ne_digestBytes {pad : Pad} (hpad : pad ≠ 0) (value other : Digest) :
    chainPayload pad value ≠ digestBytes other := by
  intro h
  have he := congrArg List.length h
  rw [chainPayload_length_of_ne hpad] at he
  have hl : (digestBytes other).length = 16 := by simp [digestBytes, bytesLE]
  rw [hl] at he
  omega

end Concrete
end SigGolfCandidate.Base4Candidate.Ideal


/-! Execution-log extraction for arbitrary padding. These definitions and
lemmas are adapted from the promoted scheme's generic support machinery. -/
namespace SigGolfCandidate.Base4Candidate.Ideal

open OracleComp OracleSpec

/-- The inputs queried on the execution path selected by an answer function. -/
def queriedInputs {alpha : Type} (f : QueryImpl HashSpec Id) (oa : OracleComp HashSpec alpha) :
    List HashInput :=
  ((simulateQ (f.withLogging) oa).run).2.map Sigma.fst

@[simp] theorem queriedInputs_pure {alpha : Type} (f : QueryImpl HashSpec Id) (x : alpha) :
    queriedInputs f (pure x) = [] := by
  rfl

@[simp] theorem queriedInputs_query_bind {alpha : Type} (f : QueryImpl HashSpec Id)
    (input : HashInput) (next : HashOutput → OracleComp HashSpec alpha) :
    queriedInputs f (liftM (HashSpec.query input) >>= next)
      = input :: queriedInputs f (next (f input)) := by
  rfl

theorem queriedInputs_bind {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta) :
    queriedInputs f (oa >>= next)
      = queriedInputs f oa ++ queriedInputs f (next (evalWithAnswerFn f oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp
  | query_bind input rest ih =>
      rw [bind_assoc, queriedInputs_query_bind, queriedInputs_query_bind, ih,
        evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input, List.cons_append]

theorem queriedInputs_mono_bind_left {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f oa) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_left _ hinput

theorem queriedInputs_mono_bind_right {alpha beta : Type} (f : QueryImpl HashSpec Id)
    (oa : OracleComp HashSpec alpha) (next : alpha → OracleComp HashSpec beta)
    {input : HashInput} (hinput : input ∈ queriedInputs f (next (evalWithAnswerFn f oa))) :
    input ∈ queriedInputs f (oa >>= next) := by
  rw [queriedInputs_bind]
  exact List.mem_append_right _ hinput

@[simp] theorem queriedInputs_tweakableHash (f : QueryImpl HashSpec Id)
    (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    queriedInputs f (Concrete.tweakableHash parameter domain payload)
      = [tweakableHashInput parameter domain payload] := by
  change queriedInputs f
    (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>=
      fun answer => pure (truncateHash answer)) = _
  rw [queriedInputs_query_bind, queriedInputs_pure]


end SigGolfCandidate.Base4Candidate.Ideal

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete
open OracleComp OracleSpec

/-- Final step of a radix-four chain. -/
def paddedLastStep : ChainStep := ⟨2, by decide⟩

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (pad : Pad)

def walkValueP (start : Nat) (value : Digest) (steps : Nat) : Digest :=
  evalWithAnswerFn f (chainWalkP parameter lay tree leaf chainIdx pad start steps value)

theorem walkValueP_succ (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    walkValueP f parameter lay tree leaf chainIdx pad start value (steps + 1)
      = truncateHash (f (tweakableHashInput parameter
          (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
          (chainPayload pad (walkValueP f parameter lay tree leaf chainIdx pad start value steps)))) := by
  simp only [walkValueP, chainWalkP, evalWithAnswerFn_bind, dif_pos hrange, eval_tweakableHash]

theorem chainWalkP_last_query_mem (start : Nat) (value : Digest) (steps : Nat)
    (hrange : start + steps < chainLength - 1) :
    tweakableHashInput parameter (.chain lay tree leaf chainIdx ⟨start + steps, hrange⟩)
        (chainPayload pad (walkValueP f parameter lay tree leaf chainIdx pad start value steps))
      ∈ queriedInputs f (chainWalkP parameter lay tree leaf chainIdx pad start (steps + 1) value) := by
  rw [chainWalkP, queriedInputs_bind]
  apply List.mem_append_right
  simp only [dif_pos hrange, queriedInputs_tweakableHash, List.mem_singleton]
  rfl

theorem lastChainStep_val : paddedLastStep.val = chainLength - 2 := rfl

theorem lastChainStep_succ : paddedLastStep.val + 1 = chainLength - 1 := by
  simp [paddedLastStep, chainLength, winternitzBits]

/-- **The padded last-step hit.** A padded walk (`pad ≠ 0`, digit below `3`) that ends on the honest
endpoint ends with a query at `lastChainStep` whose payload is not the honest one (it has 48 bytes) and
whose answer is the honest endpoint. No induction over the walk: only the last query matters. -/
theorem recoverChainP_active_hit (secret : Digest) (digit : Digit) (value : Digest)
    (hpad : pad ≠ 0) (hdigit : digit.val < chainLength - 1)
    (hend : evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx pad digit value) =
      honestChain f parameter lay tree leaf chainIdx secret (chainLength - 1)) :
    ∃ previous : Digest,
      tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
          (chainPayload pad previous)
        ∈ queriedInputs f (recoverChainP parameter lay tree leaf chainIdx pad digit value) ∧
      chainPayload pad previous ≠
        digestBytes (honestChain f parameter lay tree leaf chainIdx secret paddedLastStep.val) ∧
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
          (chainPayload pad previous)))
        = honestChain f parameter lay tree leaf chainIdx secret (paddedLastStep.val + 1) := by
  have hlen : chainLength = 4 := by simp [chainLength, winternitzBits]
  obtain ⟨n, hn⟩ : ∃ n, chainLength - 1 - digit.val = n + 1 := ⟨chainLength - 2 - digit.val, by omega⟩
  have hrange : digit.val + n < chainLength - 1 := by omega
  have hstep : (⟨digit.val + n, hrange⟩ : ChainStep) = paddedLastStep := by
    apply Fin.ext
    simp only [paddedLastStep]
    omega
  refine ⟨walkValueP f parameter lay tree leaf chainIdx pad digit.val value n, ?_,
    chainPayload_ne_digestBytes hpad _ _, ?_⟩
  · have hmem := chainWalkP_last_query_mem f parameter lay tree leaf chainIdx pad digit.val value n hrange
    rw [hstep] at hmem
    unfold recoverChainP
    rw [hn]
    exact hmem
  · have hsucc := walkValueP_succ f parameter lay tree leaf chainIdx pad digit.val value n hrange
    rw [hstep] at hsucc
    rw [← hsucc, lastChainStep_succ, ← hend]
    unfold walkValueP recoverChainP
    rw [hn]


end SigGolfCandidate.Base4Candidate.Ideal.Concrete


namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete
open OracleComp OracleSpec

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

theorem sequenceFin_component_query_mem {alpha : Type} {n : Nat}
    (computation : Fin n → OracleComp HashSpec alpha) (index : Fin n) {input : HashInput}
    (hinput : input ∈ queriedInputs f (computation index)) :
    input ∈ queriedInputs f (sequenceFin computation) := by
  induction n with
  | zero => exact index.elim0
  | succ n ih =>
      cases index using Fin.cases with
      | zero =>
          rw [sequenceFin]
          exact queriedInputs_mono_bind_left f (computation 0) _ hinput
      | succ index =>
          rw [sequenceFin]
          apply queriedInputs_mono_bind_right f (computation 0)
          apply queriedInputs_mono_bind_left
          exact ih (fun index : Fin n => computation index.succ) index hinput

theorem leafHash_query_mem (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (endpoints : ChainIndex → Digest) :
    tweakableHashInput parameter (.leaf lay tree leafIdx) (leafPayload endpoints)
      ∈ queriedInputs f (leafHash parameter lay tree leafIdx endpoints) := by
  simp [leafHash]


variable (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)

def PadsInactive (pads : ChainIndex → Pad) (codeword : Encoding) : Prop :=
  ∀ chainIdx, pads chainIdx = 0 ∨ (codeword chainIdx).val = chainLength - 1

theorem exists_active_of_not_inactive {pads : ChainIndex → Pad} {codeword : Encoding}
    (h : ¬PadsInactive pads codeword) :
    ∃ chainIdx, pads chainIdx ≠ 0 ∧ (codeword chainIdx).val < chainLength - 1 := by
  obtain ⟨chainIdx, hc⟩ := not_forall.mp h
  rw [not_or] at hc
  have := (codeword chainIdx).isLt
  exact ⟨chainIdx, hc.1, by omega⟩

/-- With inactive pads the padded one-time leaf *is* the record's, query for query and value for value,
under the answer function that decoded the codeword. -/
theorem otsLeafP_run_eq_of_inactive (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (hinactive : PadsInactive pads codeword) :
    evalWithAnswerFn f (otsLeafP parameter lay tree leaf message counter values pads) =
        evalWithAnswerFn f (otsLeaf parameter lay tree leaf message counter values) ∧
      queriedInputs f (otsLeafP parameter lay tree leaf message counter values pads) =
        queriedInputs f (otsLeaf parameter lay tree leaf message counter values) := by
  have hseq : (sequenceFin fun chainIdx => recoverChainP parameter lay tree leaf chainIdx (pads chainIdx)
        (codeword chainIdx) (values chainIdx) : OracleComp HashSpec (ChainIndex → Digest)) =
      sequenceFin fun chainIdx => recoverChain parameter lay tree leaf chainIdx (codeword chainIdx)
        (values chainIdx) := by
    congr 1
    funext chainIdx
    exact recoverChainP_eq_of_inactive parameter lay tree leaf chainIdx _ _ _ (hinactive chainIdx)
  unfold otsLeafP otsLeaf
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, queriedInputs_bind, queriedInputs_bind, hencode]
  simp only [hseq]
  refine ⟨?_, ?_⟩ <;> trivial

theorem otsLeafP_leaf_query_mem (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword) :
    tweakableHashInput parameter (.leaf lay tree leaf)
        (leafPayload fun chainIdx => evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
          (pads chainIdx) (codeword chainIdx) (values chainIdx)))
      ∈ queriedInputs f (otsLeafP parameter lay tree leaf message counter values pads) := by
  simp only [otsLeafP]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_right
  apply queriedInputs_mono_bind_left
  simpa only [evalWithAnswerFn_sequenceFin] using
    leafHash_query_mem f parameter lay tree leaf
      (fun chainIdx => evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx (pads chainIdx)
        (codeword chainIdx) (values chainIdx)))

theorem otsLeafP_chain_query_mem (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (chainIdx : ChainIndex) {input : HashInput}
    (hinput : input ∈ queriedInputs f (recoverChainP parameter lay tree leaf chainIdx (pads chainIdx)
      (codeword chainIdx) (values chainIdx))) :
    input ∈ queriedInputs f (otsLeafP parameter lay tree leaf message counter values pads) := by
  simp only [otsLeafP]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_left
  exact sequenceFin_component_query_mem f _ chainIdx hinput

theorem eval_otsLeafP (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword) :
    evalWithAnswerFn f (otsLeafP parameter lay tree leaf message counter values pads) =
      some (truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
        (leafPayload fun chainIdx => evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
          (pads chainIdx) (codeword chainIdx) (values chainIdx)))))) := by
  simp only [otsLeafP, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure, leafHash, eval_tweakableHash]


/-- Every query in the current padded OTS layer is a query in the padded
hypertree verifier, independently of whether later layers accept. -/
theorem verifyLayersP_current_query_mem (index : Index) (signature : Signature)
    (pads : ChainPads) (remaining : Nat) (hlayer : remaining < numLayers)
    (message : Digest) {input : HashInput}
    (hinput : input ∈ queriedInputs f (otsLeafP parameter ⟨remaining,hlayer⟩
      (treeIndexAt index ⟨remaining,hlayer⟩) (leafIndexAt index ⟨remaining,hlayer⟩)
      message (signature.layers ⟨remaining,hlayer⟩).counter
      (signature.layers ⟨remaining,hlayer⟩).chainValues (pads ⟨remaining,hlayer⟩))) :
    input ∈ queriedInputs f (verifyLayersP parameter index signature pads (remaining+1) message) := by
  rw [verifyLayersP, dif_pos hlayer]
  exact queriedInputs_mono_bind_left f _ _ hinput

/-- A nonzero-padded chain ending at the honest endpoint gives a distinct
payload query inside the actual OTS verifier execution. -/
theorem otsLeafP_active_hit (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding)
    (chainIdx : ChainIndex) (secret : Digest)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (hpad : pads chainIdx ≠ 0) (hdigit : (codeword chainIdx).val < chainLength-1)
    (hend : evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
      (pads chainIdx) (codeword chainIdx) (values chainIdx)) =
      honestChain f parameter lay tree leaf chainIdx secret (chainLength-1)) :
    ∃ previous : Digest,
      tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
          (chainPayload (pads chainIdx) previous)
        ∈ queriedInputs f (otsLeafP parameter lay tree leaf message counter values pads) ∧
      chainPayload (pads chainIdx) previous ≠
        digestBytes (honestChain f parameter lay tree leaf chainIdx secret paddedLastStep.val) ∧
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
          (chainPayload (pads chainIdx) previous))) =
        honestChain f parameter lay tree leaf chainIdx secret (paddedLastStep.val+1) := by
  obtain ⟨previous,hquery,hpayload,hanswer⟩ := recoverChainP_active_hit f parameter lay tree leaf
    chainIdx (pads chainIdx) secret (codeword chainIdx) (values chainIdx) hpad hdigit hend
  exact ⟨previous,otsLeafP_chain_query_mem f parameter lay tree leaf message counter values pads
    codeword hencode chainIdx hquery,hpayload,hanswer⟩

end SigGolfCandidate.Base4Candidate.Ideal.Concrete


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

abbrev toB := SigGolfCandidate.Equiv.toB

/-- Serialization shared by the typed and byte-level models. -/
theorem toB_bytesLE (n : Nat) (v : BitVec (8*n)) :
    toB (Ideal.bytesLE n v) = SigGolfCandidate.Ref.toList v :=
  SigGolfCandidate.Equiv.toB_bytesLE n v

/-- The private randomizer query agrees byte for byte, including the exact
26-byte seed prefix and the pair counter. No seed-prefix security claim is
inferred from this serialization statement. -/
theorem randomizer_input (seed : Ideal.MasterSeed) (message : Ideal.Message) (trial : Nat)
    (parameter : Ideal.PublicParameter) :
    toB (Ideal.randomizerHashInput parameter seed message (BitVec.ofNat 32 trial)) =
      [byte 2,byte 7] ++ (SigGolfCandidate.Ref.toList (n := 32) seed).take 26 ++
        SigGolfCandidate.Ref.toList message ++ le32 trial := by
  simp only [Ideal.randomizerHashInput, SigGolfCandidate.Equiv.toB_append]
  rw [show toB (Ideal.bytesLE 26 (seed.extractLsb' 0 208)) =
      (SigGolfCandidate.Ref.toList (n := 32) seed).take 26 from
      SigGolfCandidate.Equiv.toB_seedPrefix seed,
    toB_bytesLE, toB_bytesLE]
  rw [← SigGolfCandidate.Equiv.leBytes_eq_toList]
  rfl

/-- Typed chain positions split into a step byte and chain byte. -/
def splitPosition (position : Nat) : Nat := position%4+256*(position/4)

theorem splitPosition_chain (chain step : Nat) (hs : step < 4) :
    splitPosition (4*chain+step) = 256*chain+step := by
  unfold splitPosition
  omega

/-- The format acts before the independently proved address-header permutation.
It covers the fixed-size typed domains; injectivity is required on the query
set used by the algorithms, not claimed here for arbitrary byte strings. -/
def chainBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 (splitPosition (leNat (slice x 4 4))) ++ slice x 8 8 ++
    zeros 32 ++ x.drop 32

def paddedChainBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 (splitPosition (leNat (slice x 4 4))) ++ slice x 8 8 ++
    slice x 32 32 ++ x.drop 64

def nodeHeight (x : List Byte) : Nat :=
  if x.getD 1 0 = byte 10 then 9 else
    if x.getD 1 0 = byte 13 then 12 else Reference.height (x.getD 2 0).toNat

def nodeBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 0 ++ slice x 8 4 ++
    le32 (2^(nodeHeight x-leNat (slice x 4 4))+leNat (slice x 12 4)) ++ x.drop 16

def format (x : List Byte) : Query :=
  if x.length = 48 ∧ x.getD 1 0 = byte 1 then pad64 (chainBlock x)
  else if x.length = 80 ∧ x.getD 1 0 = byte 1 then pad64 (paddedChainBlock x)
  else if x.length = 64 ∧ (x.getD 1 0 = byte 3 ∨ x.getD 1 0 = byte 10 ∨ x.getD 1 0 = byte 13) then pad64 (nodeBlock x)
  else if x.length = 96 ∧ x.getD 1 0 = byte 12 then
    pad64 (x.take 16 ++ slice x 32 16 ++ x.drop 64)
  else pad64 x

def queryFormat (x : Ideal.HashInput) : Query := AddressFormat.queryPerm (format (toB x))

theorem queryFormat_blocks (x : Ideal.HashInput) :
    (queryFormat x).blocks = (format (toB x)).blocks :=
  AddressFormat.queryPerm_blocks _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- Tag seven uses the ordinary padded query format; none of the specialized
chain, node or digest cases can intercept a private derivation. -/
theorem format_private (tail : List Byte) :
    format ([byte 2,byte 7] ++ tail) = pad64 ([byte 2,byte 7] ++ tail) := by
  simp [format, List.getD, byte]

theorem randomizer_query (seed : Ideal.MasterSeed) (message : Ideal.Message) (trial : Nat)
    (parameter : Ideal.PublicParameter) :
    queryFormat (Ideal.randomizerHashInput parameter seed message (BitVec.ofNat 32 trial)) =
      AddressFormat.queryPerm (pad64 ([byte 2,byte 7] ++
        (SigGolfCandidate.Ref.toList (n := 32) seed).take 26 ++
        SigGolfCandidate.Ref.toList message ++ le32 trial)) := by
  unfold queryFormat
  rw [randomizer_input]
  simp only [List.append_assoc]
  rw [format_private]

/-- The private derivation operation is identical in both models after
relabeling, for every oracle answer and every seed/message/trial. -/
theorem relabel_randomizer_hash (seed : Ideal.MasterSeed) (message : Ideal.Message) (trial : Nat)
    (parameter : Ideal.PublicParameter) :
    SigGolfCandidate.Bridge.relabel queryFormat
      (Ideal.Concrete.oracleHash
        (Ideal.randomizerHashInput parameter seed message (BitVec.ofNat 32 trial)) :
          OracleComp Ideal.HashSpec Ideal.HashOutput) =
      Reference.hash ([byte 2,byte 7] ++ (SigGolfCandidate.Ref.toList (n := 32) seed).take 26 ++
        SigGolfCandidate.Ref.toList message ++ le32 trial) := by
  unfold Ideal.Concrete.oracleHash
  simp only [HasQuery.query, SigGolfCandidate.Bridge.relabel_query]
  rw [randomizer_query]
  rfl

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge

/-- Discarding bits above197 changes none of the fields read by verification. -/
theorem truncated_extract (u : BitVec 256) (start width : Nat) (h : start+width ≤ 198) :
    (u.extractLsb' 0 198).extractLsb' start width = u.extractLsb' start width :=
  BitVec.extractLsb'_extractLsb'_of_le h

theorem typed_check_field (u : BitVec 256) :
    (Ideal.truncateMessageDigest u).extractLsb' 186 12 = Reference.checkField u := by
  change (u.extractLsb' 0 198).extractLsb' 186 12 =
    (u.extractLsb' 186 70).extractLsb' 0 12
  rw [truncated_extract u 186 12 (by decide)]
  symm
  calc
    (u.extractLsb' 186 70).extractLsb' 0 12 = u.extractLsb' (186+0) 12 :=
      BitVec.extractLsb'_extractLsb'_of_le (by decide)
    _ = u.extractLsb' 186 12 := rfl

theorem typed_admissible (u : BitVec 256) :
    Ideal.Concrete.Admissible (Ideal.truncateMessageDigest u) ↔
      Reference.digestOK u.toNat = true := by
  unfold Ideal.Concrete.Admissible
  rw [typed_check_field]
  exact (Reference.digestOK_checkField u).symm

theorem typed_instance (u : BitVec 256) :
    (Ideal.Concrete.digestIndex (Ideal.truncateMessageDigest u)).val =
      Reference.instanceIndex u.toNat := by
  change ((u.extractLsb' 0 198).extractLsb' 0 33).toFin.val = _
  rw [truncated_extract u 0 33 (by decide)]
  simp [Reference.instanceIndex, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem typed_forest_index (u : BitVec 256) (tree : Ideal.FtsTree) :
    (Ideal.Concrete.digestLeaves (Ideal.truncateMessageDigest u)
      ⟨tree.val,by have := tree.isLt; change tree.val < 18; change tree.val < 17 at this; omega⟩).val =
        Reference.forestIndex u.toNat tree.val := by
  have ht : tree.val < 17 := tree.isLt
  change ((u.extractLsb' 0 198).extractLsb' (33+9*tree.val) 9).toFin.val = _
  rw [truncated_extract u (33+9*tree.val) 9 (by omega)]
  simp [Reference.forestIndex, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

end SigGolfCandidate.Base4Candidate.ByteBridge


/-! Structural security definitions adapted from promoted FORS baseline1bfdc18: Position. -/
section AlternateStructuralPort0
/-!
# The positions of the honest key

Six of the eight hash domains name a structural position: a chain step, a one-time leaf, a node of a
layer's tree, a few-time leaf, a node of a few-time tree, and the hash of a forest's roots. Each has
one honest payload, built from the honest values at the positions below it, and the tweak determines
which position it is. The message digest and the encoding are the two that name none: their payload
is not a function of the key, and no honest value is defined at them.

`Position` is that index set, made finite by keeping the level and index fields inside the widths the
instance uses rather than in `Nat`. It over-approximates: a node above a short layer's root is a
position here and has no honest meaning, which costs nothing since every statement about positions is
either an inclusion or a count. What matters is that `parentOf` and `children` agree, since the
accounting charges a position's settling to its parent, and that no position has two parents.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal

open OracleComp

/-- A structural position of the honest key. A `node` at `level` is the node of actual level
`level + 1`, the leaves being the `leaf` positions; likewise for `ftsNode`. -/
inductive Position where
  | chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (chainIdx : ChainIndex)
      (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight) (nodeIdx : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight) (nodeIdx : FtsLeaf)
  | ftsRoots (index : Index)
  deriving DecidableEq, Fintype

namespace Position

/-- The hash domain a position is hashed at. -/
def domain : Position → HashDomain
  | .chain lay tree leafIdx chainIdx step => HashDomain.chain lay tree leafIdx chainIdx step
  | .leaf lay tree leafIdx => HashDomain.leaf lay tree leafIdx
  | .node lay tree level nodeIdx => HashDomain.node lay tree (level.val + 1) nodeIdx.val
  | .ftsLeaf index tree leafIdx => HashDomain.ftsLeaf index tree leafIdx
  | .ftsNode index tree level nodeIdx => HashDomain.ftsNode index tree (level.val + 1) nodeIdx.val
  | .ftsRoots index => HashDomain.ftsRoots index

theorem domain_inRange (p : Position) : p.domain.InRange := by
  cases p with
  | node lay tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [maxLayerHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | ftsNode index tree level nodeIdx =>
      have hlevel := level.isLt
      have hnode := nodeIdx.isLt
      simp only [ftsTreeHeight] at hlevel hnode
      show level.val + 1 < 2 ^ 32 ∧ nodeIdx.val < 2 ^ 32
      exact ⟨by omega, by omega⟩
  | chain => exact (trivial : True)
  | leaf => exact (trivial : True)
  | ftsLeaf => exact (trivial : True)
  | ftsRoots => exact (trivial : True)

theorem domain_injective {p q : Position} (h : p.domain = q.domain) : p = q := by
  cases p <;> cases q <;> simp only [domain] at h <;> simp_all [Fin.ext_iff]

/-- The last chain step, the one whose answer is the chain's endpoint. -/
def lastChainStep : ChainStep := ⟨chainLength - 2, by have := OtsCode.two_le_chainLength; omega⟩

/-- The positions whose values the payload at this one is built from. -/
def children : Position → List Position
  | .chain lay tree leafIdx chainIdx step =>
      if h : 0 < step.val then [.chain lay tree leafIdx chainIdx ⟨step.val - 1, by omega⟩] else []
  | .leaf lay tree leafIdx =>
      List.ofFn fun chainIdx : ChainIndex => .chain lay tree leafIdx chainIdx lastChainStep
  | .node lay tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight then
        if hlevel : 0 < level.val then
          [.node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .node lay tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
            .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsLeaf _ _ _ => []
  | .ftsNode index tree level nodeIdx =>
      if hidx : 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight then
        if hlevel : 0 < level.val then
          [.ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val, by omega⟩,
            .ftsNode index tree ⟨level.val - 1, by omega⟩ ⟨2 * nodeIdx.val + 1, by omega⟩]
        else
          [.ftsLeaf index tree ⟨2 * nodeIdx.val, by omega⟩,
            .ftsLeaf index tree ⟨2 * nodeIdx.val + 1, by omega⟩]
      else []
  | .ftsRoots index =>
      List.ofFn fun tree : FtsTree =>
        .ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩ ⟨0, by positivity⟩

/-- The widest payload of the instance is a one-time leaf's `v` chain endpoints. -/
theorem children_length_le (p : Position) : p.children.length ≤ numChains := by
  have htwo := OtsCode.two_le_numChains
  have hroots := OtsCode.ftsRoots_le_numChains
  cases p <;> simp only [children] <;> (try split_ifs) <;>
    simp only [List.length_ofFn, List.length_cons, List.length_nil] <;> omega

/-! ### Children and parent agree

No position has two parents, which is what keeps the accounting's charge on a position's settling
from being paid twice, and every child of a position is charged there. -/

/-- A measure the payload recursion descends: a position's children are strictly below it. -/
def depth : Position → Nat
  | .chain _ _ _ _ step => step.val
  | .leaf _ _ _ => chainLength
  | .node _ _ level _ => chainLength + 1 + level.val
  | .ftsLeaf _ _ _ => 0
  | .ftsNode _ _ level _ => 1 + level.val
  | .ftsRoots _ => 1 + ftsTreeHeight

theorem depth_lt_of_mem_children {c d : Position} (hmem : c ∈ d.children) :
    c.depth < d.depth := by
  cases d with
  | chain lay tree leafIdx chainIdx step =>
      rw [children] at hmem
      split at hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        simp only [depth]
        omega
      · simp at hmem
  | leaf =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨chainIdx, hmem⟩ := hmem
      subst hmem
      have := OtsCode.two_le_chainLength
      simp only [depth, lastChainStep]
      omega
  | node lay tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsLeaf => simp [children] at hmem
  | ftsNode index tree level nodeIdx =>
      rw [children] at hmem
      split at hmem
      · split at hmem <;> rcases List.mem_pair.mp hmem with h | h <;> subst h <;>
          simp only [depth] <;> omega
      · simp at hmem
  | ftsRoots =>
      simp only [children, List.mem_ofFn] at hmem
      obtain ⟨tree, hmem⟩ := hmem
      subst hmem
      simp [depth, ftsTreeHeight]

end Position

end SigGolfCandidate.Base4Candidate.Ideal
end AlternateStructuralPort0


/-! Structural security definitions adapted from promoted FORS baseline1bfdc18: Parameters. -/
section AlternateStructuralPort1

/-!
# Hypertree hash costs

The oracle calls an honest computation of the hypertree makes, as formulas in the parameters of `Scheme.lean`. They are sealed, so the accounting carries them symbolically and never evaluates them.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete

/-- A one-time public key: every chain walked to its end. -/
irreducible_def oneTimeKeyHashCost : Nat := numChains * (chainLength - 1)

/-- A node at `level` of a layer tree, the leaves being level `0`: each leaf is a one-time public key and its leaf hash. -/
irreducible_def treeNodeHashCost (level : Nat) : Nat := (oneTimeKeyHashCost + 2) * 2 ^ level - 1

/-- Key generation: the root of the top layer's tree. -/
irreducible_def keygenHashCost : Nat := treeNodeHashCost (layerHeight topLayer)

theorem treeNodeHashCost_zero : treeNodeHashCost 0 = oneTimeKeyHashCost + 1 := by
  rw [treeNodeHashCost_def, pow_zero, mul_one]
  omega

theorem treeNodeHashCost_succ (level : Nat) :
    treeNodeHashCost (level + 1) = treeNodeHashCost level + (treeNodeHashCost level + 1) := by
  simp only [treeNodeHashCost_def, pow_succ, ← mul_assoc]
  have hpos : 0 < (oneTimeKeyHashCost + 2) * 2 ^ level := by positivity
  generalize (oneTimeKeyHashCost + 2) * 2 ^ level = nodes at hpos ⊢
  omega

end SigGolfCandidate.Base4Candidate.Ideal.Concrete
end AlternateStructuralPort1


/-! Structural security definitions adapted from promoted FORS baseline1bfdc18: Honest. -/
section AlternateStructuralPort2
/-!
# The honest key at a position

One payload per position, one input, one value, all as functions of an answer function and the
sampled secrets. Nothing here is a recursion: each family reads the honest computation the statement
already defines, `honestChain`, `honestNode` and `honestFtsNode`, so the value at a position is
whatever those say. What the accounting needs of them is `honestPayload_congr`: the payload at a
position is a function of the values at its children, so two answer functions that agree on the
children agree on the input, which is what pins the honest structure to a cache.

`Valid` excludes the positions `Position` over-approximates, a node whose children would fall
outside the index width. They carry no honest meaning, and excluding them is what keeps
`honestPayload_congr` true of every position the accounting settles.
-/

namespace SigGolfCandidate.Base4Candidate.Ideal

open OracleComp

namespace Concrete

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

/-- The value the honest forest's root hash carries. -/
def honestFtsKey (index : Index) (secret : FtsTree → FtsLeaf → Digest) : Digest :=
  evalWithAnswerFn f (ftsKey parameter index secret)

theorem honestFtsKey_eq (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = truncateHash (f (tweakableHashInput parameter (.ftsRoots index)
          (ftsRootsPayload fun tree =>
            honestFtsNode f parameter index tree (secret tree) ftsTreeHeight 0))) := by
  simp only [honestFtsKey, ftsKey, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    eval_tweakableHash, honestFtsNode]

theorem honestChain_zero (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (secret : Digest) :
    honestChain f parameter lay tree leafIdx chainIdx secret 0 = secret := by
  simp [honestChain, chainWalk]

end Concrete

variable (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The payload the honest key hashes at a position. -/
noncomputable def honestPayload : Position → HashInput
  | .chain lay tree leafIdx chainIdx step =>
      Concrete.digestBytes (Concrete.honestChain f parameter lay tree leafIdx chainIdx
        (otsSecret lay tree leafIdx chainIdx) step.val)
  | .leaf lay tree leafIdx =>
      Concrete.leafPayload
        (Concrete.honestEndpoints f parameter lay tree (otsSecret lay tree) leafIdx)
  | .node lay tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val (2 * nodeIdx.val))
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsLeaf index tree leafIdx => Concrete.digestBytes (ftsSecret index tree leafIdx)
  | .ftsNode index tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val))
        (Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsRoots index =>
      Concrete.ftsRootsPayload fun tree =>
        Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) ftsTreeHeight 0

/-- The input the honest key hashes at a position. -/
noncomputable def honestInput (p : Position) : HashInput :=
  tweakableHashInput parameter p.domain (honestPayload f parameter otsSecret ftsSecret p)

/-- The value the honest key carries at a position. -/
noncomputable def honestValue (p : Position) : Digest :=
  truncateHash (f (honestInput f parameter otsSecret ftsSecret p))

/-! ### What the value at a position is

The honest computations of the statement, read off the definitions above. -/

theorem honestValue_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    honestValue f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
      = Concrete.honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (step.val + 1) := by
  rw [Concrete.honestChain_succ f parameter lay tree leafIdx chainIdx _ step.val step.isLt]
  rfl

theorem honestValue_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val := by
  rw [Concrete.honestNode_zero_eq_leafHash f parameter lay tree (otsSecret lay tree) leafIdx]
  rfl

theorem honestValue_node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.node lay tree level nodeIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestNode_succ f parameter lay tree (otsSecret lay tree) level.val nodeIdx.val]
  rfl

theorem honestValue_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsLeaf index tree leafIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) 0 leafIdx.val := by
  rw [Concrete.honestFtsNode_zero f parameter index tree (ftsSecret index tree) leafIdx]
  rfl

theorem honestValue_ftsNode (index : Index) (tree : FtsTree) (level : Fin ftsTreeHeight)
    (nodeIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsNode index tree level nodeIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestFtsNode_succ f parameter index tree (ftsSecret index tree) level.val
    nodeIdx.val]
  rfl

theorem honestValue_ftsRoots (index : Index) :
    honestValue f parameter otsSecret ftsSecret (.ftsRoots index)
      = Concrete.honestFtsKey f parameter index (ftsSecret index) := by
  rw [Concrete.honestFtsKey_eq f parameter index (ftsSecret index)]
  rfl

/-! ### The payload is a concatenation of the values below

Every payload of the instance is the same shape: the values at the position's children, written as
`16` bytes each, one after another, or the secret the family starts from. Reading it that way once is
what makes the accounting generic: the payload is a function of the children's values, and it
determines each of them.
-/

/-- The positions `Position` over-approximates: a node whose children would fall outside the index
width. Nothing honest lives there, and the accounting never settles one. -/
def Position.Valid : Position → Prop
  | .node _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight
  | .ftsNode _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ ftsTreeHeight
  | _ => True

/-- The values at a position's children. -/
noncomputable def childValues (p : Position) : List Digest :=
  p.children.map (honestValue f parameter otsSecret ftsSecret)

/-- The values a position's payload concatenates: those at its children, or the secret its family
starts from. -/
noncomputable def slots : Position → List Digest
  | .chain lay tree leafIdx chainIdx step =>
      if step.val = 0 then [otsSecret lay tree leafIdx chainIdx]
      else childValues f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
  | .ftsLeaf index tree leafIdx => [ftsSecret index tree leafIdx]
  | p => childValues f parameter otsSecret ftsSecret p

/-- **The payload is the values below it.** -/
theorem honestPayload_eq_slots {p : Position} (hvalid : p.Valid) :
    honestPayload f parameter otsSecret ftsSecret p
      = (slots f parameter otsSecret ftsSecret p).flatMap Concrete.digestBytes := by
  cases p with
  | chain lay tree leafIdx chainIdx step =>
      rcases Nat.eq_zero_or_pos step.val with hstep | hstep
      · have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step) = [otsSecret lay tree leafIdx chainIdx] := by
          simp only [slots, if_pos hstep]
        rw [hslots]
        simp only [honestPayload, hstep, Concrete.honestChain_zero, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      · obtain ⟨s, hs⟩ : ∃ s, step.val = s + 1 := ⟨step.val - 1, by omega⟩
        have hslt : s < chainLength - 1 := by have := step.isLt; omega
        have hchildren : (Position.chain lay tree leafIdx chainIdx step).children
            = [.chain lay tree leafIdx chainIdx ⟨s, hslt⟩] := by
          rw [Position.children, dif_pos hstep]
          simp only [List.cons.injEq, Position.chain.injEq, Fin.mk.injEq, and_true, true_and]
          omega
        have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step)
            = [honestValue f parameter otsSecret ftsSecret
                (.chain lay tree leafIdx chainIdx ⟨s, hslt⟩)] := by
          simp only [slots, if_neg (by omega : ¬ step.val = 0), childValues, hchildren,
            List.map_cons, List.map_nil]
        rw [hslots, honestValue_chain]
        simp only [honestPayload, List.flatMap_cons, List.flatMap_nil, List.append_nil, hs]
  | leaf lay tree leafIdx =>
      have hslots : slots f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
          = List.ofFn fun chainIdx : ChainIndex => honestValue f parameter otsSecret ftsSecret
              (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
        simp only [slots, childValues, Position.children, List.map_ofFn, Function.comp_def]
      rw [hslots]
      simp only [honestPayload, Concrete.leafPayload]
      refine congrArg _ (congrArg _ (funext fun chainIdx => ?_))
      rw [honestValue_chain]
      rfl
  | node lay tree level nodeIdx =>
      simp only [Position.Valid] at hvalid
      rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
              .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_leaf, honestValue_leaf, hlevel]
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val, by omega⟩,
              .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hlevel]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_node, honestValue_node, show level.val - 1 + 1 = level.val from by omega]
  | ftsLeaf index tree leafIdx =>
      simp [slots, honestPayload]
  | ftsNode index tree level nodeIdx =>
      simp only [Position.Valid] at hvalid
      rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
      · have hchildren : (Position.ftsNode index tree level nodeIdx).children
            = [.ftsLeaf index tree ⟨2 * nodeIdx.val, by omega⟩,
              .ftsLeaf index tree ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsLeaf, honestValue_ftsLeaf, hlevel]
      · have hchildren : (Position.ftsNode index tree level nodeIdx).children
            = [.ftsNode index tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val, by omega⟩,
              .ftsNode index tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hlevel]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsNode, honestValue_ftsNode,
          show level.val - 1 + 1 = level.val from by omega]
  | ftsRoots index =>
      have hslots : slots f parameter otsSecret ftsSecret (.ftsRoots index)
          = List.ofFn fun tree : FtsTree => honestValue f parameter otsSecret ftsSecret
              (.ftsNode index tree ⟨ftsTreeHeight - 1, by decide⟩ ⟨0, by positivity⟩) := by
        simp only [slots, childValues, Position.children, List.map_ofFn, Function.comp_def]
      rw [hslots]
      simp only [honestPayload, Concrete.ftsRootsPayload]
      refine congrArg _ (congrArg _ (funext fun tree => ?_))
      rw [honestValue_ftsNode]
      rfl

end SigGolfCandidate.Base4Candidate.Ideal
end AlternateStructuralPort2


namespace SigGolfCandidate.Base4Candidate.Ideal.Concrete
open OracleComp OracleSpec

/-- The local padded-chain endpoint witness is a distinct-input hit at the
same structural position used by the global security accounting. -/
theorem otsLeafP_structural_hit (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding)
    (chainIdx : ChainIndex)
    (hencode : evalWithAnswerFn f (encode parameter lay tree leaf message counter) = some codeword)
    (hpad : pads chainIdx ≠ 0) (hdigit : (codeword chainIdx).val < chainLength-1)
    (hend : evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
      (pads chainIdx) (codeword chainIdx) (values chainIdx)) =
      honestChain f parameter lay tree leaf chainIdx (otsSecret lay tree leaf chainIdx) (chainLength-1)) :
    ∃ input : HashInput,
      input ∈ queriedInputs f (otsLeafP parameter lay tree leaf message counter values pads) ∧
      input ≠ honestInput f parameter otsSecret ftsSecret (.chain lay tree leaf chainIdx paddedLastStep) ∧
      truncateHash (f input) =
        honestValue f parameter otsSecret ftsSecret (.chain lay tree leaf chainIdx paddedLastStep) := by
  obtain ⟨previous,hquery,hpayload,hanswer⟩ := otsLeafP_active_hit f parameter lay tree leaf
    message counter values pads codeword chainIdx (otsSecret lay tree leaf chainIdx)
    hencode hpad hdigit hend
  refine ⟨tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
    (chainPayload (pads chainIdx) previous),hquery,?_,?_⟩
  · intro heq
    change tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
      (chainPayload (pads chainIdx) previous) =
      tweakableHashInput parameter (.chain lay tree leaf chainIdx paddedLastStep)
        (digestBytes (honestChain f parameter lay tree leaf chainIdx
          (otsSecret lay tree leaf chainIdx) paddedLastStep.val)) at heq
    have hd := Position.domain_inRange (.chain lay tree leaf chainIdx paddedLastStep)
    exact hpayload (tweakableHashInput_injective parameter hd hd heq).2
  · rw [honestValue_chain]
    exact hanswer

end SigGolfCandidate.Base4Candidate.Ideal.Concrete


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

/-- Splitting a radix-four position retains both quotient and remainder. -/
theorem splitPosition_injective : Function.Injective splitPosition := by
  intro p q heq
  unfold splitPosition at heq
  omega

theorem splitPosition_bound (p : Nat) (hp : p < 2^26) : splitPosition p < 2^32 := by
  unfold splitPosition
  omega

theorem splitPosition_serialized_injective (p q : Nat) (hp : p < 2^26) (hq : q < 2^26)
    (heq : le32 (splitPosition p) = le32 (splitPosition q)) : p = q := by
  have hn := congrArg leNat heq
  rw [leNat_le32,leNat_le32,Nat.mod_eq_of_lt (splitPosition_bound p hp),
    Nat.mod_eq_of_lt (splitPosition_bound q hq)] at hn
  exact splitPosition_injective hn

/-- Valid level/index pairs occupy disjoint power-of-two intervals. This
also covers level-zero cache leaves. -/
theorem heapIndex_injective (h a j b k : Nat) (ha : a ≤ h) (hb : b ≤ h)
    (hj : j < 2^(h-a)) (hk : k < 2^(h-b))
    (heq : 2^(h-a)+j = 2^(h-b)+k) : a = b ∧ j = k := by
  have hab : h-a = h-b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have he : 2^(h-a+1) ≤ 2^(h-b) := Nat.pow_le_pow_right (by omega) hlt
      rw [Nat.pow_succ] at he
      omega
    · have he : 2^(h-b+1) ≤ 2^(h-a) := Nat.pow_le_pow_right (by omega) hlt
      rw [Nat.pow_succ] at he
      omega
  refine ⟨by omega,?_⟩
  rw [hab] at heq
  omega

theorem heapIndex_bound (h level index : Nat) (hh : h ≤ 12)
    (hi : index < 2^(h-level)) : 2^(h-level)+index < 2^32 := by
  have hp : 2^(h-level) ≤ 2^12 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem heapIndex_serialized_injective (h a j b k : Nat) (hh : h ≤ 12)
    (ha : a ≤ h) (hb : b ≤ h) (hj : j < 2^(h-a)) (hk : k < 2^(h-b))
    (heq : le32 (2^(h-a)+j) = le32 (2^(h-b)+k)) : a = b ∧ j = k := by
  have hn := congrArg leNat heq
  rw [leNat_le32,leNat_le32,Nat.mod_eq_of_lt (heapIndex_bound h a j hh hj),
    Nat.mod_eq_of_lt (heapIndex_bound h b k hh hk)] at hn
  exact heapIndex_injective h a j b k ha hb hj hk hn

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

private theorem length_slice (x : List Byte) (a n : Nat) (h : a+n ≤ x.length) :
    (slice x a n).length = n := by
  simp [slice]
  omega

private theorem le32_leNat (x : List Byte) (h : x.length = 4) : le32 (leNat x) = x := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [le32, leBytes, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat,leNat_div_mod,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h2]
  rfl

private theorem decompose (x : List Byte) (a n1 n2 n3 : Nat) :
    x = x.take a ++ slice x a n1 ++ slice x (a+n1) n2 ++ slice x (a+n1+n2) n3 ++
      x.drop (a+n1+n2+n3) := by
  have ht (a n : Nat) : x.take (a+n) = x.take a ++ slice x a n := List.take_add ..
  rw [← ht,← ht,← ht,List.take_append_drop]

private theorem decompose_padded (x : List Byte) :
    x = x.take 4 ++ slice x 4 4 ++ slice x 8 8 ++ slice x 16 16 ++
      slice x 32 32 ++ x.drop 64 := by
  have h1 := decompose x 4 4 8 16
  have h2 : x.drop 32 = slice x 32 32 ++ x.drop 64 := by
    unfold slice
    rw [show (64 : Nat) = 32+32 from rfl,← List.drop_drop,List.take_append_drop]
  conv_lhs => rw [h1,h2]
  simp only [List.append_assoc]

/-- Normal chain formatting retains the input when its dropped public
parameter slot is fixed, including the original four-byte position. -/
theorem chainBlock_injective (x y : List Byte) (hx : x.length = 48) (hy : y.length = 48)
    (hpx : leNat (slice x 4 4) < 2^26) (hpy : leNat (slice y 4 4) < 2^26)
    (hP : slice x 16 16 = slice y 16 16) (h : chainBlock x = chainBlock y) : x = y := by
  unfold chainBlock at h
  obtain ⟨e1,eV⟩ := List.append_inj h (by simp [slice]; omega)
  obtain ⟨e2,_⟩ := List.append_inj e1 (by simp [slice]; omega)
  obtain ⟨e3,eC⟩ := List.append_inj e2 (by simp [slice]; omega)
  obtain ⟨eA,eB⟩ := List.append_inj e3 (by simp; omega)
  have ep := splitPosition_serialized_injective _ _ hpx hpy eB
  have e4 : slice x 4 4 = slice y 4 4 := by
    rw [← le32_leNat (slice x 4 4) (length_slice _ _ _ (by omega)),
      ← le32_leNat (slice y 4 4) (length_slice _ _ _ (by omega)),ep]
  have dx := decompose x 4 4 8 16
  have dy := decompose y 4 4 8 16
  rw [dx,dy,eA,e4,eC,hP,eV]

/-- Nonzero-padded formatting likewise retains every byte other than the
fixed public parameter slot; the pad itself is preserved in full. -/
theorem paddedChainBlock_injective (x y : List Byte) (hx : x.length = 80) (hy : y.length = 80)
    (hpx : leNat (slice x 4 4) < 2^26) (hpy : leNat (slice y 4 4) < 2^26)
    (hP : slice x 16 16 = slice y 16 16)
    (h : paddedChainBlock x = paddedChainBlock y) : x = y := by
  unfold paddedChainBlock at h
  obtain ⟨e1,eV⟩ := List.append_inj h (by simp [slice]; omega)
  obtain ⟨e2,ePad⟩ := List.append_inj e1 (by simp [slice]; omega)
  obtain ⟨e3,eC⟩ := List.append_inj e2 (by simp [slice]; omega)
  obtain ⟨eA,eB⟩ := List.append_inj e3 (by simp; omega)
  have ep := splitPosition_serialized_injective _ _ hpx hpy eB
  have e4 : slice x 4 4 = slice y 4 4 := by
    rw [← le32_leNat (slice x 4 4) (length_slice _ _ _ (by omega)),
      ← le32_leNat (slice y 4 4) (length_slice _ _ _ (by omega)),ep]
  rw [decompose_padded x,decompose_padded y,eA,e4,eC,hP,ePad,eV]

/-- Honest zero-pad and nonzero-pad blocks cannot coincide. This is the
cross-format case needed in addition to each individual injectivity lemma. -/
theorem chainBlock_ne_paddedChainBlock (x y : List Byte) (hx : x.length = 48) (hy : y.length = 80)
    (hnonzero : slice y 32 32 ≠ zeros 32) : chainBlock x ≠ paddedChainBlock y := by
  intro heq
  unfold chainBlock paddedChainBlock at heq
  obtain ⟨e1,_⟩ := List.append_inj heq (by simp [slice]; omega)
  obtain ⟨_,hpad⟩ := List.append_inj e1 (by simp [slice]; omega)
  exact hnonzero hpad.symm

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

private theorem getD_take4 (x : List Byte) (i : Nat) (hi : i < 4) :
    (x.take 4).getD i 0 = x.getD i 0 := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_take,hi]

private theorem nodeHeight_take4 (x : List Byte) : nodeHeight x = nodeHeight (x.take 4) := by
  unfold nodeHeight
  rw [getD_take4 x 1 (by decide),getD_take4 x 2 (by decide)]

private theorem nodeHeight_bound (x : List Byte) : nodeHeight x ≤ 12 := by
  unfold nodeHeight Reference.height
  split_ifs <;> decide

/-- Heap formatting preserves the node level and index on the valid node
interval, and retains every other header and payload byte. -/
theorem nodeBlock_injective (x y : List Byte) (hx : x.length = 64) (hy : y.length = 64)
    (hlx : leNat (slice x 4 4) ≤ nodeHeight x) (hly : leNat (slice y 4 4) ≤ nodeHeight y)
    (hjx : leNat (slice x 12 4) < 2^(nodeHeight x-leNat (slice x 4 4)))
    (hjy : leNat (slice y 12 4) < 2^(nodeHeight y-leNat (slice y 4 4)))
    (heq : nodeBlock x = nodeBlock y) : x = y := by
  unfold nodeBlock at heq
  obtain ⟨e1,eV⟩ := List.append_inj heq (by simp [slice]; omega)
  obtain ⟨e2,eD⟩ := List.append_inj e1 (by simp [slice]; omega)
  obtain ⟨e3,eC⟩ := List.append_inj e2 (by simp [slice]; omega)
  obtain ⟨eA,_⟩ := List.append_inj e3 (by simp; omega)
  have hH : nodeHeight x = nodeHeight y := by
    rw [nodeHeight_take4 x,nodeHeight_take4 y,eA]
  rw [hH] at eD hlx hjx
  obtain ⟨ep,ej⟩ := heapIndex_serialized_injective _ _ _ _ _ (nodeHeight_bound y)
    hlx hly hjx hjy eD
  have e4 : slice x 4 4 = slice y 4 4 := by
    rw [← le32_leNat (slice x 4 4) (length_slice _ _ _ (by omega)),
      ← le32_leNat (slice y 4 4) (length_slice _ _ _ (by omega)),ep]
  have e12 : slice x 12 4 = slice y 12 4 := by
    rw [← le32_leNat (slice x 12 4) (length_slice _ _ _ (by omega)),
      ← le32_leNat (slice y 12 4) (length_slice _ _ _ (by omega)),ej]
  have dx := decompose x 4 4 4 4
  have dy := decompose y 4 4 4 4
  rw [dx,dy,eA,e4,eC,e12,eV]

/-- Digest compression drops only the fixed public-parameter and root slots. -/
theorem digestBlock_injective (x y : List Byte) (hx : x.length = 96) (hy : y.length = 96)
    (hP : slice x 16 16 = slice y 16 16) (hRoot : slice x 48 16 = slice y 48 16)
    (heq : x.take 16 ++ slice x 32 16 ++ x.drop 64 =
      y.take 16 ++ slice y 32 16 ++ y.drop 64) : x = y := by
  obtain ⟨e1,eV⟩ := List.append_inj heq (by simp [slice]; omega)
  obtain ⟨eA,eR⟩ := List.append_inj e1 (by simp; omega)
  have dx := decompose x 16 16 16 16
  have dy := decompose y 16 16 16 16
  rw [dx,dy,eA,hP,eR,hRoot,eV]

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem bytes_pad64 (x : List Byte) : SigGolfCandidate.Ref.toList (pad64 x).2 = padTo64 x :=
  SigGolfCandidate.Ref.toList_ofList _ _ (SigGolfCandidate.Ref.length_padTo64 x)

/-- For domains with a fixed input length, zero padding is injective even when
payloads themselves end in zero bytes. -/
theorem pad64_injective_of_length (x y : List Byte) (hlen : x.length = y.length)
    (heq : pad64 x = pad64 y) : x = y := by
  have hb := congrArg (fun q : Query => SigGolfCandidate.Ref.toList q.2) heq
  rw [bytes_pad64,bytes_pad64] at hb
  have ht := congrArg (fun l : List Byte => l.take x.length) hb
  simp only [padTo64] at ht
  rw [List.take_append_of_le_length (by omega),List.take_append_of_le_length (by omega)] at ht
  simpa only [List.take_length,hlen] using ht

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

private theorem getD_append_left (x y : List Byte) (i : Nat) (hi : i < x.length) :
    (x++y).getD i 0 = x.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

private theorem prefix_of_padded (x y : List Byte) (i : Nat) (hi : i < x.length) :
    (SigGolfCandidate.Ref.toList (pad64 (x++y)).2).getD i 0 = x.getD i 0 := by
  rw [bytes_pad64]
  simp only [padTo64,List.append_assoc]
  exact getD_append_left _ _ i hi

/-- Every formatting case retains the domain tag, so different hash domains
cannot collide merely through byte rearrangement or padding. -/
theorem format_tag (x : List Byte) (hx : 4 ≤ x.length) :
    (SigGolfCandidate.Ref.toList (format x).2).getD 1 0 = x.getD 1 0 := by
  unfold format
  split_ifs with hc hp hn hd
  · simp only [chainBlock,List.append_assoc]
    rw [prefix_of_padded _ _ 1 (by simp; omega),getD_take4 x 1 (by decide)]
  · simp only [paddedChainBlock,List.append_assoc]
    rw [prefix_of_padded _ _ 1 (by simp; omega),getD_take4 x 1 (by decide)]
  · simp only [nodeBlock,List.append_assoc]
    rw [prefix_of_padded _ _ 1 (by simp; omega),getD_take4 x 1 (by decide)]
  · simp only [List.append_assoc]
    rw [prefix_of_padded _ _ 1 (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_take]
  · rw [bytes_pad64]
    exact getD_append_left x _ 1 (by omega)

theorem chainBlock_length (x : List Byte) (h : x.length = 48) : (chainBlock x).length = 64 := by
  simp [chainBlock,slice,zeros,h]

theorem paddedChainBlock_length (x : List Byte) (h : x.length = 80) :
    (paddedChainBlock x).length = 64 := by
  simp [paddedChainBlock,slice,h]

theorem nodeBlock_length (x : List Byte) (h : x.length = 64) : (nodeBlock x).length = 64 := by
  simp [nodeBlock,slice,h]

/-- Fixed unpadded input lengths, determined by the domain tag. -/
def tagLength : Nat → Nat
  | 0 => 64 | 1 => 48 | 2 => 1024 | 3 => 64 | 4 => 52 | 7 => 64 | 8 => 64
  | 9 => 48 | 10 => 64 | 11 => 304 | 12 => 96 | 13 => 64 | 14 => 131104 | _ => 0

def NodeTag (x : List Byte) : Prop :=
  x.getD 1 0 = byte 3 ∨ x.getD 1 0 = byte 10 ∨ x.getD 1 0 = byte 13

def NodeValid (x : List Byte) : Prop :=
  leNat (slice x 4 4) ≤ nodeHeight x ∧
    leNat (slice x 12 4) < 2^(nodeHeight x-leNat (slice x 4 4))

/-- The permitted ordinary query format. Only slots removed by formatting
are required to be zero; node positions are restricted to their valid intervals. -/
def NormalInput (x : List Byte) : Prop :=
  4 ≤ x.length ∧ x.length = tagLength (x.getD 1 0).toNat ∧
  (x.getD 1 0 = byte 1 → slice x 16 16 = zeros 16 ∧ leNat (slice x 4 4) < 2^26) ∧
  (NodeTag x → NodeValid x) ∧
  (x.getD 1 0 = byte 12 → slice x 16 16 = zeros 16 ∧ slice x 48 16 = zeros 16)

def PaddedInput (x : List Byte) : Prop :=
  x.length = 80 ∧ x.getD 1 0 = byte 1 ∧ slice x 16 16 = zeros 16 ∧
    leNat (slice x 4 4) < 2^26 ∧ slice x 32 32 ≠ zeros 32

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem format_normal_injective {x y : List Byte} (hx : NormalInput x) (hy : NormalInput y)
    (heq : format x = format y) : x = y := by
  obtain ⟨hx4,hxl,hxc,hxn,hxd⟩ := hx
  obtain ⟨hy4,hyl,hyc,hyn,hyd⟩ := hy
  have ht : x.getD 1 0 = y.getD 1 0 := by
    rw [← format_tag x hx4,← format_tag y hy4,heq]
  have hlen : x.length = y.length := by rw [hxl,hyl,ht]
  by_cases hc : x.getD 1 0 = byte 1
  · have hcy : y.getD 1 0 = byte 1 := ht ▸ hc
    have hx48 : x.length = 48 := by rw [hxl,hc]; rfl
    have hy48 : y.length = 48 := by omega
    have fx : format x = pad64 (chainBlock x) := by simp [format,hx48,hc]
    have fy : format y = pad64 (chainBlock y) := by simp [format,hy48,hcy]
    rw [fx,fy] at heq
    have hb := pad64_injective_of_length _ _
      (by rw [chainBlock_length x hx48,chainBlock_length y hy48]) heq
    exact chainBlock_injective x y hx48 hy48 (hxc hc).2 (hyc hcy).2
      ((hxc hc).1.trans (hyc hcy).1.symm) hb
  have hcy : y.getD 1 0 ≠ byte 1 := by rwa [← ht]
  by_cases hn : NodeTag x
  · have hny : NodeTag y := by simpa only [NodeTag,← ht] using hn
    have hx64 : x.length = 64 := by
      rcases hn with h3 | h10 | h13
      · rw [hxl,h3]; rfl
      · rw [hxl,h10]; rfl
      · rw [hxl,h13]; rfl
    have hy64 : y.length = 64 := by omega
    have fx : format x = pad64 (nodeBlock x) := by
      have hn' := hn
      unfold NodeTag at hn'
      simp [format,hx64,hn']
    have fy : format y = pad64 (nodeBlock y) := by
      have hn' := hny
      unfold NodeTag at hn'
      simp [format,hy64,hn']
    rw [fx,fy] at heq
    have hb := pad64_injective_of_length _ _
      (by rw [nodeBlock_length x hx64,nodeBlock_length y hy64]) heq
    exact nodeBlock_injective x y hx64 hy64 (hxn hn).1 (hyn hny).1 (hxn hn).2 (hyn hny).2 hb
  have hny : ¬ NodeTag y := by simpa only [NodeTag,← ht] using hn
  by_cases hd : x.getD 1 0 = byte 12
  · have hdy : y.getD 1 0 = byte 12 := ht ▸ hd
    have hx96 : x.length = 96 := by rw [hxl,hd]; rfl
    have hy96 : y.length = 96 := by omega
    have fx : format x = pad64 (x.take 16 ++ slice x 32 16 ++ x.drop 64) := by
      simp [format,hx96,hd]
    have fy : format y = pad64 (y.take 16 ++ slice y 32 16 ++ y.drop 64) := by
      simp [format,hy96,hdy]
    rw [fx,fy] at heq
    have hb := pad64_injective_of_length _ _ (by simp [slice,hx96,hy96]) heq
    exact digestBlock_injective x y hx96 hy96 ((hxd hd).1.trans (hyd hdy).1.symm)
      ((hxd hd).2.trans (hyd hdy).2.symm) hb
  have hdy : y.getD 1 0 ≠ byte 12 := by rwa [← ht]
  have fx : format x = pad64 x := by
    unfold NodeTag at hn
    simp [format,hc,hn,hd]
  have fy : format y = pad64 y := by
    unfold NodeTag at hny
    simp [format,hcy,hny,hdy]
  rw [fx,fy] at heq
  exact pad64_injective_of_length x y hlen heq

theorem format_padded_injective {x y : List Byte} (hx : PaddedInput x) (hy : PaddedInput y)
    (heq : format x = format y) : x = y := by
  obtain ⟨hxl,hxt,hxP,hxp,hxpad⟩ := hx
  obtain ⟨hyl,hyt,hyP,hyp,hypad⟩ := hy
  have fx : format x = pad64 (paddedChainBlock x) := by simp [format,hxl,hxt]
  have fy : format y = pad64 (paddedChainBlock y) := by simp [format,hyl,hyt]
  rw [fx,fy] at heq
  have hb := pad64_injective_of_length _ _
    (by rw [paddedChainBlock_length x hxl,paddedChainBlock_length y hyl]) heq
  exact paddedChainBlock_injective x y hxl hyl hxp hyp (hxP.trans hyP.symm) hb

theorem format_normal_ne_padded {x y : List Byte} (hx : NormalInput x) (hy : PaddedInput y) :
    format x ≠ format y := by
  intro heq
  obtain ⟨hxl,hxt,hyP,hyp,hypad⟩ := hy
  have ht : x.getD 1 0 = byte 1 := by
    rw [← format_tag x hx.1,heq,format_tag y (by omega),hxt]
  have hx48 : x.length = 48 := by rw [hx.2.1,ht]; rfl
  have fx : format x = pad64 (chainBlock x) := by simp [format,hx48,ht]
  have fy : format y = pad64 (paddedChainBlock y) := by simp [format,hxl,hxt]
  rw [fx,fy] at heq
  have hb := pad64_injective_of_length _ _
    (by rw [chainBlock_length x hx48,paddedChainBlock_length y hxl]) heq
  exact chainBlock_ne_paddedChainBlock x y hx48 hxl hypad hb

/-- Unified permitted-query injectivity, including adversarial chain padding. -/
theorem format_injective_on : Set.InjOn format (fun x => NormalInput x ∨ PaddedInput x) := by
  intro x hx y hy heq
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact format_normal_injective hx hy heq
  · exact False.elim (format_normal_ne_padded hx hy heq)
  · exact False.elim (format_normal_ne_padded hy hx heq.symm)
  · exact format_padded_injective hx hy heq

/-- The global address-header permutation preserves this injection. -/
theorem queryFormat_injective_on : Set.InjOn queryFormat
    (fun x => NormalInput (toB x) ∨ PaddedInput (toB x)) := by
  intro x hx y hy heq
  apply SigGolfCandidate.Equiv.toB_injective
  exact format_injective_on hx hy (AddressFormat.queryPerm_injective heq)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- The private derivation lies in the injective query set, for all seed,
message and counter values. -/
theorem normal_private (tail : List Byte) (h : tail.length = 62) :
    NormalInput ([byte 2,byte 7] ++ tail) := by
  simp [NormalInput,NodeTag,tagLength,List.getD,byte,h]

theorem normal_randomizer (seed : Ideal.MasterSeed) (message : Ideal.Message)
    (trial : BitVec 32) (parameter : Ideal.PublicParameter) :
    NormalInput (toB (Ideal.randomizerHashInput parameter seed message trial)) := by
  have ht : BitVec.ofNat 32 trial.toNat = trial := by simp
  rw [← ht,randomizer_input]
  simp only [List.append_assoc]
  apply normal_private
  simp [length_toList]

/-- Structural query membership: it quantifies over every oracle answer. -/
def Permitted (x : Ideal.HashInput) : Prop := NormalInput (toB x) ∨ PaddedInput (toB x)

abbrev AComp := OracleComp Ideal.HashSpec

def QueriesPermitted {α : Type} (oa : AComp α) : Prop :=
  SigGolfCandidate.Bridge.AllQ Permitted oa

theorem queries_pure {α : Type} (x : α) : QueriesPermitted (pure x : AComp α) :=
  SigGolfCandidate.Bridge.allQ_pure Permitted x

theorem queries_bind {α β : Type} {oa : AComp α} {ob : α → AComp β}
    (h : QueriesPermitted oa) (h' : ∀ x, QueriesPermitted (ob x)) :
    QueriesPermitted (oa >>= ob) :=
  SigGolfCandidate.Bridge.allQ_bind Permitted h h'

theorem queries_oracleHash (x : Ideal.HashInput) (h : Permitted x) :
    QueriesPermitted (Ideal.Concrete.oracleHash (m := AComp) x) :=
  (SigGolfCandidate.Bridge.allQ_query (R := Ideal.HashOutput) Permitted x).mpr h

theorem queries_randomizerPair (seed : Ideal.MasterSeed) (message : Ideal.Message)
    (trial : BitVec 32) (parameter : Ideal.PublicParameter) :
    QueriesPermitted (Ideal.Seeded.deriveRandomizerPair (m := AComp) parameter seed message trial) := by
  exact queries_bind (queries_oracleHash _ (Or.inl (normal_randomizer seed message trial parameter)))
    (fun _ => queries_pure _)

theorem queries_sequenceFin {α : Type} {n : Nat} (c : Fin n → AComp α)
    (h : ∀ i, QueriesPermitted (c i)) : QueriesPermitted (Ideal.Concrete.sequenceFin c) := by
  induction n with
  | zero => exact queries_pure _
  | succ n ih =>
    exact queries_bind (h 0) fun _ =>
      queries_bind (ih _ fun i => h i.succ) fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- The typed tweak serializes to the exact protocol-two machine header. -/
theorem toB_tweakFields (tag lay tree pos index : Nat) :
    toB (Ideal.fieldBytes (Ideal.tweakFields tag lay tree pos index)) =
      Reference.header tag lay tree pos index := by
  simp only [Ideal.fieldBytes,Ideal.tweakFields,SigGolfCandidate.Equiv.toB_append]
  rw [SigGolfCandidate.Equiv.extract_hi,SigGolfCandidate.Equiv.extract_lo]
  rw [show (BitVec.ofNat 8 tag : BitVec 8) = BitVec.ofNat (8*1) tag from rfl,
    show (BitVec.ofNat 8 lay : BitVec 8) = BitVec.ofNat (8*1) lay from rfl,
    show (BitVec.ofNat 32 pos : BitVec 32) = BitVec.ofNat (8*4) pos from rfl,
    show (BitVec.ofNat 32 index : BitVec 32) = BitVec.ofNat (8*4) index from rfl]
  simp only [toB_bytesLE,← SigGolfCandidate.Equiv.leBytes_eq_toList]
  simp [Reference.header,le32,leBytes,Ideal.protocolDomainSep,byte]

theorem header_length (tag lay tree pos index : Nat) :
    (Reference.header tag lay tree pos index).length = 16 := by
  simp [Reference.header]

theorem header_tag (tag lay tree pos index : Nat) (payload : List Byte) :
    (Reference.header tag lay tree pos index ++ payload).getD 1 0 = byte tag := by
  simp [Reference.header]

/-- Tags outside the chain, node and message-digest cases preserve all bytes. -/
theorem format_plain_header (tag lay tree pos index : Nat) (payload : List Byte)
    (h1 : byte tag ≠ byte 1) (h3 : byte tag ≠ byte 3)
    (h10 : byte tag ≠ byte 10) (h13 : byte tag ≠ byte 13) (h12 : byte tag ≠ byte 12) :
    format (Reference.header tag lay tree pos index ++ payload) =
      pad64 (Reference.header tag lay tree pos index ++ payload) := by
  simp [format,header_tag,h1,h3,h10,h13,h12]

theorem normal_plain_header (tag lay tree pos index : Nat) (payload : List Byte)
    (hlen : 16+payload.length = tagLength (byte tag).toNat)
    (h1 : byte tag ≠ byte 1) (h3 : byte tag ≠ byte 3)
    (h10 : byte tag ≠ byte 10) (h13 : byte tag ≠ byte 13) (h12 : byte tag ≠ byte 12) :
    NormalInput (Reference.header tag lay tree pos index ++ payload) := by
  simp only [NormalInput,NodeTag,header_tag,List.length_append,header_length]
  exact ⟨by omega,hlen,fun h => False.elim (h1 h),
    fun h => False.elim (h.elim h3 (fun h => h.elim h10 h13)),
    fun h => False.elim (h12 h)⟩

theorem normal_plain_tweak (tag lay tree pos index : Nat) (parameter : Ideal.PublicParameter)
    (payload : Ideal.HashInput) (hlen : 32+payload.length = tagLength (byte tag).toNat)
    (h1 : byte tag ≠ byte 1) (h3 : byte tag ≠ byte 3)
    (h10 : byte tag ≠ byte 10) (h13 : byte tag ≠ byte 13) (h12 : byte tag ≠ byte 12) :
    NormalInput (toB (Ideal.fieldBytes (Ideal.tweakFields tag lay tree pos index) ++
      Ideal.bytesLE 16 parameter ++ payload)) := by
  simp only [SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,List.append_assoc]
  apply normal_plain_header _ _ _ _ _ _ _ h1 h3 h10 h13 h12
  simpa [SigGolfCandidate.Equiv.length_toB,length_toList,Nat.add_assoc] using hlen

theorem queries_tweakableHash (parameter : Ideal.PublicParameter) (domain : Ideal.HashDomain)
    (payload : Ideal.HashInput)
    (h : NormalInput (toB (Ideal.tweakableHashInput parameter domain payload))) :
    QueriesPermitted (Ideal.Concrete.tweakableHash (m := AComp) parameter domain payload) :=
  queries_bind (queries_oracleHash _ (Or.inl h)) fun _ => queries_pure _

theorem normal_keygen_ots (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (pair : Ideal.ChainPair) :
    NormalInput (toB (Ideal.keygenHashInput parameter (.ots lay tree leaf pair) seed)) := by
  apply normal_plain_tweak 0 lay.val tree.val pair.val leaf.val parameter
  all_goals simp [tagLength,Ideal.bytesLE_length,byte]

theorem normal_keygen_fts (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (index : Ideal.Index) (tree : Ideal.FtsTree) (pair : Ideal.FtsPair) :
    NormalInput (toB (Ideal.keygenHashInput parameter (.fts index tree pair) seed)) := by
  apply normal_plain_tweak 8 tree.val index.val 0 pair.val parameter
  all_goals simp [tagLength,Ideal.bytesLE_length,byte]

theorem queries_otsSecret (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (pair : Ideal.ChainPair) :
    QueriesPermitted (Ideal.Seeded.otsSecret (m := AComp) parameter seed lay tree leaf pair) :=
  queries_bind (queries_oracleHash _ (Or.inl (normal_keygen_ots parameter seed lay tree leaf pair)))
    fun _ => queries_pure _

theorem queries_ftsSecret (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (index : Ideal.Index) (tree : Ideal.FtsTree) (pair : Ideal.FtsPair) :
    QueriesPermitted (Ideal.Seeded.ftsSecret (m := AComp) parameter seed index tree pair) :=
  queries_bind (queries_oracleHash _ (Or.inl (normal_keygen_fts parameter seed index tree pair)))
    fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- Public leaf aggregation has a fixed length independent of every endpoint. -/
theorem leafPayload_length (endpoints : Ideal.ChainIndex → Ideal.Digest) :
    (Ideal.Concrete.leafPayload endpoints).length = 992 := by
  unfold Ideal.Concrete.leafPayload
  rw [Reference.flatMap_length_constant _ _ 16]
  · simp [Ideal.numChains]
  · intro x hx
    exact Ideal.bytesLE_length 16 x

theorem ftsRootsPayload_length (roots : Ideal.FtsTree → Ideal.Digest) :
    (Ideal.Concrete.ftsRootsPayload roots).length = 272 := by
  unfold Ideal.Concrete.ftsRootsPayload
  rw [Reference.flatMap_length_constant _ _ 16]
  · simp [Ideal.ftsTrees]
  · intro x hx
    exact Ideal.bytesLE_length 16 x

theorem normal_leaf (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (endpoints : Ideal.ChainIndex → Ideal.Digest) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.leaf lay tree leaf)
      (Ideal.Concrete.leafPayload endpoints))) := by
  apply normal_plain_tweak 2 lay.val tree.val 0 leaf.val parameter
  all_goals simp [tagLength,leafPayload_length,byte]

theorem normal_encoding (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (message : Ideal.Digest) (counter : Ideal.Counter) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.encoding lay tree leaf)
      (Ideal.bytesLE 16 message ++ Ideal.bytesLE 4 counter))) := by
  apply normal_plain_tweak 4 lay.val tree.val 0 leaf.val parameter
  all_goals simp [tagLength,Ideal.bytesLE_length,byte]

theorem normal_ftsLeaf (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (tree : Ideal.FtsTree) (leaf : Ideal.FtsLeaf) (secret : Ideal.Digest) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.ftsLeaf index tree leaf)
      (Ideal.bytesLE 16 secret))) := by
  apply normal_plain_tweak 9 tree.val index.val 0 leaf.val parameter
  all_goals simp [tagLength,Ideal.bytesLE_length,byte]

theorem normal_ftsRoots (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (roots : Ideal.FtsTree → Ideal.Digest) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.ftsRoots index)
      (Ideal.Concrete.ftsRootsPayload roots))) := by
  apply normal_plain_tweak 11 0 index.val 0 0 parameter
  all_goals simp [tagLength,ftsRootsPayload_length,byte]

theorem queries_leafHash (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (endpoints : Ideal.ChainIndex → Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.leafHash (m := AComp) parameter lay tree leaf endpoints) :=
  queries_tweakableHash _ _ _ (normal_leaf parameter lay tree leaf endpoints)

theorem queries_encode (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (message : Ideal.Digest) (counter : Ideal.Counter) :
    QueriesPermitted (Ideal.Concrete.encode (m := AComp) parameter lay tree leaf message counter) :=
  queries_bind (queries_tweakableHash _ _ _ (normal_encoding parameter lay tree leaf message counter))
    fun _ => queries_pure _

theorem queries_ftsLeafHash (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (tree : Ideal.FtsTree) (leaf : Ideal.FtsLeaf) (secret : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.ftsLeafHash (m := AComp) parameter index tree leaf secret) :=
  queries_tweakableHash _ _ _ (normal_ftsLeaf parameter index tree leaf secret)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem slice_header4 (tag lay tree pos index : Nat) (rest : List Byte) :
    slice (Reference.header tag lay tree pos index ++ rest) 4 4 = le32 pos := by
  rw [SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp [header_length])]
  unfold Reference.header
  rw [SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp),
    SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp),
    SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp)]
  exact SigGolfCandidate.Equiv.slice_self _ _ (length_le32 pos)

theorem slice_header12 (tag lay tree pos index : Nat) (rest : List Byte) :
    slice (Reference.header tag lay tree pos index ++ rest) 12 4 = le32 index := by
  rw [SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp [header_length])]
  unfold Reference.header
  rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp)]
  exact SigGolfCandidate.Equiv.slice_self _ _ (length_le32 index)

/-- Ordinary chain calls use a zero parameter slot and a bounded packed position. -/
theorem normal_chain_header (lay tree pos index : Nat) (value : List Byte)
    (hv : value.length = 16) (hp : pos < 2^26) :
    NormalInput (Reference.header 1 lay tree pos index ++ (zeros 16 ++ value)) := by
  have hzero : slice (Reference.header 1 lay tree pos index ++ (zeros 16 ++ value)) 16 16 = zeros 16 := by
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [header_length])]
    simp [header_length,slice,zeros]
  have hpos : leNat (slice (Reference.header 1 lay tree pos index ++ (zeros 16 ++ value)) 4 4) < 2^26 := by
    rw [slice_header4,leNat_le32,Nat.mod_eq_of_lt (by omega)]
    exact hp
  have hn : ¬ NodeTag (Reference.header 1 lay tree pos index ++ (zeros 16 ++ value)) := by
    simp [NodeTag,header_tag,byte]
  have hd : (Reference.header 1 lay tree pos index ++ (zeros 16 ++ value)).getD 1 0 ≠ byte 12 := by
    simp [header_tag,byte]
  refine ⟨?_,?_,fun _ => ⟨hzero,hpos⟩,fun h => False.elim (hn h),fun h => False.elim (hd h)⟩
  · simp [header_length,zeros]
  · simp [header_length,header_tag,zeros,hv,tagLength,byte]

theorem normal_chain (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (step : Ideal.ChainStep) (value : Ideal.Digest) :
    NormalInput (toB (Ideal.tweakableHashInput 0 (.chain lay tree leaf chain step)
      (Ideal.bytesLE 16 value))) := by
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  apply normal_chain_header _ _ _ _ _ (length_toList value)
  have hc := chain.isLt
  have hs := step.isLt
  simp only [Ideal.numChains,Ideal.chainLength,Ideal.winternitzBits] at *
  omega

/-- Membership is preserved along every bounded chain walk, including early
out-of-range branches and arbitrary oracle answers. -/
theorem queries_chainWalk (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (start steps : Nat) (value : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.chainWalk (m := AComp) 0 lay tree leaf chain start steps value) := by
  induction steps with
  | zero => exact queries_pure _
  | succ steps ih =>
    refine queries_bind ih fun previous => ?_
    split
    · exact queries_tweakableHash _ _ _ (normal_chain lay tree leaf chain _ previous)
    · exact queries_pure _

theorem queries_recoverChain (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (digit : Ideal.Digit) (value : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.recoverChain (m := AComp) 0 lay tree leaf chain digit value) :=
  queries_chainWalk lay tree leaf chain _ _ value

theorem queries_otsLeaf (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (message : Ideal.Digest) (counter : Ideal.Counter) (values : Ideal.ChainIndex → Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.otsLeaf (m := AComp) 0 lay tree leaf message counter values) := by
  refine queries_bind (queries_encode 0 lay tree leaf message counter) fun encoding => ?_
  cases encoding with
  | none => exact queries_pure _
  | some encoding =>
    refine queries_bind (queries_sequenceFin _ fun chain =>
      queries_recoverChain lay tree leaf chain (encoding chain) (values chain)) fun endpoints => ?_
    exact queries_bind (queries_leafHash 0 lay tree leaf endpoints) fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem digest_toList_injective {x y : Ideal.Digest} (h : toList x = toList y) : x = y := by
  apply Ideal.bytesLE_injective (n := 16)
  apply SigGolfCandidate.Equiv.toB_injective
  simpa only [toB_bytesLE] using h

theorem pad_bytes_nonzero (pad : Ideal.Pad) (h : pad ≠ 0) :
    toList pad.1 ++ toList pad.2 ≠ zeros 32 := by
  intro heq
  have hz : zeros 32 = toList (0 : Ideal.Digest) ++ toList (0 : Ideal.Digest) := by
    rw [SigGolfCandidate.Equiv.toList_zero,SigGolfCandidate.Equiv.toList_zero]
    rfl
  rw [hz] at heq
  obtain ⟨h1,h2⟩ := List.append_inj heq (by simp [length_toList])
  exact h (Prod.ext (digest_toList_injective h1) (digest_toList_injective h2))

/-- Nonzero witness pads are retained as 32 bytes in the hash query. -/
theorem padded_chain_header (lay tree pos index : Nat) (pad value : List Byte)
    (hp : pos < 2^26) (hpad : pad.length = 32) (hv : value.length = 16)
    (hne : pad ≠ zeros 32) :
    PaddedInput (Reference.header 1 lay tree pos index ++ (zeros 16 ++ (pad ++ value))) := by
  have hzero : slice (Reference.header 1 lay tree pos index ++ (zeros 16 ++ (pad ++ value))) 16 16 = zeros 16 := by
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [header_length])]
    simp [header_length,slice,zeros]
  have hslot : slice (Reference.header 1 lay tree pos index ++ (zeros 16 ++ (pad ++ value))) 32 32 = pad := by
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [header_length])]
    simp only [header_length,show 32-16=16 from rfl]
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [zeros])]
    simp only [zeros,List.length_replicate,Nat.sub_self,slice,List.drop_zero]
    exact List.take_left' hpad
  refine ⟨?_,header_tag _ _ _ _ _ _,hzero,?_,?_⟩
  · simp [header_length,zeros,hpad,hv]
  · rw [slice_header4,leNat_le32,Nat.mod_eq_of_lt (by omega)]
    exact hp
  · rw [hslot]
    exact hne

theorem permitted_chainPayload (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (step : Ideal.ChainStep) (pad : Ideal.Pad) (value : Ideal.Digest) :
    Permitted (Ideal.tweakableHashInput 0 (.chain lay tree leaf chain step)
      (Ideal.Concrete.chainPayload pad value)) := by
  by_cases hz : pad = 0
  · simp only [Ideal.Concrete.chainPayload,if_pos hz]
    exact Or.inl (normal_chain lay tree leaf chain step value)
  · apply Or.inr
    simp only [Ideal.Concrete.chainPayload,if_neg hz,Ideal.tweakableHashInput,
      Ideal.tweakBytes,Ideal.hashDomainFields,SigGolfCandidate.Equiv.toB_append,
      toB_tweakFields,toB_bytesLE,SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
    have hp : Ideal.chainLength*chain.val+step.val < 2^26 := by
      have hc := chain.isLt
      have hs := step.isLt
      simp only [Ideal.numChains,Ideal.chainLength,Ideal.winternitzBits] at *
      omega
    simpa only [List.append_assoc] using
      padded_chain_header lay.val tree.val (Ideal.chainLength*chain.val+step.val) leaf.val
        (toList pad.1 ++ toList pad.2) (toList value) hp
        (by simp [length_toList]) (length_toList value) (pad_bytes_nonzero pad hz)

theorem queries_tweakableHash_permitted (parameter : Ideal.PublicParameter) (domain : Ideal.HashDomain)
    (payload : Ideal.HashInput) (h : Permitted (Ideal.tweakableHashInput parameter domain payload)) :
    QueriesPermitted (Ideal.Concrete.tweakableHash (m := AComp) parameter domain payload) :=
  queries_bind (queries_oracleHash _ h) fun _ => queries_pure _

theorem queries_chainWalkP (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (pad : Ideal.Pad) (start steps : Nat) (value : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.chainWalkP (m := AComp) 0 lay tree leaf chain pad start steps value) := by
  induction steps with
  | zero => exact queries_pure _
  | succ steps ih =>
    refine queries_bind ih fun previous => ?_
    split
    · exact queries_tweakableHash_permitted _ _ _
        (permitted_chainPayload lay tree leaf chain _ pad previous)
    · exact queries_pure _

theorem queries_recoverChainP (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (pad : Ideal.Pad) (digit : Ideal.Digit) (value : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.recoverChainP (m := AComp) 0 lay tree leaf chain pad digit value) :=
  queries_chainWalkP lay tree leaf chain pad _ _ value

theorem queries_otsLeafP (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (message : Ideal.Digest) (counter : Ideal.Counter) (values : Ideal.ChainIndex → Ideal.Digest)
    (pads : Ideal.ChainIndex → Ideal.Pad) :
    QueriesPermitted (Ideal.Concrete.otsLeafP (m := AComp) 0 lay tree leaf message counter values pads) := by
  refine queries_bind (queries_encode 0 lay tree leaf message counter) fun encoding => ?_
  cases encoding with
  | none => exact queries_pure _
  | some encoding =>
    refine queries_bind (queries_sequenceFin _ fun chain =>
      queries_recoverChainP lay tree leaf chain (pads chain) (encoding chain) (values chain)) fun endpoints => ?_
    exact queries_bind (queries_leafHash 0 lay tree leaf endpoints) fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem slice_at_append (prefixBytes suffix : List Byte) (count : Nat) :
    slice (prefixBytes ++ suffix) prefixBytes.length count = suffix.take count := by
  simp [slice]

theorem normal_digest_header (randomness message : List Byte)
    (hr : randomness.length = 16) (hm : message.length = 32) :
    NormalInput (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))) := by
  have hparameter : slice (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))) 16 16 = zeros 16 := by
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [header_length])]
    simp [header_length,slice,zeros]
  have hroot : slice (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))) 48 16 = zeros 16 := by
    have hprefix : (Reference.header 12 0 0 0 0 ++ zeros 16 ++ randomness).length = 48 := by
      simp [header_length,zeros,hr]
    have h := slice_at_append (Reference.header 12 0 0 0 0 ++ zeros 16 ++ randomness)
      (zeros 16 ++ message) 16
    rw [hprefix] at h
    simpa [List.append_assoc,zeros] using h
  have h1 : (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))).getD 1 0 ≠ byte 1 := by
    simp [header_tag,byte]
  have hn : ¬ NodeTag (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))) := by
    simp [NodeTag,header_tag,byte]
  refine ⟨?_,?_,fun h => False.elim (h1 h),fun h => False.elim (hn h),
    fun _ => ⟨hparameter,hroot⟩⟩
  · simp [header_length,zeros]
  · simp [header_length,header_tag,zeros,hr,hm,tagLength,byte]

theorem normal_messageDigest (root : Ideal.Digest) (message : Ideal.Message)
    (randomness : Ideal.Randomness) :
    NormalInput (toB (Ideal.tweakableHashInput 0 .message
      (Ideal.Concrete.messageDigestPayload root message randomness))) := by
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    Ideal.Concrete.messageDigestPayload,SigGolfCandidate.Equiv.toB_append,
    toB_tweakFields,toB_bytesLE,SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  exact normal_digest_header (toList randomness) (toList message)
    (length_toList randomness) (length_toList message)

theorem queries_messageDigest (root : Ideal.Digest) (message : Ideal.Message)
    (randomness : Ideal.Randomness) :
    QueriesPermitted (Ideal.Concrete.messageDigest (m := AComp) 0 root message randomness) :=
  queries_bind (queries_oracleHash _ (Or.inl (normal_messageDigest root message randomness)))
    fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem normal_node_header (tag lay tree level index : Nat) (rest : List Byte)
    (hr : rest.length = 48) (ht : tag = 3 ∨ tag = 10 ∨ tag = 13)
    (hn : NodeValid (Reference.header tag lay tree level index ++ rest)) :
    NormalInput (Reference.header tag lay tree level index ++ rest) := by
  have hlen : tagLength (byte tag).toNat = 64 := by
    rcases ht with rfl | rfl | rfl <;> rfl
  have h1 : byte tag ≠ byte 1 := by
    rcases ht with rfl | rfl | rfl <;> decide
  have h12 : byte tag ≠ byte 12 := by
    rcases ht with rfl | rfl | rfl <;> decide
  refine ⟨?_,?_,?_,fun _ => hn,?_⟩
  · simp [header_length]
  · simp [header_length,header_tag,hr,hlen]
  · intro h
    exact False.elim (h1 ((header_tag _ _ _ _ _ _).symm.trans h))
  · intro h
    exact False.elim (h12 ((header_tag _ _ _ _ _ _).symm.trans h))

theorem layerHeight_le12 (lay : Ideal.Layer) : Ideal.layerHeight lay ≤ 12 := by
  unfold Ideal.layerHeight Ideal.maxLayerHeight
  split <;> omega

theorem normal_node (parameter : Ideal.PublicParameter) (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (level index : Nat) (left right : Ideal.Digest)
    (hl : level ≤ Ideal.layerHeight lay) (hi : index < 2^(Ideal.layerHeight lay-level)) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.node lay tree level index)
      (Ideal.Concrete.nodePayload left right))) := by
  have hmax := layerHeight_le12 lay
  have hlevel : level < 2^32 := by omega
  have hindex : index < 2^32 := lt_of_lt_of_le hi
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hlay : lay.val % 256 = lay.val := Nat.mod_eq_of_lt (by
    have h := lay.isLt
    simp only [Ideal.numLayers] at h
    omega)
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    Ideal.Concrete.nodePayload,SigGolfCandidate.Equiv.toB_append,toB_tweakFields,
    toB_bytesLE,List.append_assoc]
  apply normal_node_header _ _ _ _ _ _ (by simp [length_toList]) (Or.inl rfl)
  simp only [NodeValid,slice_header4,slice_header12,leNat_le32,
    Nat.mod_eq_of_lt hlevel,Nat.mod_eq_of_lt hindex]
  have hh : nodeHeight (Reference.header 3 lay.val tree.val level index ++
      (toList parameter ++ (toList left ++ toList right))) = Ideal.layerHeight lay := by
    simp [nodeHeight,Reference.header,byte,hlay,Reference.height,Ideal.layerHeight,Ideal.maxLayerHeight]
  rw [hh]
  exact ⟨hl,hi⟩

theorem normal_ftsNode (parameter : Ideal.PublicParameter) (index : Ideal.Index) (tree : Ideal.FtsTree)
    (level node : Nat) (left right : Ideal.Digest)
    (hl : level ≤ Ideal.ftsTreeHeight) (hi : node < 2^(Ideal.ftsTreeHeight-level)) :
    NormalInput (toB (Ideal.tweakableHashInput parameter (.ftsNode index tree level node)
      (Ideal.Concrete.nodePayload left right))) := by
  have hlevel : level < 2^32 := by simp only [Ideal.ftsTreeHeight] at hl; omega
  have hnode : node < 2^32 := lt_of_lt_of_le hi
    (Nat.pow_le_pow_right (by decide) (by simp only [Ideal.ftsTreeHeight]; omega))
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    Ideal.Concrete.nodePayload,SigGolfCandidate.Equiv.toB_append,toB_tweakFields,
    toB_bytesLE,List.append_assoc]
  apply normal_node_header _ _ _ _ _ _ (by simp [length_toList]) (Or.inr (Or.inl rfl))
  simp only [NodeValid,slice_header4,slice_header12,leNat_le32,
    Nat.mod_eq_of_lt hlevel,Nat.mod_eq_of_lt hnode]
  have hh : nodeHeight (Reference.header 10 tree.val index.val level node ++
      (toList parameter ++ (toList left ++ toList right))) = Ideal.ftsTreeHeight := by
    simp [nodeHeight,header_tag,Ideal.ftsTreeHeight]
  rw [hh]
  exact ⟨hl,hi⟩

theorem queries_node (parameter : Ideal.PublicParameter) (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (level index : Nat) (left right : Ideal.Digest)
    (hl : level ≤ Ideal.layerHeight lay) (hi : index < 2^(Ideal.layerHeight lay-level)) :
    QueriesPermitted (Ideal.Concrete.tweakableHash (m := AComp) parameter (.node lay tree level index)
      (Ideal.Concrete.nodePayload left right)) :=
  queries_tweakableHash _ _ _ (normal_node parameter lay tree level index left right hl hi)

theorem queries_ftsNode (parameter : Ideal.PublicParameter) (index : Ideal.Index) (tree : Ideal.FtsTree)
    (level node : Nat) (left right : Ideal.Digest)
    (hl : level ≤ Ideal.ftsTreeHeight) (hi : node < 2^(Ideal.ftsTreeHeight-level)) :
    QueriesPermitted (Ideal.Concrete.tweakableHash (m := AComp) parameter (.ftsNode index tree level node)
      (Ideal.Concrete.nodePayload left right)) :=
  queries_tweakableHash _ _ _ (normal_ftsNode parameter index tree level node left right hl hi)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem div_pow_position_lt (leaf height level : Nat)
    (hleaf : leaf < 2^height) (hlevel : level ≤ height) :
    leaf/2^level < 2^(height-level) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),← pow_add,Nat.sub_add_cancel hlevel]
  exact hleaf

theorem queries_treeFold (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (path : Nat → Ideal.Digest)
    (levels : Nat) (value : Ideal.Digest) (hleaf : leaf.val < 2^Ideal.layerHeight lay)
    (hlevels : levels ≤ Ideal.layerHeight lay) :
    QueriesPermitted (Ideal.Concrete.treeFold (m := AComp) parameter lay tree leaf path levels value) := by
  induction levels with
  | zero => exact queries_pure _
  | succ levels ih =>
    refine queries_bind (ih (by omega)) fun current => ?_
    have hi := div_pow_position_lt leaf.val (Ideal.layerHeight lay) (levels+1) hleaf hlevels
    split <;> exact queries_node parameter lay tree (levels+1) _ _ _ hlevels hi

theorem queries_ftsFold (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (tree : Ideal.FtsTree) (leaf : Ideal.FtsLeaf) (path : Fin Ideal.ftsTreeHeight → Ideal.Digest)
    (levels : Nat) (value : Ideal.Digest) (hlevels : levels ≤ Ideal.ftsTreeHeight) :
    QueriesPermitted (Ideal.Concrete.ftsFold (m := AComp) parameter index tree leaf path levels value) := by
  induction levels with
  | zero => exact queries_pure _
  | succ levels ih =>
    refine queries_bind (ih (by omega)) fun current => ?_
    have hi := div_pow_position_lt leaf.val Ideal.ftsTreeHeight (levels+1) leaf.isLt hlevels
    split <;> exact queries_ftsNode parameter index tree (levels+1) _ _ _ hlevels hi

theorem queries_ftsRecover (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (leaves : Ideal.IndexGroup → Ideal.FtsLeaf) (secrets : Ideal.FtsTree → Ideal.Digest)
    (paths : Ideal.FtsTree → Fin Ideal.ftsTreeHeight → Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.ftsRecover (m := AComp) parameter index leaves secrets paths) := by
  refine queries_bind (queries_sequenceFin _ fun tree => ?_) fun roots => ?_
  · refine queries_bind (queries_ftsLeafHash parameter index tree _ _) fun value => ?_
    exact queries_ftsFold parameter index tree _ _ _ value le_rfl
  · exact queries_tweakableHash _ _ _ (normal_ftsRoots parameter index roots)

theorem queries_verifyLayersP (index : Ideal.Index) (signature : Ideal.Signature)
    (pads : Ideal.ChainPads) (remaining : Nat) (message : Ideal.Digest) :
    QueriesPermitted (Ideal.Concrete.verifyLayersP (m := AComp) 0 index signature pads remaining message) := by
  induction remaining generalizing message with
  | zero => exact queries_pure _
  | succ remaining ih =>
    unfold Ideal.Concrete.verifyLayersP
    split
    · rename_i hlayer
      refine queries_bind (queries_otsLeafP ⟨remaining,hlayer⟩ _ _ _ _ _ _) fun result => ?_
      cases result with
      | none => exact queries_pure _
      | some value =>
        refine queries_bind (queries_treeFold 0 ⟨remaining,hlayer⟩ _ _ _ _ value
          (Ideal.Concrete.leafIndexAt_lt index ⟨remaining,hlayer⟩) le_rfl) fun root => ?_
        exact ih root
    · exact queries_pure _

/-- Every query of the complete padded verifier belongs to the set on which
query formatting is injective. This includes arbitrary signatures and pads,
all oracle answers, failed counter checks and rejected encodings. -/
theorem queries_verifyP (publicKey : Ideal.PublicKey) (hp : publicKey.parameter = 0)
    (message : Ideal.Message) (signature : Ideal.Signature) (pads : Ideal.ChainPads) :
    QueriesPermitted (Ideal.Concrete.verifyP (m := AComp) publicKey message signature pads) := by
  unfold Ideal.Concrete.verifyP
  split
  · unfold Ideal.Concrete.verifyCoreP
    rw [hp]
    refine queries_bind (queries_messageDigest publicKey.root message signature.randomness) fun digest => ?_
    split
    · exact queries_pure _
    · refine queries_bind (queries_ftsRecover 0 _ _ _ _) fun root => ?_
      refine queries_bind (queries_verifyLayersP _ signature pads _ root) fun result => ?_
      cases result <;> exact queries_pure _
  · exact queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem normal_keygen_mask (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (level : Fin Ideal.maxLayerHeight) (node : Fin (2^Ideal.maxLayerHeight))
    (hi : node.val < 2^(Ideal.maxLayerHeight-level.val)) :
    NormalInput (toB (Ideal.keygenHashInput parameter (.mask level node) seed)) := by
  have hl : level.val < 12 := level.isLt
  have hlevel : level.val < 2^32 := by omega
  have hnode : node.val < 2^32 := by
    have h := node.isLt
    simp only [Ideal.maxLayerHeight] at h
    omega
  simp only [Ideal.keygenHashInput,Ideal.keygenDomainFields,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,List.append_assoc]
  apply normal_node_header _ _ _ _ _ _ (by simp [length_toList]) (Or.inr (Or.inr rfl))
  simp only [NodeValid,slice_header4,slice_header12,leNat_le32,
    Nat.mod_eq_of_lt hlevel,Nat.mod_eq_of_lt hnode]
  have hh : nodeHeight (Reference.header 13 0 0 level.val node.val ++
      (toList parameter ++ toList seed)) = Ideal.maxLayerHeight := by
    simp [nodeHeight,header_tag,Ideal.maxLayerHeight,byte]
  rw [hh]
  exact ⟨by omega,hi⟩

theorem queries_maskSecret (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (level node : Nat) (hl : level < Ideal.maxLayerHeight)
    (hi : node < 2^(Ideal.maxLayerHeight-level)) :
    QueriesPermitted (Ideal.Seeded.maskSecret (m := AComp) parameter seed level node) := by
  have hn : node < 2^Ideal.maxLayerHeight := lt_of_lt_of_le hi
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  apply queries_bind (queries_oracleHash _ (Or.inl (normal_keygen_mask parameter seed _ _ ?_)))
    (fun _ => queries_pure _)
  simpa only [Ideal.Seeded.maskDomain,Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hn] using hi

theorem regionBytes_length (region : Ideal.TopRegion) : (Ideal.regionBytes region).length = 131040 := by
  have hrow (level : Fin Ideal.maxLayerHeight) :
      ((List.ofFn (region level)).flatMap (Ideal.bytesLE 16)).length =
        2^(Ideal.maxLayerHeight-level.val)*16 := by
    rw [Reference.flatMap_length_constant _ _ 16]
    · simp
    · intro value hvalue
      exact Ideal.bytesLE_length 16 value
  unfold Ideal.regionBytes
  simp only [List.length_flatMap,Function.comp_def,hrow]
  decide

theorem normal_mac (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed) (region : Ideal.TopRegion) :
    NormalInput (toB (Ideal.macHashInput parameter seed region)) := by
  apply normal_plain_tweak 14 0 0 0 0 parameter
  all_goals simp [tagLength,Ideal.bytesLE_length,regionBytes_length,byte]

theorem queries_maskRegion (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (table : Nat → Nat → Ideal.Digest) :
    QueriesPermitted (Ideal.Seeded.maskRegion (m := AComp) parameter seed table) := by
  refine queries_bind (queries_sequenceFin _ fun depth => ?_) fun rows => queries_pure _
  refine queries_bind (queries_sequenceFin _ fun node => ?_) fun row => queries_pure _
  refine queries_bind (queries_maskSecret parameter seed _ node.val ?_ node.isLt) fun mask => queries_pure _
  have h := depth.isLt
  simp only [Ideal.maxLayerHeight] at *
  omega

theorem queries_cachedTopNode (parameter : Ideal.PublicParameter) (seed : Ideal.MasterSeed)
    (cache : Ideal.TopCache) (level node : Nat) (hl : level < Ideal.maxLayerHeight)
    (hi : node < 2^(Ideal.maxLayerHeight-level)) :
    QueriesPermitted (Ideal.Seeded.cachedTopNode (m := AComp) parameter seed cache level node) :=
  queries_bind (queries_maskSecret parameter seed level node hl hi) fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem queries_buildLevel (hashNode : Nat → Ideal.Digest → Ideal.Digest → AComp Ideal.Digest)
    (width : Nat) (below : Nat → Ideal.Digest)
    (hh : ∀ node, node < width → ∀ left right, QueriesPermitted (hashNode node left right)) :
    QueriesPermitted (Ideal.Concrete.buildLevel hashNode width below) :=
  queries_bind (queries_sequenceFin _ fun node => hh node.val node.isLt _ _) fun _ => queries_pure _

theorem queries_buildLevels (hashNode : Nat → Nat → Ideal.Digest → Ideal.Digest → AComp Ideal.Digest)
    (height : Nat) (leaves : Nat → Ideal.Digest) (levels : Nat)
    (hh : ∀ level, level ≤ height → ∀ node, node < 2^(height-level) →
      ∀ left right, QueriesPermitted (hashNode level node left right))
    (hl : levels ≤ height) : QueriesPermitted (Ideal.Concrete.buildLevels hashNode height leaves levels) := by
  induction levels with
  | zero => exact queries_pure _
  | succ levels ih =>
    refine queries_bind (ih (by omega)) fun table => ?_
    exact queries_bind (queries_buildLevel _ _ _ (hh (levels+1) hl)) fun _ => queries_pure _

theorem queries_buildChain (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (secret : AComp Ideal.Digest) (digit : Nat)
    (hs : QueriesPermitted secret) :
    QueriesPermitted (Ideal.Concrete.buildChain 0 lay tree leaf chain secret digit) := by
  refine queries_bind hs fun start => ?_
  refine queries_bind (queries_chainWalk lay tree leaf chain 0 digit start) fun value => ?_
  exact queries_bind (queries_chainWalk lay tree leaf chain digit _ value) fun _ => queries_pure _

theorem queries_buildLeafPaired (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (secret : Ideal.ChainPair → AComp (Ideal.Digest × Ideal.Digest)) (digits : Ideal.Encoding)
    (hs : ∀ pair, QueriesPermitted (secret pair)) :
    QueriesPermitted (Ideal.Concrete.buildLeafPaired 0 lay tree leaf secret digits) := by
  refine queries_bind (queries_sequenceFin _ fun pair => ?_) fun pairs => ?_
  · refine queries_bind (hs pair) fun secrets => ?_
    refine queries_bind (queries_buildChain lay tree leaf _ _ _ (queries_pure secrets.1)) fun first => ?_
    exact queries_bind (queries_buildChain lay tree leaf _ _ _ (queries_pure secrets.2)) fun _ => queries_pure _
  · exact queries_bind (queries_leafHash 0 lay tree leaf _) fun _ => queries_pure _

theorem queries_buildLayerTablePaired (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (secret : Ideal.LeafIndex → Ideal.ChainPair → AComp (Ideal.Digest × Ideal.Digest))
    (leaf : Ideal.LeafIndex) (digits : Ideal.Encoding)
    (hs : ∀ leaf pair, QueriesPermitted (secret leaf pair)) :
    QueriesPermitted (Ideal.Concrete.buildLayerTablePaired 0 lay tree secret leaf digits) := by
  refine queries_bind (queries_sequenceFin _ fun leafNat =>
    queries_buildLeafPaired lay tree _ _ _ (hs _)) fun leaves => ?_
  refine queries_bind (queries_buildLevels _ _ _ _ ?_ le_rfl) fun _ => queries_pure _
  intro level hl node hn left right
  exact queries_node 0 lay tree level node left right hl hn

/-- Key generation's hash queries stay within the injective format for every
seed and every possible oracle answer, including the complete masked cache. -/
theorem queries_keygenFromSeed (seed : Ideal.MasterSeed) :
    QueriesPermitted (Ideal.Seeded.keygenFromSeed seed) := by
  refine queries_bind (queries_buildLayerTablePaired Ideal.topLayer Ideal.Concrete.rootTree _ _ _
    (fun leaf pair => queries_otsSecret 0 seed Ideal.topLayer Ideal.Concrete.rootTree leaf pair)) fun built => ?_
  refine queries_bind (queries_maskRegion 0 seed built.2) fun region => ?_
  exact queries_bind (queries_oracleHash _ (Or.inl (normal_mac 0 seed region))) fun _ => queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem queries_encodingSearch (parameter : Ideal.PublicParameter) (lay : Ideal.Layer)
    (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex) (message : Ideal.Digest) (attempts counter : Nat) :
    QueriesPermitted (Ideal.Concrete.encodingSearch (m := AComp) parameter lay tree leaf message attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact queries_pure _
  | succ attempts ih =>
    refine queries_bind (queries_encode parameter lay tree leaf message _) fun result => ?_
    cases result with
    | none => exact ih _
    | some encoding => exact queries_pure _

theorem queries_buildLayerTreePaired (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (secret : Ideal.LeafIndex → Ideal.ChainPair → AComp (Ideal.Digest × Ideal.Digest))
    (leaf : Ideal.LeafIndex) (digits : Ideal.Encoding)
    (hs : ∀ leaf pair, QueriesPermitted (secret leaf pair)) :
    QueriesPermitted (Ideal.Concrete.buildLayerTreePaired 0 lay tree secret leaf digits) :=
  queries_bind (queries_buildLayerTablePaired lay tree secret leaf digits hs) fun _ => queries_pure _

theorem queries_buildFtsTreePaired (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (tree : Ideal.FtsTree) (secret : Ideal.FtsPair → AComp (Ideal.Digest × Ideal.Digest))
    (leaf : Ideal.FtsLeaf) (hs : ∀ pair, QueriesPermitted (secret pair)) :
    QueriesPermitted (Ideal.Concrete.buildFtsTreePaired parameter index tree secret leaf) := by
  refine queries_bind (queries_sequenceFin _ fun pair => ?_) fun pairs => ?_
  · refine queries_bind (hs pair) fun secrets => ?_
    refine queries_bind (queries_ftsLeafHash parameter index tree _ secrets.1) fun first => ?_
    exact queries_bind (queries_ftsLeafHash parameter index tree _ secrets.2) fun _ => queries_pure _
  · refine queries_bind (queries_buildLevels _ _ _ _ ?_ le_rfl) fun _ => queries_pure _
    intro level hl node hn left right
    exact queries_ftsNode parameter index tree level node left right hl hn

theorem queries_buildForestPaired (parameter : Ideal.PublicParameter) (index : Ideal.Index)
    (secret : Ideal.FtsTree → Ideal.FtsPair → AComp (Ideal.Digest × Ideal.Digest))
    (leaves : Ideal.IndexGroup → Ideal.FtsLeaf) (hs : ∀ tree pair, QueriesPermitted (secret tree pair)) :
    QueriesPermitted (Ideal.Concrete.buildForestPaired parameter index secret leaves) := by
  refine queries_bind (queries_sequenceFin _ fun tree =>
    queries_buildFtsTreePaired parameter index tree (secret tree) _ (hs tree)) fun trees => ?_
  exact queries_bind (queries_tweakableHash _ _ _ (normal_ftsRoots parameter index _)) fun _ => queries_pure _

theorem queries_signAttempt (secretKey : Ideal.Seeded.SecretKey) (hp : secretKey.parameter = 0)
    (message : Ideal.Message) (randomness : Ideal.Randomness) :
    QueriesPermitted (Ideal.Seeded.signAttempt (m := AComp) secretKey message randomness) := by
  unfold Ideal.Seeded.signAttempt
  rw [hp]
  refine queries_bind (queries_messageDigest secretKey.root message randomness) fun digest => ?_
  split <;> exact queries_pure _

theorem queries_signDigestPairs (secretKey : Ideal.Seeded.SecretKey) (hp : secretKey.parameter = 0)
    (message : Ideal.Message) (attempts trial : Nat) :
    QueriesPermitted (Ideal.Seeded.signDigestPairs (m := AComp) secretKey message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact queries_pure _
  | succ attempts ih =>
    refine queries_bind (queries_randomizerPair secretKey.seed message _ secretKey.parameter) fun pair => ?_
    refine queries_bind (queries_signAttempt secretKey hp message pair.1) fun first => ?_
    cases first with
    | some first => exact queries_pure _
    | none =>
      refine queries_bind (queries_signAttempt secretKey hp message pair.2) fun second => ?_
      cases second with
      | some second => exact queries_pure _
      | none => exact ih _

theorem queries_signTopLayerPaired (index : Ideal.Index)
    (secret : Ideal.LeafIndex → Ideal.ChainPair → AComp (Ideal.Digest × Ideal.Digest))
    (topNode : Nat → Nat → AComp Ideal.Digest) (message : Ideal.Digest)
    (hs : ∀ leaf pair, QueriesPermitted (secret leaf pair))
    (ht : ∀ level, level < Ideal.maxLayerHeight → ∀ node, node < 2^(Ideal.maxLayerHeight-level) →
      QueriesPermitted (topNode level node)) :
    QueriesPermitted (Ideal.Concrete.signTopLayerPaired 0 index secret topNode message) := by
  refine queries_bind (queries_encodingSearch 0 Ideal.topLayer _ _ message _ _) fun result => ?_
  cases result with
  | none => exact queries_pure _
  | some result =>
    refine queries_bind (queries_sequenceFin _ fun pair => ?_) fun pairs => ?_
    · refine queries_bind (hs _ pair) fun secrets => ?_
      refine queries_bind (queries_chainWalk Ideal.topLayer _ _ _ _ _ secrets.1) fun first => ?_
      exact queries_bind (queries_chainWalk Ideal.topLayer _ _ _ _ _ secrets.2) fun _ => queries_pure _
    · refine queries_bind (queries_sequenceFin _ fun level => ?_) fun _ => queries_pure _
      exact ht level.val level.isLt _ (Ideal.Concrete.xor_div_lt
        (Ideal.Concrete.leafIndexAt_lt index Ideal.topLayer) level.isLt)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem queries_signLayersPaired (index : Ideal.Index)
    (secret : Ideal.Layer → Ideal.TreeIndex → Ideal.LeafIndex → Ideal.ChainPair →
      AComp (Ideal.Digest × Ideal.Digest)) (topNode : Nat → Nat → AComp Ideal.Digest)
    (remaining : Nat) (message : Ideal.Digest)
    (hs : ∀ lay tree leaf pair, QueriesPermitted (secret lay tree leaf pair))
    (ht : ∀ level, level < Ideal.maxLayerHeight → ∀ node, node < 2^(Ideal.maxLayerHeight-level) →
      QueriesPermitted (topNode level node)) :
    QueriesPermitted (Ideal.Concrete.signLayersPaired 0 index secret topNode remaining message) := by
  induction remaining generalizing message with
  | zero => exact queries_pure _
  | succ remaining ih =>
    unfold Ideal.Concrete.signLayersPaired
    split
    · rename_i hlayer
      split
      · refine queries_bind (queries_signTopLayerPaired index _ topNode message (hs _ _) ht) fun output => ?_
        cases output <;> exact queries_pure _
      · refine queries_bind (queries_encodingSearch 0 ⟨remaining,hlayer⟩ _ _ message _ _) fun output => ?_
        cases output with
        | none => exact queries_pure _
        | some output =>
          refine queries_bind (queries_buildLayerTreePaired ⟨remaining,hlayer⟩ _ _ _ _ (hs _ _)) fun built => ?_
          refine queries_bind (ih built.2.2) fun rest => ?_
          cases rest <;> exact queries_pure _
    · exact queries_pure _

theorem queries_signFromPaired (index : Ideal.Index)
    (ftsSecret : Ideal.FtsTree → Ideal.FtsPair → AComp (Ideal.Digest × Ideal.Digest))
    (otsSecret : Ideal.Layer → Ideal.TreeIndex → Ideal.LeafIndex → Ideal.ChainPair →
      AComp (Ideal.Digest × Ideal.Digest)) (topNode : Nat → Nat → AComp Ideal.Digest)
    (randomness : Ideal.Randomness) (leaves : Ideal.IndexGroup → Ideal.FtsLeaf)
    (hf : ∀ tree pair, QueriesPermitted (ftsSecret tree pair))
    (hs : ∀ lay tree leaf pair, QueriesPermitted (otsSecret lay tree leaf pair))
    (ht : ∀ level, level < Ideal.maxLayerHeight → ∀ node, node < 2^(Ideal.maxLayerHeight-level) →
      QueriesPermitted (topNode level node)) :
    QueriesPermitted (Ideal.Concrete.signFromPaired 0 index ftsSecret otsSecret topNode randomness leaves) := by
  refine queries_bind (queries_buildForestPaired 0 index ftsSecret leaves hf) fun built => ?_
  refine queries_bind (queries_signLayersPaired index otsSecret topNode _ built.2.2 hs ht) fun result => ?_
  cases result <;> exact queries_pure _

theorem queries_signChecked (secretKey : Ideal.Seeded.SecretKey) (hp : secretKey.parameter = 0)
    (cache : Ideal.TopCache) (message : Ideal.Message) :
    QueriesPermitted (Ideal.Seeded.signChecked (m := AComp) secretKey cache message) := by
  refine queries_bind (queries_signDigestPairs secretKey hp message _ _) fun result => ?_
  cases result with
  | none => exact queries_pure _
  | some result =>
    simp only [hp]
    exact queries_signFromPaired _ _ _ _ _ _
      (fun tree pair => queries_ftsSecret 0 secretKey.seed _ tree pair)
      (fun lay tree leaf pair => queries_otsSecret 0 secretKey.seed lay tree leaf pair)
      (fun level hl node hn => queries_cachedTopNode 0 secretKey.seed cache level node hl hn)

/-- The complete signer makes only permitted queries, for arbitrary cache
contents and every oracle answer, including rejection and exhausted searches. -/
theorem queries_sign (secretKey : Ideal.Seeded.SecretKey) (hp : secretKey.parameter = 0)
    (cache : Ideal.TopCache) (message : Ideal.Message) :
    QueriesPermitted (Ideal.Seeded.sign (m := AComp) secretKey cache message) := by
  refine queries_bind (queries_oracleHash _
    (Or.inl (normal_mac secretKey.parameter secretKey.seed cache.region))) fun tag => ?_
  split
  · exact queries_signChecked secretKey hp cache message
  · exact queries_pure _

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem header_split (tag lay tree pos index : Nat) (rest : List Byte) :
    Reference.header tag lay tree pos index ++ rest =
      [byte 2,byte tag,byte lay,byte (tree/2^32)] ++
        (le32 pos ++ (le32 tree ++ (le32 index ++ rest))) := by
  simp [Reference.header,List.append_assoc]

private theorem take_at_length {left : List Byte} (right : List Byte) {n : Nat} (h : left.length = n) :
    (left ++ right).take n = left := by subst h; simp

private theorem drop_at_length {left : List Byte} (right : List Byte) {n : Nat} (h : left.length = n) :
    (left ++ right).drop n = right := by subst h; simp

/-- Formatting the typed chain query produces the exact in-place machine block. -/
theorem chainBlock_header (lay tree pos leaf : Nat) (value : List Byte) (hp : pos < 2^32) :
    chainBlock (Reference.header 1 lay tree pos leaf ++ (zeros 16 ++ value)) =
      Reference.header 1 lay tree (splitPosition pos) leaf ++ zeros 32 ++ value := by
  unfold chainBlock slice
  rw [header_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a,b,c,d] ++ l).take 4 = [a,b,c,d] :=
    fun _ _ _ _ _ => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a,b,c,d] ++ l).drop 4 = l :=
    fun _ _ _ _ _ => rfl
  rw [e4,d4,take_at_length _ (length_le32 pos),leNat_le32,Nat.mod_eq_of_lt hp]
  rw [show (8 : Nat) = 4+4 from rfl,← List.drop_drop,d4,drop_at_length _ (length_le32 pos),
    show (32 : Nat) = 4+28 from rfl,← List.drop_drop,d4,
    show (28 : Nat) = 4+24 from rfl,← List.drop_drop,drop_at_length _ (length_le32 pos),
    show (24 : Nat) = 4+20 from rfl,← List.drop_drop,drop_at_length _ (length_le32 tree),
    show (20 : Nat) = 4+16 from rfl,← List.drop_drop,drop_at_length _ (length_le32 leaf),
    drop_at_length _ (show (zeros 16).length = 16 by simp [zeros])]
  have ht : (le32 tree ++ (le32 leaf ++ (zeros 16 ++ value))).take (4+4) = le32 tree ++ le32 leaf := by
    rw [List.take_add,take_at_length _ (length_le32 tree),drop_at_length _ (length_le32 tree),
      take_at_length _ (length_le32 leaf)]
  rw [ht]
  simp [Reference.header,List.append_assoc]

theorem format_chain_header (lay tree pos leaf : Nat) (value : List Byte)
    (hp : pos < 2^32) (hv : value.length = 16) :
    format (Reference.header 1 lay tree pos leaf ++ (zeros 16 ++ value)) =
      pad64 (Reference.header 1 lay tree (splitPosition pos) leaf ++ zeros 32 ++ value) := by
  have hx : (Reference.header 1 lay tree pos leaf ++ (zeros 16 ++ value)).length = 48 := by
    simp [header_length,zeros,hv]
  have hf : (Reference.header 1 lay tree pos leaf ++ (zeros 16 ++ value)).length = 48 ∧
      (Reference.header 1 lay tree pos leaf ++ (zeros 16 ++ value)).getD 1 0 = byte 1 :=
    ⟨hx,header_tag _ _ _ _ _ _⟩
  rw [format,if_pos hf,chainBlock_header lay tree pos leaf value hp]

theorem chain_query (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (step : Ideal.ChainStep) (value : Ideal.Digest) :
    queryFormat (Ideal.tweakableHashInput 0 (.chain lay tree leaf chain step) (Ideal.bytesLE 16 value)) =
      AddressFormat.queryPerm (pad64 (Reference.chainInput lay.val tree.val leaf.val chain.val
        (step.val+1) (toList value))) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  have hc := chain.isLt
  have hs := step.isLt
  simp only [Ideal.numChains,Ideal.chainLength,Ideal.winternitzBits] at hc hs ⊢
  rw [format_chain_header _ _ _ _ _ (by omega) (length_toList value),
    splitPosition_chain _ _ (by omega)]
  have he : 256*chain.val+step.val = 256*chain.val+(step.val+1)-1 := by omega
  rw [he] <;> rfl

/-- Output truncation is identical in the typed and byte-level models. -/
theorem answerBytes_digest (answer : BitVec 256) :
    answerBytes 16 answer = toList (Ideal.truncateHash answer) :=
  SigGolfCandidate.Equiv.answerBytes_eq answer

theorem hash16_tweakable (parameter : Ideal.PublicParameter) (domain : Ideal.HashDomain)
    (payload : Ideal.HashInput) (input : List Byte)
    (h : queryFormat (Ideal.tweakableHashInput parameter domain payload) =
      AddressFormat.queryPerm (pad64 input)) :
    (fun value : Ideal.Digest => toList value) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.tweakableHash (m := AComp) parameter domain payload) = Reference.h16 input := by
  simp only [Ideal.Concrete.tweakableHash,Ideal.Concrete.oracleHash,
    SigGolfCandidate.Bridge.relabel_bind,SigGolfCandidate.Bridge.relabel_pure,
    HasQuery.query,SigGolfCandidate.Bridge.relabel_query,map_bind,map_pure]
  rw [h]
  simp only [Reference.h16,Reference.hash,answerBytes_digest]

theorem chain_hash (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (step : Ideal.ChainStep) (value : Ideal.Digest) :
    (fun result : Ideal.Digest => toList result) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.tweakableHash (m := AComp) 0 (.chain lay tree leaf chain step) (Ideal.bytesLE 16 value)) =
      Reference.h16 (Reference.chainInput lay.val tree.val leaf.val chain.val (step.val+1) (toList value)) :=
  hash16_tweakable _ _ _ _ (chain_query lay tree leaf chain step value)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec
open SigGolfCandidate.Bridge (relabel relabel_bind relabel_pure)

/-- The entire bounded chain walk agrees, not just one HASH invocation. -/
theorem chain_walk (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (chain : Ideal.ChainIndex) (start steps : Nat) (hs : start+steps ≤ 3) (value : Ideal.Digest) :
    Reference.walk lay.val tree.val leaf.val chain.val (start+1) steps (toList value) =
      (fun result : Ideal.Digest => toList result) <$>
        relabel queryFormat (Ideal.Concrete.chainWalk (m := AComp) 0 lay tree leaf chain start steps value) := by
  unfold Reference.walk
  induction steps with
  | zero => simp [Ideal.Concrete.chainWalk,relabel_pure]
  | succ steps ih =>
    rw [List.range'_concat,List.foldlM_append,ih (by omega)]
    simp only [Ideal.Concrete.chainWalk,relabel_bind,map_bind,bind_map_left,
      Nat.one_mul,List.foldlM_cons,List.foldlM_nil,bind_pure]
    congr 1
    funext current
    have hp : start+steps < Ideal.chainLength-1 := by
      simp only [Ideal.chainLength,Ideal.winternitzBits]
      omega
    rw [dif_pos hp,show start+1+steps = (start+steps)+1 by omega]
    exact (chain_hash lay tree leaf chain ⟨start+steps,hp⟩ current).symm

theorem relabel_oracle_of_format (input : Ideal.HashInput) (raw : List Byte)
    (h : queryFormat input = AddressFormat.queryPerm (pad64 raw)) :
    relabel queryFormat (Ideal.Concrete.oracleHash (m := AComp) input) = Reference.hash raw := by
  simp only [Ideal.Concrete.oracleHash,HasQuery.query,SigGolfCandidate.Bridge.relabel_query]
  rw [h]
  rfl

theorem paired_hash (input : Ideal.HashInput) (raw : List Byte)
    (h : queryFormat input = AddressFormat.queryPerm (pad64 raw)) :
    Reference.pair raw = (fun pair : Ideal.Digest × Ideal.Digest => (toList pair.1,toList pair.2)) <$>
      relabel queryFormat (do
        let output ← Ideal.Concrete.oracleHash (m := AComp) input
        return Ideal.Seeded.splitSecrets output) := by
  simp only [relabel_bind,relabel_oracle_of_format input raw h,relabel_pure,map_bind,map_pure,Reference.pair]
  refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun answer => ?_
  rw [SigGolfCandidate.Equiv.answerBytes_take,SigGolfCandidate.Equiv.answerBytes_drop]
  rfl

theorem ots_secret_query (seed : Ideal.MasterSeed) (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (leaf : Ideal.LeafIndex) (pair : Ideal.ChainPair) :
    queryFormat (Ideal.keygenHashInput 0 (.ots lay tree leaf pair) seed) =
      AddressFormat.queryPerm (pad64 (Reference.input 0 lay.val tree.val pair.val leaf.val (toList seed))) := by
  unfold queryFormat
  simp only [Ideal.keygenHashInput,Ideal.keygenDomainFields,SigGolfCandidate.Equiv.toB_append,
    toB_tweakFields,toB_bytesLE,SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_plain_header _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [Reference.input,List.append_assoc]

theorem fts_secret_query (seed : Ideal.MasterSeed) (index : Ideal.Index) (tree : Ideal.FtsTree)
    (pair : Ideal.FtsPair) :
    queryFormat (Ideal.keygenHashInput 0 (.fts index tree pair) seed) =
      AddressFormat.queryPerm (pad64 (Reference.input 8 tree.val index.val 0 pair.val (toList seed))) := by
  unfold queryFormat
  simp only [Ideal.keygenHashInput,Ideal.keygenDomainFields,SigGolfCandidate.Equiv.toB_append,
    toB_tweakFields,toB_bytesLE,SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_plain_header _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp only [Reference.input,List.append_assoc]

theorem ots_secret_pair (seed : Ideal.MasterSeed) (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (leaf : Ideal.LeafIndex) (pair : Ideal.ChainPair) :
    Reference.pair (Reference.input 0 lay.val tree.val pair.val leaf.val (toList seed)) =
      (fun pair : Ideal.Digest × Ideal.Digest => (toList pair.1,toList pair.2)) <$>
        relabel queryFormat (Ideal.Seeded.otsSecret (m := AComp) 0 seed lay tree leaf pair) :=
  paired_hash _ _ (ots_secret_query seed lay tree leaf pair)

theorem fts_secret_pair (seed : Ideal.MasterSeed) (index : Ideal.Index) (tree : Ideal.FtsTree)
    (pair : Ideal.FtsPair) :
    Reference.pair (Reference.input 8 tree.val index.val 0 pair.val (toList seed)) =
      (fun pair : Ideal.Digest × Ideal.Digest => (toList pair.1,toList pair.2)) <$>
        relabel queryFormat (Ideal.Seeded.ftsSecret (m := AComp) 0 seed index tree pair) :=
  paired_hash _ _ (fts_secret_query seed index tree pair)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem slice_header8 (tag lay tree pos index : Nat) (rest : List Byte) :
    slice (Reference.header tag lay tree pos index ++ rest) 8 4 = le32 tree := by
  rw [SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp [header_length])]
  unfold Reference.header
  rw [SigGolfCandidate.Equiv.hslice_append_left _ _ _ _ (by simp),
    SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp)]
  exact SigGolfCandidate.Equiv.slice_self _ _ (length_le32 tree)

theorem take_header4 (tag lay tree pos index : Nat) (rest : List Byte) :
    (Reference.header tag lay tree pos index ++ rest).take 4 =
      [byte 2,byte tag,byte lay,byte (tree/2^32)] := by
  rw [header_split]
  rfl

/-- Node formatting converts a level/index pair to the machine's heap index,
without changing the parameter or child payload bytes. -/
theorem nodeBlock_header (tag lay tree level index : Nat) (rest : List Byte)
    (hl : level < 2^32) (hi : index < 2^32) :
    nodeBlock (Reference.header tag lay tree level index ++ rest) =
      Reference.header tag lay tree 0
        (2^(nodeHeight (Reference.header tag lay tree level index ++ rest)-level)+index) ++ rest := by
  unfold nodeBlock
  rw [take_header4,slice_header4,slice_header8,slice_header12,leNat_le32,leNat_le32,
    Nat.mod_eq_of_lt hl,Nat.mod_eq_of_lt hi,List.drop_left' (header_length _ _ _ _ _)]
  simp [Reference.header,List.append_assoc]

theorem format_node_header (tag lay tree level index : Nat) (rest : List Byte)
    (hr : rest.length = 48) (ht : tag = 3 ∨ tag = 10 ∨ tag = 13)
    (hl : level < 2^32) (hi : index < 2^32) :
    format (Reference.header tag lay tree level index ++ rest) =
      pad64 (Reference.header tag lay tree 0
        (2^(nodeHeight (Reference.header tag lay tree level index ++ rest)-level)+index) ++ rest) := by
  have hlen : (Reference.header tag lay tree level index ++ rest).length = 64 := by
    simp [header_length,hr]
  have htag : byte tag = byte 3 ∨ byte tag = byte 10 ∨ byte tag = byte 13 := by
    rcases ht with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hf : format (Reference.header tag lay tree level index ++ rest) =
      pad64 (nodeBlock (Reference.header tag lay tree level index ++ rest)) := by
    simp [format,hlen,header_tag,htag]
  rw [hf,nodeBlock_header _ _ _ _ _ _ hl hi]

theorem tree_node_query (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (level index : Nat)
    (left right : Ideal.Digest) (hl : level < 2^32) (hi : index < 2^32) :
    queryFormat (Ideal.tweakableHashInput 0 (.node lay tree level index) (Ideal.Concrete.nodePayload left right)) =
      AddressFormat.queryPerm (pad64 (Reference.treeNode lay.val tree.val level index (toList left) (toList right))) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,Ideal.Concrete.nodePayload,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_node_header _ _ _ _ _ _ (by simp [zeros,length_toList]) (Or.inl rfl) hl hi]
  have hlay : lay.val % 256 = lay.val := Nat.mod_eq_of_lt (by
    have h := lay.isLt
    simp only [Ideal.numLayers] at h
    omega)
  have hh : nodeHeight (Reference.header 3 lay.val tree.val level index ++
      (zeros 16 ++ (toList left ++ toList right))) = Reference.height lay.val := by
    simp [nodeHeight,Reference.header,byte,hlay]
  rw [hh]
  simp only [Reference.treeNode,Reference.input,List.append_assoc]

theorem forest_node_query (index : Ideal.Index) (tree : Ideal.FtsTree) (level node : Nat)
    (left right : Ideal.Digest) (hl : level < 2^32) (hi : node < 2^32) :
    queryFormat (Ideal.tweakableHashInput 0 (.ftsNode index tree level node) (Ideal.Concrete.nodePayload left right)) =
      AddressFormat.queryPerm (pad64 (Reference.forestNode index.val tree.val level node (toList left) (toList right))) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,Ideal.Concrete.nodePayload,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_node_header _ _ _ _ _ _ (by simp [zeros,length_toList]) (Or.inr (Or.inl rfl)) hl hi]
  have hh : nodeHeight (Reference.header 10 tree.val index.val level node ++
      (zeros 16 ++ (toList left ++ toList right))) = 9 := by
    simp [nodeHeight,header_tag]
  rw [hh]
  simp only [Reference.forestNode,Reference.input,List.append_assoc]

theorem tree_node_hash (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (level index : Nat)
    (left right : Ideal.Digest) (hl : level < 2^32) (hi : index < 2^32) :
    (fun result : Ideal.Digest => toList result) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.tweakableHash (m := AComp) 0 (.node lay tree level index) (Ideal.Concrete.nodePayload left right)) =
      Reference.h16 (Reference.treeNode lay.val tree.val level index (toList left) (toList right)) :=
  hash16_tweakable _ _ _ _ (tree_node_query lay tree level index left right hl hi)

theorem forest_node_hash (index : Ideal.Index) (tree : Ideal.FtsTree) (level node : Nat)
    (left right : Ideal.Digest) (hl : level < 2^32) (hi : node < 2^32) :
    (fun result : Ideal.Digest => toList result) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.tweakableHash (m := AComp) 0 (.ftsNode index tree level node) (Ideal.Concrete.nodePayload left right)) =
      Reference.h16 (Reference.forestNode index.val tree.val level node (toList left) (toList right)) :=
  hash16_tweakable _ _ _ _ (forest_node_query index tree level node left right hl hi)

end SigGolfCandidate.Base4Candidate.ByteBridge


namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

theorem format_digest_header (randomness message : List Byte)
    (hr : randomness.length = 16) (hm : message.length = 32) :
    format (Reference.header 12 0 0 0 0 ++
      (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))) =
      pad64 ([byte 2,byte 12] ++ zeros 14 ++ randomness ++ message) := by
  let x := Reference.header 12 0 0 0 0 ++ (zeros 16 ++ (randomness ++ (zeros 16 ++ message)))
  have hx : x.length = 96 := by simp [x,header_length,zeros,hr,hm]
  have ht : x.getD 1 0 = byte 12 := header_tag _ _ _ _ _ _
  have hfirst : x.take 16 = Reference.header 12 0 0 0 0 :=
    List.take_left' (header_length _ _ _ _ _)
  have hrho : slice x 32 16 = randomness := by
    unfold x
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [header_length])]
    simp only [header_length,show 32-16=16 from rfl]
    rw [SigGolfCandidate.Equiv.hslice_append_right _ _ _ _ (by simp [zeros])]
    simp only [zeros,List.length_replicate,Nat.sub_self,slice,List.drop_zero]
    exact List.take_left' hr
  have hprefix : (Reference.header 12 0 0 0 0 ++ zeros 16 ++ randomness ++ zeros 16).length = 64 := by
    simp [header_length,zeros,hr]
  have hmessage : x.drop 64 = message := by
    have h := drop_at_length (left := Reference.header 12 0 0 0 0 ++ zeros 16 ++ randomness ++ zeros 16)
      message hprefix
    simpa only [x,List.append_assoc] using h
  have hf : format x = pad64 (x.take 16 ++ slice x 32 16 ++ x.drop 64) := by
    simp [format,hx,ht]
  change format x = _
  rw [hf,hfirst,hrho,hmessage]
  have hheader : Reference.header 12 0 0 0 0 = [byte 2,byte 12] ++ zeros 14 := by decide
  rw [hheader]

theorem message_digest_query (root : Ideal.Digest) (message : Ideal.Message) (randomness : Ideal.Randomness) :
    queryFormat (Ideal.tweakableHashInput 0 .message (Ideal.Concrete.messageDigestPayload root message randomness)) =
      AddressFormat.queryPerm (pad64 ([byte 2,byte 12] ++ zeros 14 ++ toList randomness ++ toList message)) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,Ideal.Concrete.messageDigestPayload,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_digest_header _ _ (length_toList randomness) (length_toList message)] <;>
    simp only [List.append_assoc]

/-- The byte-level digest retains the full answer; the typed digest retains
exactly the 198 bits consumed by the instance, forest, and acceptance fields. -/
theorem message_digest_agrees (root : Ideal.Digest) (message : Ideal.Message)
    (randomness : Ideal.Randomness) :
    (fun value : Ideal.MessageDigest => value.toNat) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.messageDigest (m := AComp) 0 root message randomness) =
      (fun value : Nat => value % 2^198) <$>
        Reference.digest (toList randomness) (toList message) := by
  simp only [Ideal.Concrete.messageDigest,
    SigGolfCandidate.Bridge.relabel_bind, SigGolfCandidate.Bridge.relabel_pure,
    relabel_oracle_of_format _ _ (message_digest_query root message randomness),
    Reference.digest, map_bind, map_pure]
  congr 1
  funext answer
  congr 1
  simp [Ideal.truncateMessageDigest, Ideal.messageDigestBits, Ideal.totalHeight,
    Ideal.ftsTrees, Ideal.ftsTreeHeight, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

theorem encoding_query (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (message : Ideal.Digest) (counter : Ideal.Counter) :
    queryFormat (Ideal.tweakableHashInput 0 (.encoding lay tree leaf)
      (Ideal.bytesLE 16 message ++ Ideal.bytesLE 4 counter)) =
      AddressFormat.queryPerm (pad64 (Reference.input 4 lay.val tree.val 0 leaf.val
        (toList message ++ le32 counter.toNat))) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,Ideal.hashDomainFields,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_plain_header _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hc : toList counter = le32 counter.toNat := by
    rw [le32,SigGolfCandidate.Equiv.leBytes_eq_toList]
    simp
  simp only [hc,Reference.input,List.append_assoc]

/-- The reference encoding hash and decoder are the typed encoding operation,
with only the decoded word's result representation changed. -/
theorem encoding_agrees (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (message : Ideal.Digest) (counter : Ideal.Counter) :
    Reference.encoding lay.val tree.val leaf.val (toList message) counter.toNat =
      (fun result : Option Ideal.Encoding => result.map fun word => List.ofFn fun i : Ideal.ChainIndex => (word i).val) <$>
        SigGolfCandidate.Bridge.relabel queryFormat
          (Ideal.Concrete.encode (m := AComp) 0 lay tree leaf message counter) := by
  simp only [Ideal.Concrete.encode,Ideal.Concrete.tweakableHash,
    SigGolfCandidate.Bridge.relabel_bind,SigGolfCandidate.Bridge.relabel_pure,
    relabel_oracle_of_format _ _ (encoding_query lay tree leaf message counter),
    map_bind,map_pure,Reference.encoding,bind_assoc,pure_bind] <;> rfl

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- Inputs outside the implemented domains give every other organizer query a
separate abstract name. Tag 255 is never a permitted algorithm query. -/
noncomputable def spareQueryCode (q : Query) : Ideal.HashInput :=
  0 :: 255 :: SigGolfCandidate.Bridge.defaultQEnc q

theorem spareQueryCode_injective : Function.Injective spareQueryCode := by
  intro x y h
  exact SigGolfCandidate.Bridge.defaultQEnc_injective
    (List.cons.inj (List.cons.inj h).2).2

theorem spareQueryCode_not_permitted (q : Query) : ¬ Permitted (spareQueryCode q) := by
  simp [spareQueryCode,Permitted,NormalInput,PaddedInput,
    SigGolfCandidate.Equiv.toB,List.getD,tagLength,byte]

open Classical in
/-- Total organizer-to-abstract map, including arbitrary adversary queries. -/
noncomputable def unformat (q : Query) : Ideal.HashInput :=
  if h : ∃ x, Permitted x ∧ queryFormat x = q then Classical.choose h
  else spareQueryCode q

open Classical in
noncomputable def completeFormat (x : Ideal.HashInput) : Query :=
  if Permitted x then queryFormat x
  else if h : ∃ q, x = spareQueryCode q then Classical.choose h
  else queryFormat x

theorem completeFormat_unformat (q : Query) : completeFormat (unformat q) = q := by
  classical
  unfold unformat
  split_ifs with h
  · have hs := Classical.choose_spec h
    simp [completeFormat,hs.1,hs.2]
  · have hn := spareQueryCode_not_permitted q
    have hex : ∃ q', spareQueryCode q = spareQueryCode q' := ⟨q,rfl⟩
    simp only [completeFormat,hn,if_false,dif_pos hex]
    exact (spareQueryCode_injective (Classical.choose_spec hex)).symm

theorem unformat_completeFormat (x : Ideal.HashInput) (hx : Permitted x) :
    unformat (completeFormat x) = x := by
  classical
  have he : ∃ y, Permitted y ∧ queryFormat y = queryFormat x := ⟨x,hx,rfl⟩
  simp only [completeFormat,hx,if_true,unformat,dif_pos he]
  have hs := Classical.choose_spec he
  exact queryFormat_injective_on hs.1 hx hs.2

theorem unformat_injective : Function.Injective unformat := by
  intro x y h
  rw [← completeFormat_unformat x,← completeFormat_unformat y,h]

/-- Completing the relabelling on adversary-only inputs leaves every keygen,
signer and padded-verifier computation covered by QueriesPermitted unchanged. -/
theorem relabel_completeFormat {α : Type} (oa : AComp α) (h : QueriesPermitted oa) :
    SigGolfCandidate.Bridge.relabel completeFormat oa =
      SigGolfCandidate.Bridge.relabel queryFormat oa := by
  apply SigGolfCandidate.Bridge.relabel_congr_of_allQ Permitted _ h
  intro x hx
  classical
  simp [completeFormat,hx]

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy OracleComp OracleSpec

/-- The completed format preserves the complete lazy-random-oracle experiment,
including uniform coins and arbitrary adaptive organizer-side queries. -/
theorem random_oracle_relabel {α : Type}
    (computation : OracleComp (unifSpec + (Query →ₒ BitVec 256)) α) :
    (simulateQ (SigGolfCandidate.Bridge.roImpl Query (BitVec 256)) computation).run' ∅ =
      (simulateQ (SigGolfCandidate.Bridge.roImpl Ideal.HashInput (BitVec 256))
        (SigGolfCandidate.Bridge.relabelW unformat computation)).run' ∅ := by
  exact SigGolfCandidate.Bridge.run'_relabelW unformat unformat_injective
    computation ∅ ∅ (fun _ => rfl)

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy OracleComp OracleSpec
open SigGolfCandidate.Bridge

/-- Compression weight after exact serialization. In particular, the shortened
message digest costs one block, while the full cache MAC costs 2049 blocks. -/
def compressionWeight (input : Ideal.HashInput) : Nat := (queryFormat input).blocks

/-- Query-format transfer preserves compression counts, not merely hash-call
counts. This is the counter required for the three exponential budget bounds. -/
theorem relabel_compression_count {α : Type} (oa : AComp α) (initialCount : Nat) :
    relabel queryFormat (countFrom compressionWeight oa initialCount) =
      countFrom Query.blocks (relabel queryFormat oa) initialCount := by
  induction oa using OracleComp.inductionOn generalizing initialCount with
  | pure x => rfl
  | query_bind input continuation ih =>
    rw [countFrom_query_bind,relabel_bind,relabel_bind,relabel_query,countFrom_query_bind]
    simp only [ih,compressionWeight]

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- Exact byte agreement for domains that do not shorten or rearrange payloads. -/
theorem plain_domain_query (domain : Ideal.HashDomain) (tag lay tree pos index : Nat)
    (payload : Ideal.HashInput)
    (hf : Ideal.hashDomainFields domain = Ideal.tweakFields tag lay tree pos index)
    (h1 : byte tag ≠ byte 1) (h3 : byte tag ≠ byte 3)
    (h10 : byte tag ≠ byte 10) (h13 : byte tag ≠ byte 13) (h12 : byte tag ≠ byte 12) :
    queryFormat (Ideal.tweakableHashInput 0 domain payload) =
      AddressFormat.queryPerm (pad64 (Reference.input tag lay tree pos index (toB payload))) := by
  unfold queryFormat
  simp only [Ideal.tweakableHashInput,Ideal.tweakBytes,hf,
    SigGolfCandidate.Equiv.toB_append,toB_tweakFields,toB_bytesLE,
    SigGolfCandidate.Equiv.toList_zero,List.append_assoc]
  rw [format_plain_header _ _ _ _ _ _ h1 h3 h10 h13 h12]
  simp only [Reference.input,List.append_assoc]

theorem leaf_hash (lay : Ideal.Layer) (tree : Ideal.TreeIndex) (leaf : Ideal.LeafIndex)
    (endpoints : Ideal.ChainIndex → Ideal.Digest) :
    (fun value : Ideal.Digest => toList value) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.leafHash (m := AComp) 0 lay tree leaf endpoints) =
      Reference.h16 (Reference.input 2 lay.val tree.val 0 leaf.val
        (toB (Ideal.Concrete.leafPayload endpoints))) := by
  apply hash16_tweakable
  exact plain_domain_query _ _ _ _ _ _ _ rfl
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem forest_leaf_hash (index : Ideal.Index) (tree : Ideal.FtsTree) (leaf : Ideal.FtsLeaf)
    (secret : Ideal.Digest) :
    (fun value : Ideal.Digest => toList value) <$>
      SigGolfCandidate.Bridge.relabel queryFormat
        (Ideal.Concrete.ftsLeafHash (m := AComp) 0 index tree leaf secret) =
      Reference.h16 (Reference.input 9 tree.val index.val 0 leaf.val (toList secret)) := by
  apply hash16_tweakable
  simpa only [toB_bytesLE] using
    plain_domain_query (.ftsLeaf index tree leaf) 9 tree.val index.val 0 leaf.val
      (Ideal.bytesLE 16 secret) rfl
      (by decide) (by decide) (by decide) (by decide) (by decide)

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec

/-- The reference's layer cuts agree with the typed four-layer hypertree. -/
theorem layer_route_tables (lay : Ideal.Layer) :
    (if lay.val = 0 then 21 else 7 * (3-lay.val)) = Ideal.heightBelow lay ∧
    Reference.height lay.val = Ideal.layerHeight lay ∧
    (if lay.val = 0 then 21 else 7 * (3-lay.val)) + Reference.height lay.val =
      Ideal.totalHeight - Ideal.heightAbove lay := by
  revert lay
  decide

theorem route_agrees (index : Ideal.Index) (lay : Ideal.Layer) :
    Reference.route index.val lay.val =
      ((Ideal.Concrete.leafIndexAt index lay).val,
       (Ideal.Concrete.treeIndexAt index lay).val) := by
  obtain ⟨hcut, hheight, htree⟩ := layer_route_tables lay
  simp only [Reference.route, Ideal.Concrete.leafIndexAt, Ideal.Concrete.treeIndexAt]
  rw [← htree, hcut, hheight]

theorem recover_chain_agrees (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (leaf : Ideal.LeafIndex) (chain : Ideal.ChainIndex) (digit : Ideal.Digit)
    (value : Ideal.Digest) :
    Reference.walk lay.val tree.val leaf.val chain.val (digit.val+1) (3-digit.val) (toList value) =
      (fun result : Ideal.Digest => toList result) <$>
        SigGolfCandidate.Bridge.relabel queryFormat
          (Ideal.Concrete.recoverChain (m := AComp) 0 lay tree leaf chain digit value) := by
  have hd : digit.val ≤ 3 := by
    have h := digit.isLt
    simp only [Ideal.chainLength, Ideal.winternitzBits] at h
    omega
  simpa only [Ideal.Concrete.recoverChain, Ideal.chainLength, Ideal.winternitzBits] using
    chain_walk lay tree leaf chain digit.val (3-digit.val) (by omega) value

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec
open SigGolfCandidate.Bridge (relabel relabel_bind relabel_pure)

/-- Transfer a bounded authentication-path fold, including both child orders.
The hash agreement is needed only at the levels actually visited. -/
theorem fold_path_aux (node : Reference.Node) (leaf : Nat)
    (hashNode : Nat → Nat → Ideal.Digest → Ideal.Digest → AComp Ideal.Digest)
    (sibling : Nat → Ideal.Digest) (fold : Nat → Ideal.Digest → AComp Ideal.Digest)
    (hzero : ∀ v, fold 0 v = pure v)
    (hstep : ∀ level v, fold (level+1) v = do
      let cur ← fold level v
      if leaf.testBit level then
        hashNode (level+1) (leaf / 2^(level+1)) (sibling level) cur
      else hashNode (level+1) (leaf / 2^(level+1)) cur (sibling level))
    (ps : List Val) (n : Nat)
    (hps : ∀ level < n, ps.getD level [] = toList (sibling level))
    (hnode : ∀ level < n, ∀ left right : Ideal.Digest,
      Reference.h16 (node (level+1) (leaf / 2^(level+1)) (toList left) (toList right)) =
        (fun result : Ideal.Digest => toList result) <$>
          relabel queryFormat (hashNode (level+1) (leaf / 2^(level+1)) left right))
    (v : Ideal.Digest) :
    (List.range n).foldlM (fun cur level =>
      if leaf / 2^level % 2 = 0 then
        Reference.h16 (node (level+1) (leaf / 2^(level+1)) cur (ps.getD level []))
      else Reference.h16 (node (level+1) (leaf / 2^(level+1)) (ps.getD level []) cur)) (toList v) =
      (fun result : Ideal.Digest => toList result) <$> relabel queryFormat (fold n v) := by
  induction n with
  | zero => simp [hzero, relabel_pure]
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append,
      ih (fun level hl => hps level (by omega))
        (fun level hl => hnode level (by omega))]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, bind_map_left,
      hstep, relabel_bind, map_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun cur => ?_
    rw [hps n (by omega)]
    have hmod : leaf / 2^n % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases hb : leaf.testBit n = true
    · have hone : leaf / 2^n % 2 = 1 := by
        simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff] using hb
      rw [if_neg (by omega), if_pos hb, hnode n (by omega)]
    · have hzeroBit : leaf / 2^n % 2 = 0 := by
        have hne : leaf / 2^n % 2 ≠ 1 := by
          simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff] using hb
        omega
      rw [if_pos hzeroBit, if_neg hb, hnode n (by omega)]

end SigGolfCandidate.Base4Candidate.ByteBridge

namespace SigGolfCandidate.Base4Candidate.ByteBridge
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp OracleSpec
open SigGolfCandidate.Bridge (relabel)

/-- Authentication paths agree for every supplied sibling value, without an
honesty assumption on the witness. -/
theorem tree_fold_agrees (lay : Ideal.Layer) (tree : Ideal.TreeIndex)
    (leaf : Ideal.LeafIndex) (path : Nat → Ideal.Digest) (n : Nat) (hn : n ≤ 12)
    (value : Ideal.Digest) :
    Reference.foldPath (Reference.treeNode lay.val tree.val) leaf.val (toList value)
      ((List.range n).map fun level => toList (path level)) =
      (fun result : Ideal.Digest => toList result) <$>
        relabel queryFormat (Ideal.Concrete.treeFold (m := AComp) 0 lay tree leaf path n value) := by
  unfold Reference.foldPath
  simp only [List.length_map, List.length_range]
  apply fold_path_aux (Reference.treeNode lay.val tree.val) leaf.val
    (fun level index left right => Ideal.Concrete.tweakableHash (m := AComp) 0
      (.node lay tree level index) (Ideal.Concrete.nodePayload left right))
    path (Ideal.Concrete.treeFold (m := AComp) 0 lay tree leaf path)
  · intro v
    exact Ideal.Concrete.treeFold_zero_eq _ _ _ _ _ _
  · intro level v
    exact Ideal.Concrete.treeFold_succ_eq _ _ _ _ _ _ _
  · intro level hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
    rfl
  · intro level hl left right
    have hi : leaf.val / 2^(level+1) < 2^32 := by
      have hleaf := leaf.isLt
      simp only [Ideal.maxLayerHeight] at hleaf
      have hdiv := Nat.div_le_self leaf.val (2^(level+1))
      omega
    exact (tree_node_hash lay tree (level+1) (leaf.val / 2^(level+1))
      left right (by omega) hi).symm

/-- The serialized digest selects the same hypertree instance and FORS leaves. -/
theorem digest_index_agrees (digest : Ideal.MessageDigest) :
    Reference.instanceIndex digest.toNat = (Ideal.Concrete.digestIndex digest).val := by
  simp [Reference.instanceIndex, Ideal.Concrete.digestIndex, Ideal.totalHeight,
    BitVec.toNat_extractLsb', Nat.shiftRight_eq_div_pow]

theorem digest_forest_index_agrees (digest : Ideal.MessageDigest) (tree : Ideal.FtsTree) :
    Reference.forestIndex digest.toNat tree.val =
      (Ideal.Concrete.digestLeaves digest (Ideal.Concrete.ftsIndexOf tree)).val := by
  simp [Reference.forestIndex, Ideal.Concrete.digestLeaves, Ideal.Concrete.ftsIndexOf,
    Ideal.totalHeight, Ideal.ftsTreeHeight, BitVec.toNat_extractLsb', Nat.shiftRight_eq_div_pow, Nat.mul_comm]

end SigGolfCandidate.Base4Candidate.ByteBridge
