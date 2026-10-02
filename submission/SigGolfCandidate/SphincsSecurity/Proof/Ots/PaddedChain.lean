import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Descent
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Queried
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
import SigGolfCandidate.SphincsSecurity.Proof.Ots.Code
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.GraphPayloadInputs
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraphSampling
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Honest
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixOracle

/-!
# Padded WOTS chains (W1a)

The padded verifier `verifyP` (`Scheme.lean`) hashes every chain step with the forgery's pad in the
payload. This module relates it to the record verifier:

* zero pads: `verifyP_zero` (the padded verifier *is* `verify`), and more generally a layer whose
  padded chains all have pad `0` or digit `7` makes exactly the record layer's queries and value
  (`otsLeafAttemptP_run_eq_of_inactive`);
* **the padded last-step hit** (`recoverChainP_active_hit`): a padded walk (nonzero pad, digit below
  `7`) that ends on the honest endpoint ends with a query at `Position.lastChainStep` whose 48-byte
  payload is not the honest one and whose answer is the honest endpoint;
* padded inputs in the canonical graph: they are hashed at their chain position and no other, they are
  canonical-graph inputs, and (80 bytes) they are no OTS prefix row;
* the verify-level descent with pads (`verifyP_extract`, `LayerFrameP`, `hypertree_walkP`), the
  analogues of `Hypertree/Descent.lean`.
-/

open OracleComp OracleSpec

namespace SphincsSecurity

namespace Concrete

section defs

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-! ### Zero pads: the record verifier -/

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

/-- An inactive chain: pad `0`, or digit `7` (no step is hashed). -/
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

/-- **Completeness side**: with zero pads the padded verifier is the record verifier. -/
theorem verifyP_zero (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verifyP (m := m) publicKey message signature (fun _ _ => 0) = verify publicKey message signature := by
  unfold verifyP verify verifyCoreP verifyCore
  split
  · refine bind_congr fun digest => bind_congr fun key => ?_
    cases key with
    | none => rfl
    | some key =>
        simp only
        rw [verifyLayersP_zero]
  · rfl

end defs

/-! ### Padded walks under an answer function -/

section eval

attribute [local irreducible] canonicalPayloadInputs canonicalGraphInputs

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
  (leaf : LeafIndex) (chainIdx : ChainIndex) (pad : Pad)

theorem length_bytesLE16 (value : Digest) : (bytesLE 16 value).length = 16 := by
  simp [bytesLE]

/-- A nonzero pad makes a 48-byte payload. -/
theorem chainPayload_length_of_ne {pad : Pad} (hpad : pad ≠ 0) (value : Digest) :
    (chainPayload pad value).length = 48 := by
  simp only [chainPayload, if_neg hpad, List.length_append, length_bytesLE16]

/-- A padded payload is never a record (16-byte) chain payload. -/
theorem chainPayload_ne_digestBytes {pad : Pad} (hpad : pad ≠ 0) (value other : Digest) :
    chainPayload pad value ≠ digestBytes other := by
  intro h
  have := congrArg List.length h
  rw [chainPayload_length_of_ne hpad, digestBytes_length] at this
  omega

/-- A padded payload is three digests, so it is a canonical-graph payload. -/
theorem chainPayload_mem_canonicalPayloadInputs (pad : Pad) (value : Digest) :
    chainPayload pad value ∈ canonicalPayloadInputs := by
  unfold chainPayload
  split
  · exact digestBytes_mem_canonicalPayloadInputs value
  · have h := flatMap_mem_canonicalPayloadInputs [pad.1, pad.2, value]
      (by change 3 ≤ numChains; decide)
    have e : [pad.1, pad.2, value].flatMap digestBytes =
        bytesLE 16 pad.1 ++ bytesLE 16 pad.2 ++ bytesLE 16 value := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    rw [e] at h
    exact h

/-- What the padded walk has reached after `steps` steps from `start`. -/
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

theorem lastChainStep_val : Position.lastChainStep.val = chainLength - 2 := rfl

theorem lastChainStep_succ : Position.lastChainStep.val + 1 = chainLength - 1 := by
  simp [Position.lastChainStep, chainLength, winternitzBits]

/-- **The padded last-step hit.** A padded walk (`pad ≠ 0`, digit below `7`) that ends on the honest
endpoint ends with a query at `lastChainStep` whose payload is not the honest one (it has 48 bytes) and
whose answer is the honest endpoint. No induction over the walk: only the last query matters. -/
theorem recoverChainP_active_hit (secret : Digest) (digit : Digit) (value : Digest)
    (hpad : pad ≠ 0) (hdigit : digit.val < chainLength - 1)
    (hend : evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx pad digit value) =
      honestChain f parameter lay tree leaf chainIdx secret (chainLength - 1)) :
    ∃ previous : Digest,
      tweakableHashInput parameter (.chain lay tree leaf chainIdx Position.lastChainStep)
          (chainPayload pad previous)
        ∈ queriedInputs f (recoverChainP parameter lay tree leaf chainIdx pad digit value) ∧
      chainPayload pad previous ≠
        digestBytes (honestChain f parameter lay tree leaf chainIdx secret Position.lastChainStep.val) ∧
      truncateHash (f (tweakableHashInput parameter (.chain lay tree leaf chainIdx Position.lastChainStep)
          (chainPayload pad previous)))
        = honestChain f parameter lay tree leaf chainIdx secret (Position.lastChainStep.val + 1) := by
  have hlen : chainLength = 8 := by simp [chainLength, winternitzBits]
  obtain ⟨n, hn⟩ : ∃ n, chainLength - 1 - digit.val = n + 1 := ⟨chainLength - 2 - digit.val, by omega⟩
  have hrange : digit.val + n < chainLength - 1 := by omega
  have hstep : (⟨digit.val + n, hrange⟩ : ChainStep) = Position.lastChainStep := by
    apply Fin.ext
    simp only [Position.lastChainStep]
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

/-! ### Inactive pads: the record's layer -/

/-- Every padded chain of the layer is inactive: pad `0` or digit `7`. -/
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
theorem otsLeafAttemptP_run_eq_of_inactive (message : Digest) (counter : Counter)
    (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (hinactive : PadsInactive pads codeword) :
    evalWithAnswerFn f (otsLeafAttemptP parameter lay tree leaf message counter values pads) =
        evalWithAnswerFn f (otsLeafAttempt parameter lay tree leaf message counter values) ∧
      queriedInputs f (otsLeafAttemptP parameter lay tree leaf message counter values pads) =
        queriedInputs f (otsLeafAttempt parameter lay tree leaf message counter values) := by
  have hseq : (sequenceFin fun chainIdx => recoverChainP parameter lay tree leaf chainIdx (pads chainIdx)
        (codeword chainIdx) (values chainIdx) : OracleComp HashSpec (ChainIndex → Digest)) =
      sequenceFin fun chainIdx => recoverChain parameter lay tree leaf chainIdx (codeword chainIdx)
        (values chainIdx) := by
    congr 1
    funext chainIdx
    exact recoverChainP_eq_of_inactive parameter lay tree leaf chainIdx _ _ _ (hinactive chainIdx)
  unfold otsLeafAttemptP otsLeafAttempt
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, queriedInputs_bind, queriedInputs_bind, hencode]
  simp only [hseq]
  refine ⟨?_, ?_⟩ <;> trivial

theorem cachedRun_otsLeafAttemptP_iff_of_inactive (cache : QueryCache HashSpec) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (hinactive : PadsInactive pads codeword) :
    CachedRun cache f (otsLeafAttemptP parameter lay tree leaf message counter values pads) ↔
      CachedRun cache f (otsLeafAttempt parameter lay tree leaf message counter values) := by
  unfold CachedRun
  rw [(otsLeafAttemptP_run_eq_of_inactive f parameter lay tree leaf message counter values pads codeword
    hencode hinactive).2]

/-! ### Where the padded leaf's queries are -/

theorem otsLeafP_leaf_query_mem (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword) :
    tweakableHashInput parameter (.leaf lay tree leaf)
        (leafPayload fun chainIdx => evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
          (pads chainIdx) (codeword chainIdx) (values chainIdx)))
      ∈ queriedInputs f (otsLeafAttemptP parameter lay tree leaf message counter values pads) := by
  simp only [otsLeafAttemptP]
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
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword)
    (chainIdx : ChainIndex) {input : HashInput}
    (hinput : input ∈ queriedInputs f (recoverChainP parameter lay tree leaf chainIdx (pads chainIdx)
      (codeword chainIdx) (values chainIdx))) :
    input ∈ queriedInputs f (otsLeafAttemptP parameter lay tree leaf message counter values pads) := by
  simp only [otsLeafAttemptP]
  apply queriedInputs_mono_bind_right
  rw [hencode]
  apply queriedInputs_mono_bind_left
  exact sequenceFin_component_query_mem f _ chainIdx hinput

theorem eval_otsLeafAttemptP (message : Digest) (counter : Counter) (values : ChainIndex → Digest)
    (pads : ChainIndex → Pad) (codeword : Encoding)
    (hencode : evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter) = some codeword) :
    evalWithAnswerFn f (otsLeafAttemptP parameter lay tree leaf message counter values pads) =
      some (truncateHash (f (tweakableHashInput parameter (.leaf lay tree leaf)
        (leafPayload fun chainIdx => evalWithAnswerFn f (recoverChainP parameter lay tree leaf chainIdx
          (pads chainIdx) (codeword chainIdx) (values chainIdx)))))) := by
  simp only [otsLeafAttemptP, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure, leafHash, eval_tweakableHash]

end eval

/-! ## Padded inputs in the canonical graph -/

section padded_inputs

attribute [local irreducible] canonicalPayloadInputs canonicalGraphInputs instFintypePosition

variable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  (chainIdx : ChainIndex) (step : ChainStep) (pad : Pad) (previous : Digest)

theorem length_tweakableHashInput' (domain : HashDomain) (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp only [tweakableHashInput, tweakBytes, fieldBytes, bytesLE, List.length_append, List.length_ofFn,
    List.length_singleton]

/-- The padded input of a chain step. -/
abbrev paddedInput : HashInput :=
  tweakableHashInput parameter (.chain lay tree leaf chainIdx step) (chainPayload pad previous)

theorem paddedInput_length (hpad : pad ≠ 0) :
    (paddedInput parameter lay tree leaf chainIdx step pad previous).length = 80 := by
  rw [paddedInput, length_tweakableHashInput', chainPayload_length_of_ne hpad]

/-- A padded input is hashed at its chain position ... -/
theorem paddedInput_atPosition :
    AtPosition parameter (paddedInput parameter lay tree leaf chainIdx step pad previous)
      (.chain lay tree leaf chainIdx step) := ⟨_, rfl⟩

/-- ... and at no other: **atPosition uniqueness for padded payloads** (the pad is payload, not tweak). -/
theorem paddedInput_position_unique {position : Position}
    (h : AtPosition parameter (paddedInput parameter lay tree leaf chainIdx step pad previous) position) :
    position = .chain lay tree leaf chainIdx step :=
  atPosition_unique parameter h (paddedInput_atPosition parameter lay tree leaf chainIdx step pad previous)

/-- A padded input is a canonical-graph input (its payload is three digests). -/
theorem paddedInput_mem_canonicalGraphInputs :
    paddedInput parameter lay tree leaf chainIdx step pad previous ∈ canonicalGraphInputs parameter :=
  graphInput_mem_of_payload parameter (.chain lay tree leaf chainIdx step) _
    (chainPayload_mem_canonicalPayloadInputs pad previous)

/-- An OTS prefix row has 48 bytes. -/
theorem OtsPrefix.input_length (segment : OtsPrefix) (query : segment.Query) :
    (segment.input query).length = 48 := by
  rw [OtsPrefix.input, length_tweakableHashInput', digestBytes_length]

/-- A padded input (80 bytes) is no OTS prefix row, at any address, whatever the reference words. -/
theorem parse_eq_none_of_length {segment : OtsPrefix} {input : HashInput} (h : input.length ≠ 48) :
    segment.parse input = none := by
  cases hq : segment.parse input with
  | none => rfl
  | some query =>
      exact absurd (((segment.parse_some_iff input query).mp hq) ▸ OtsPrefix.input_length segment query) h

/-- A padded input is not the honest input of its position. -/
theorem paddedInput_ne_honestInput (f : QueryImpl HashSpec Id)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (hpad : pad ≠ 0) :
    paddedInput parameter lay tree leaf chainIdx step pad previous ≠
      honestInput f parameter otsSecret ftsSecret (.chain lay tree leaf chainIdx step) := by
  intro heq
  have hp := (tweakableHashInput_injective parameter (Position.domain_inRange (.chain lay tree leaf chainIdx step))
    (Position.domain_inRange (.chain lay tree leaf chainIdx step)) heq).2
  exact chainPayload_ne_digestBytes hpad previous _ hp

end padded_inputs

/-! ## The verify-level chain: `StatementLemmas`, `Support`, `Descent` with pads -/

section descent

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

theorem verifyLayersP_succ_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (pads : ChainPads) (remaining : Nat) (message : Digest) :
    verifyLayersP (m := m) parameter index signature pads (remaining + 1) message
      = (if hlayer : remaining < numLayers then
          (do
            match ← otsLeafAttemptP parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
                (leafIndexAt index ⟨remaining, hlayer⟩) message
                (signature.counter ⟨remaining, hlayer⟩)
                (signature.chainValue ⟨remaining, hlayer⟩) (pads ⟨remaining, hlayer⟩) with
            | none => pure none
            | some value => do
                let root ← treeFold parameter ⟨remaining, hlayer⟩
                  (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩)
                  (signaturePath signature ⟨remaining, hlayer⟩) (layerHeight ⟨remaining, hlayer⟩)
                  value
                verifyLayersP parameter index signature pads remaining root)
        else pure none) := by
  rw [verifyLayersP]
  split
  · simp only [otsLeafP_eq]
    apply bind_congr
    intro result
    cases result <;> rfl
  · rfl

theorem verifyCoreP_eq (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads) :
    verifyCoreP (m := m) publicKey message signature pads
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          match ← ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts with
          | none => return false
          | some ftsPublicKey =>
              match ← verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers
                  ftsPublicKey with
              | none => return false
              | some root => return decide (root = publicKey.root)) := by
  unfold verifyCoreP
  apply bind_congr
  intro digest
  apply bind_congr
  intro key
  cases key with
  | none => rfl
  | some key =>
      apply bind_congr
      intro result
      cases result <;> rfl

theorem verifyP_eq_ite (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads) :
    verifyP (m := m) publicKey message signature pads =
      if CountersInRange signature then verifyCoreP publicKey message signature pads else pure false := by
  rw [verifyP]

theorem verifyP_eq (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads)
    (hcounters : CountersInRange signature) :
    verifyP (m := m) publicKey message signature pads = verifyCoreP publicKey message signature pads := by
  rw [verifyP, if_pos hcounters]

theorem verifyP_eq_of_not_counters (publicKey : PublicKey) (message : Message) (signature : Signature)
    (pads : ChainPads) (hcounters : ¬ CountersInRange signature) :
    verifyP (m := m) publicKey message signature pads = pure false := by
  rw [verifyP, if_neg hcounters]

end descent

section descentEval

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter} {cache : QueryCache HashSpec}

theorem verifyLayersP_succ_extract (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (index : Index) (signature : Signature) (pads : ChainPads) (remaining : Nat) (hlayer : remaining < numLayers)
    (message : Digest) (target : Digest)
    (hverify : evalWithAnswerFn f
        (verifyLayersP parameter index signature pads (remaining + 1) message) = some target) :
    ∃ leafValue, evalWithAnswerFn f (otsLeafAttemptP parameter ⟨remaining, hlayer⟩
          (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
          (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩)
          (pads ⟨remaining, hlayer⟩))
        = some leafValue
      ∧ evalWithAnswerFn f (verifyLayersP parameter index signature pads remaining
          (foldValue f parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
            (leafIndexAt index ⟨remaining, hlayer⟩) (signaturePath signature ⟨remaining, hlayer⟩)
            leafValue (layerHeight ⟨remaining, hlayer⟩))) = some target := by
  rcases hleaf : evalWithAnswerFn f (otsLeafAttemptP parameter ⟨remaining, hlayer⟩
      (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩) message
      (signature.counter ⟨remaining, hlayer⟩) (signature.chainValue ⟨remaining, hlayer⟩)
      (pads ⟨remaining, hlayer⟩))
    with _ | leafValue
  · rw [verifyLayersP_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simp at hverify
  · refine ⟨leafValue, rfl, ?_⟩
    rw [verifyLayersP_succ_eq, dif_pos hlayer, evalWithAnswerFn_bind, hleaf] at hverify
    simpa [foldValue, evalWithAnswerFn_bind] using hverify

theorem counters_of_verifyP (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads)
    (hverify : evalWithAnswerFn f (verifyP publicKey message signature pads) = true) :
    CountersInRange signature := by
  by_contra hcounters
  rw [verifyP_eq_of_not_counters publicKey message signature pads hcounters] at hverify
  simp at hverify

/-- `verify_extract` with pads (`Hypertree/Descent.lean:32`). -/
theorem verifyP_extract (publicKey : PublicKey) (message : Message) (signature : Signature) (pads : ChainPads)
    (hverify : evalWithAnswerFn f (verifyP publicKey message signature pads) = true)
    (hrun : CachedRun cache f (verifyP publicKey message signature pads)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ ∃ ftsPublicKey : Digest,
          evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts) = some ftsPublicKey
            ∧ evalWithAnswerFn f
              (verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts)
            ∧ CachedRun cache f
              (verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers ftsPublicKey) := by
  have hcounters := counters_of_verifyP publicKey message signature pads hverify
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  rw [verifyP_eq _ _ _ _ hcounters, verifyCoreP_eq] at hverify hrun
  rw [evalWithAnswerFn_bind] at hverify
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  change evalWithAnswerFn f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) = true at hverify
  change CachedRun cache f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts := hafterDigest.bind_left
  rw [evalWithAnswerFn_bind] at hverify
  have hafterFts := hafterDigest.bind_right
  revert hverify hafterFts
  cases hkey : evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
      (slotValue (digestLeaves digest)) signature.fts) with
  | none => intro hverify; simp at hverify
  | some ftsPublicKey =>
      intro hverify hafterFts
      simp only at hverify hafterFts
      rw [evalWithAnswerFn_bind] at hverify
      have hlayersRun := hafterFts.bind_left
      refine ⟨digest, rfl, hmessageRun, ftsPublicKey, hkey, ?_, hfts, hlayersRun⟩
      cases hresult : evalWithAnswerFn f
          (verifyLayersP publicKey.parameter (digestIndex digest) signature pads numLayers ftsPublicKey) with
      | none =>
          rw [hresult] at hverify
          simp at hverify
      | some root =>
          rw [hresult] at hverify
          simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
          simp [hverify]

/-- `LayerFrame` with pads (`Hypertree/Descent.lean:127`). -/
def LayerFrameP (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature) (pads : ChainPads)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeafAttemptP parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay) (pads lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayersP parameter index signature pads lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeafAttemptP parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay) (pads lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayersP parameter index signature pads lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))

theorem layerFrameP_of_verify (index : Index) (signature : Signature) (pads : ChainPads)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayersP parameter index signature pads (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayersP parameter index signature pads (lay.val + 1) message)) :
    ∃ leafValue, LayerFrameP f cache parameter index signature pads lay message target leafValue := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayersP_succ_extract f parameter index signature pads lay.val lay.isLt message target hverify
  rw [verifyLayersP_succ_eq, dif_pos lay.isLt] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩

/-- **The hypertree walk with pads** (`hypertree_walk`, `Hypertree/Descent.lean:169`, verbatim with
`LayerFrameP`/`verifyLayersP`). -/
theorem hypertree_walkP (key : SecretKey) (index : Index) (signature : Signature) (pads : ChainPads)
    (Q : Layer → Prop)
    (hstep : ∀ lay message leafValue,
      LayerFrameP f cache key.parameter index signature pads lay message key.root leafValue →
      foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) leafValue (layerHeight lay) =
        honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
          (layerHeight lay) 0 →
      message = evalWithAnswerFn f (layerMessage key index lay) ∧ Q lay)
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)
      (layerHeight topLayer) 0)
    (ftsPublicKey : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayersP key.parameter index signature pads numLayers ftsPublicKey) = some key.root)
    (hrun : CachedRun cache f (verifyLayersP key.parameter index signature pads numLayers ftsPublicKey)) :
    (∀ lay, Q lay) ∧ ftsPublicKey = evalWithAnswerFn f (layerMessage key index bottomLayer) := by
  have hwalk : ∀ remaining, (hr : remaining ≤ numLayers) → ∀ message,
      evalWithAnswerFn f (verifyLayersP key.parameter index signature pads remaining message) = some key.root →
      CachedRun cache f (verifyLayersP key.parameter index signature pads remaining message) →
      (∀ lay : Layer, lay.val < remaining → Q lay) ∧
        (∀ h : 0 < remaining,
          message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by have := hr; omega⟩)) ∧
        (remaining = 0 → message = key.root) := by
    intro remaining
    induction remaining with
    | zero =>
        intro _ message hv _
        simp only [verifyLayersP, evalWithAnswerFn_pure, Option.some.injEq] at hv
        exact ⟨fun lay h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
          fun _ => hv⟩
    | succ r ih =>
        intro hr message hv hc
        have hlayer : r < numLayers := by omega
        let lay : Layer := ⟨r, hlayer⟩
        obtain ⟨leafValue, hframe⟩ :=
          layerFrameP_of_verify (f := f) (cache := cache) index signature pads lay message key.root hv hc
        have hrest := ih (by omega) _ hframe.2.1 hframe.2.2.2.2
        have hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay) =
            honestNode f key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0 := by
          rcases Nat.eq_zero_or_pos r with hzero | hpos
          · have htop : lay = topLayer := Fin.ext hzero
            have htree : treeIndexAt index lay = rootTree := by
              rw [htop]
              exact Fin.ext (treeIndexAt_topLayer index)
            rw [hrest.2.2 hzero, hroot, htree, htop]
          · rw [hrest.2.1 hpos]
            have hbelow : r - 1 + 1 < numLayers := by omega
            rw [layerMessage_of_lt key index ⟨r - 1, by omega⟩ hbelow]
            have hl : (⟨r - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl]
            rfl
        obtain ⟨hmessage, hq⟩ := hstep lay message leafValue hframe hfold
        refine ⟨fun other hother => ?_, fun _ => hmessage, fun h => absurd h (Nat.succ_ne_zero r)⟩
        by_cases heq : other.val = r
        · have : other = lay := Fin.ext heq
          rw [this]
          exact hq
        · exact hrest.1 other (by omega)
  obtain ⟨hq, hmessage, _⟩ := hwalk numLayers le_rfl ftsPublicKey hverify hrun
  exact ⟨fun lay => hq lay lay.isLt, hmessage (by decide)⟩

end descentEval

end Concrete

end SphincsSecurity
