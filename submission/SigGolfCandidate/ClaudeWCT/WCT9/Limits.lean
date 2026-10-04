import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
def digestAttemptLimit : Nat := 2 ^ 21
theorem digestAttemptLimit_eq : digestAttemptLimit = 2097152 := by
  norm_num [digestAttemptLimit]
theorem digestAttemptLimit_eq_two_mul : digestAttemptLimit = 2 * SigGolfCandidate.T3.attemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
theorem digestAttemptLimit_le : digestAttemptLimit ≤ 2 ^ 32 := by
  norm_num [digestAttemptLimit]
theorem attemptLimit_le_digestAttemptLimit : SigGolfCandidate.T3.attemptLimit ≤ digestAttemptLimit := by
  norm_num [digestAttemptLimit, SigGolfCandidate.T3.attemptLimit]
def signPayloadWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let rho ← privateNonce message
  let some (_, output) ← digestSearch rho message 0 limit | pure none
  let index := output.toNat % 2 ^ 31
  let state ← (List.finRange 9).foldlM
    (fun (state : List Opening × List Digest) coord => do
      let selected := child output coord
      let (levels, values) ← buildCoordinate index coord selected (rank output coord)
      let path := (List.range 7).map fun level =>
        (levels.getD level []).getD (selected.val / 2 ^ level ^^^ 1) 0
      let opening : Opening := ⟨fun i => values.getD i.val 0, fun i => path.getD i.val 0⟩
      pure (state.1 ++ [opening], state.2 ++ [(levels.getD 7 []).getD 0 0])) ([], [])
  let root ← forestPk index state.2
  let some layers ← signLayers cache index 4 root | pure none
  pure (some ⟨rho, fun coord => state.1.getD coord.val ⟨fun _ => 0, fun _ => 0⟩,
    fun lay => piecesSignature lay (layers.getD lay.val ([], []))⟩)
def signWith (limit : Nat) (cache : Cache) (message : Message) : M (Option Signature) := do
  let tag ← privateMac cache.region
  if tag ≠ cache.tag then return none
  signPayloadWith limit cache message
def expandWith (limit : Nat) (message : Message) (pk : Digest) (sig : Signature) :
    M (Option Witness) := do
  let some (counter, output) ← digestSearch sig.rho message 0 limit | pure none
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts sig index output
  let some (root, counters) ← expandLayers (toT3Signature sig) index 4 root | pure none
  if root ≠ pk then return none
  pure (some ⟨sig, counter, fun lay => counters.getD lay.val 0⟩)
def verifyWith (limit : Nat) (message : Message) (pk : Digest) (w : Witness) : M Bool := do
  if w.digestCounter.toNat ≥ limit then return false
  let output ← digest w.signature.rho message w.digestCounter
  if !admissible output then return false
  let index := output.toNat % 2 ^ 31
  let root ← recoverFts w.signature index output
  let some root ← verifyLayers (toT3Witness w) index 4 root | pure false
  pure (root == pk)
theorem signPayloadWith_attemptLimit :
    signPayloadWith SigGolfCandidate.T3.attemptLimit = signPayload := rfl
theorem signWith_attemptLimit : signWith SigGolfCandidate.T3.attemptLimit = sign := rfl
theorem expandWith_attemptLimit : expandWith SigGolfCandidate.T3.attemptLimit = expand := rfl
theorem verifyWith_attemptLimit : verifyWith SigGolfCandidate.T3.attemptLimit = verify := rfl
namespace Rev3
def signPayload (cache : Cache) (message : Message) : M (Option Signature) :=
  signPayloadWith digestAttemptLimit cache message
def sign (cache : Cache) (message : Message) : M (Option Signature) :=
  signWith digestAttemptLimit cache message
def expand (message : Message) (pk : Digest) (sig : Signature) : M (Option Witness) :=
  expandWith digestAttemptLimit message pk sig
def verify (message : Message) (pk : Digest) (w : Witness) : M Bool :=
  verifyWith digestAttemptLimit message pk w
def keygen : M (Digest × Cache) := ClaudeWCT.WCT9.keygen
theorem sign_eq (cache : Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
end Rev3
end ClaudeWCT.WCT9
