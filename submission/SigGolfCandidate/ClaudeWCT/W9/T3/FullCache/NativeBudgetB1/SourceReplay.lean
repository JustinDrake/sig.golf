import SigGolfCandidate.ClaudeWCT.W9.T3.FullCache.NativeBudgetB1.Budgets
import SigGolfCandidate.ClaudeWCT.WCT9.Forest

namespace ClaudeWCT.W9.T3.SourceReplay
open OracleComp OracleSpec
open SigGolfCandidate.T3 hiding Signature Witness sign expand verify signPayload digestSearch admissible
open SigGolfCandidate.T3.SourceReplay (HashOnly hashOnly_pure hashOnly_bind hashOnly_map hashOnly_mapM
  hashOnly_foldlM hashOnly_shortHash hashOnly_privatePair hashOnly_nodeHash fixedAnswers fixed_replay)
open ClaudeWCT.WCT9 (Signature Witness)
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
@[aesop safe apply] theorem hashOnly_chain (index coord selected i start count : Nat) (value : Digest) :
    HashOnly (ClaudeWCT.WCT9.chain index coord selected i start count value) := by
  unfold ClaudeWCT.WCT9.chain; hashes
@[aesop safe apply] theorem hashOnly_leafHash (index coord selected : Nat) (ends : List Digest) :
    HashOnly (ClaudeWCT.WCT9.leafHash index coord selected ends) := by
  unfold ClaudeWCT.WCT9.leafHash; hashes
@[aesop safe apply] theorem hashOnly_forestPk (index : Nat) (roots : List Digest) :
    HashOnly (ClaudeWCT.WCT9.forestPk index roots) := by
  unfold ClaudeWCT.WCT9.forestPk; hashes
@[aesop safe apply] theorem hashOnly_buildChild (index coord selected : Nat) (word : ClaudeWCT.WCT9.Rank) :
    HashOnly (ClaudeWCT.WCT9.buildChild index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildChild; hashes
@[aesop safe apply] theorem hashOnly_buildCoordinate (index : Nat) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    HashOnly (ClaudeWCT.WCT9.buildCoordinate index coord selected word) := by
  unfold ClaudeWCT.WCT9.buildCoordinate
  refine hashOnly_bind (hashOnly_foldlM _ _ (fun state j => ?_) _) fun state => ?_
  · refine hashOnly_bind (hashOnly_buildChild index coord.val j word) fun r => ?_
    rcases r with ⟨root, values⟩
    exact hashOnly_pure _
  · refine hashOnly_bind (hashOnly_foldlM _ _ (fun nodes heap => ?_) _) fun nodes => hashOnly_pure _
    exact hashOnly_bind (hashOnly_nodeHash 11 coord.val index heap _ _) fun _ => hashOnly_pure _
@[aesop safe apply] theorem hashOnly_digestSearch (rho : Digest) (message : Message) (counter fuel : Nat) :
    HashOnly (ClaudeWCT.WCT9.digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold ClaudeWCT.WCT9.digestSearch; hashes
  | succ fuel ih => unfold ClaudeWCT.WCT9.digestSearch; hashes
@[aesop safe apply] theorem hashOnly_openingStep (index : Nat) (output : HashOutput)
    (state : List ClaudeWCT.WCT9.Opening × List Digest) (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.openingStep index output state coord) := by
  unfold ClaudeWCT.WCT9.openingStep; hashes
@[aesop safe apply] theorem hashOnly_forestRows (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.forestRows index output) := by
  unfold ClaudeWCT.WCT9.forestRows; hashes
@[aesop safe apply] theorem hashOnly_signForest (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.signForest index output) := by
  unfold ClaudeWCT.WCT9.signForest; hashes
@[aesop safe apply] theorem hashOnly_recoverCoordinate (sig : Signature) (index : Nat) (output : HashOutput)
    (coord : ClaudeWCT.WCT9.Coord) :
    HashOnly (ClaudeWCT.WCT9.recoverCoordinate sig index output coord) := by
  unfold ClaudeWCT.WCT9.recoverCoordinate; hashes
@[aesop safe apply] theorem hashOnly_recoverFts (sig : Signature) (index : Nat) (output : HashOutput) :
    HashOnly (ClaudeWCT.WCT9.recoverFts sig index output) := by
  unfold ClaudeWCT.WCT9.recoverFts; hashes
@[aesop safe apply] theorem hashOnly_signPayloadWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signPayloadWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signPayloadWith; hashes
@[aesop safe apply] theorem hashOnly_signWith (limit : Nat) (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.signWith limit cache message) := by
  unfold ClaudeWCT.WCT9.signWith; hashes
@[aesop safe apply] theorem hashOnly_expandWith (limit : Nat) (message : Message) (pk : Digest)
    (sig : Signature) : HashOnly (ClaudeWCT.WCT9.expandWith limit message pk sig) := by
  unfold ClaudeWCT.WCT9.expandWith; hashes
@[aesop safe apply] theorem hashOnly_verifyWith (limit : Nat) (message : Message) (pk : Digest)
    (w : Witness) : HashOnly (ClaudeWCT.WCT9.verifyWith limit message pk w) := by
  unfold ClaudeWCT.WCT9.verifyWith; hashes
@[aesop safe apply] theorem hashOnly_signPayload (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.signPayload cache message) :=
  hashOnly_signPayloadWith _ cache message
@[aesop safe apply] theorem hashOnly_sign (cache : Cache) (message : Message) :
    HashOnly (ClaudeWCT.WCT9.Rev3.sign cache message) :=
  hashOnly_signWith _ cache message
@[aesop safe apply] theorem hashOnly_expand (message : Message) (pk : Digest) (sig : Signature) :
    HashOnly (ClaudeWCT.WCT9.Rev3.expand message pk sig) :=
  hashOnly_expandWith _ message pk sig
@[aesop safe apply] theorem hashOnly_verify (message : Message) (pk : Digest) (w : Witness) :
    HashOnly (ClaudeWCT.WCT9.Rev3.verify message pk w) :=
  hashOnly_verifyWith _ message pk w
theorem sign_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (cache : Cache) (message : Message) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.sign cache message)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.sign cache message)) :=
  fixed_replay secret hash _ (hashOnly_sign cache message)
theorem expand_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (sig : Signature) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.expand message pk sig)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.expand message pk sig)) :=
  fixed_replay secret hash _ (hashOnly_expand message pk sig)
theorem verify_replay (secret : BitVec 256) (hash : QueryImpl SphincsSecurity.HashSpec Id)
    (message : Message) (pk : Digest) (w : Witness) :
    simulateQ (unifFwdAnswerImpl hash) (realize secret (ClaudeWCT.WCT9.Rev3.verify message pk w)) =
      pure (evalWithAnswerFn (fixedAnswers secret hash) (ClaudeWCT.WCT9.Rev3.verify message pk w)) :=
  fixed_replay secret hash _ (hashOnly_verify message pk w)
end ClaudeWCT.W9.T3.SourceReplay
