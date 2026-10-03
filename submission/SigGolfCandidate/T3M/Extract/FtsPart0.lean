import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Witness.Shaped
import SigGolfCandidate.T3M.Extract.Basic

namespace SigGolfCandidate.T3M.FtsExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def out (answers : Answers) (input : HashInput) : Digest := (answers (.inl (.inr input))).extractLsb' 0 128
def honL (answers : Answers) (index coord : Nat) (secret : Nat → Digest) : Nat → Nat → Digest
  | 0, node => out answers (ftsLeafInputP index coord node 0 (secret node) 0)
  | level + 1, node => out answers (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
      (honL answers index coord secret level (2 * node)) 0 (honL answers index coord secret level (2 * node + 1)))
def honInputL (answers : Answers) (index coord : Nat) (secret : Nat → Digest) : Nat → Nat → HashInput
  | 0, node => ftsLeafInputP index coord node 0 (secret node) 0
  | level + 1, node => nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
      (honL answers index coord secret level (2 * node)) 0 (honL answers index coord secret level (2 * node + 1))
theorem honL_eq (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (level node : Nat) :
    honL answers index coord secret level node = out answers (honInputL answers index coord secret level node) := by
  cases level <;> rfl
theorem eval_shortHash_out (answers : Answers) (input : HashInput) (h : pad64 input = input) :
    evalWithAnswerFn answers (shortHash input) = out answers input := by
  rw [eval_shortHash, h]; rfl
theorem honL_built (answers : Answers) (index coord : Nat) : ∀ level node, level ≤ 11 → node < 2 ^ (11 - level) →
    honL answers index coord (fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0) level node =
      treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level node := by
  have ht := Correctness.eval_buildFts_correct answers index coord
  intro level
  induction level with
  | zero =>
      intro node _ hn
      rw [ht.2.2.1 node (by simpa using hn), ftsLeaf_eq_shortHash, eval_shortHash_out _ _ (pad64_ftsLeafInputP ..)]
      rfl
  | succ level ih =>
      intro node hl hn
      have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
        rw [← pow_succ']; congr 1; omega
      rw [ht.2.2.2 level (by omega) node hn, nodeHash_eq_shortHash, eval_shortHash_out _ _ (pad64_nodeInputP ..),
        ← ih (2 * node) (by omega) (by omega), ← ih (2 * node + 1) (by omega) (by omega)]
      rfl
def AllHonest (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (qs : List Spec.Domain) : Prop :=
  ∀ q ∈ qs, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ q = .inl (.inr (honInputL answers index coord secret l n))
def TreeHit (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (qs : List Spec.Domain) : Prop :=
  ∃ actual, .inl (.inr actual) ∈ qs ∧
    ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ HashHit answers (honInputL answers index coord secret l n) actual ∧
      Extract.SameHeader actual (honInputL answers index coord secret l n)
theorem hdrBlock_append {a b : HashInput} (c : HashInput) (ha : a.length = 16) (hb : b.length = 16) :
    Extract.hdrBlock (a ++ b ++ c) = b := by
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]
theorem hdrBlock_block4 (a b c d : Digest) : Extract.hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc (bytesLE 16 a ++ bytesLE 16 b), hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _)]
end SigGolfCandidate.T3M.FtsExtract
