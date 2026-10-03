import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Eval

section


namespace SphincsSecurity.Concrete
variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]
theorem chainWalk_add (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b) value
      = (do
          let mid ← chainWalk (m := m) parameter lay tree leaf chainIdx start a value
          chainWalk parameter lay tree leaf chainIdx (start + a) b mid) := by
  induction b with
  | zero => simp [chainWalk]
  | succ b ih =>
      show chainWalk (m := m) parameter lay tree leaf chainIdx start (a + b + 1) value = _
      simp only [chainWalk, ih, bind_assoc, Nat.add_assoc]
end SphincsSecurity.Concrete
end

section



namespace SphincsSecurity.Concrete
open OracleComp
variable {α : Type} (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (lay : Layer)
  (tree : TreeIndex) (leaf : LeafIndex)
theorem eval_chainWalk_add (chainIdx : ChainIndex) (start a b : Nat) (value : Digest) :
    evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start (a + b) value)
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx (start + a) b
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start a value))) := by
  rw [chainWalk_add, evalWithAnswerFn_bind]
theorem eval_recoverChain (chainIdx : ChainIndex) (digit : Digit) (value : Digest) :
    evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
        (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
  have hdigit : digit.val + (chainLength - 1 - digit.val) = chainLength - 1 := by
    have hlt := digit.isLt
    simp only [chainLength, winternitzBits] at hlt
    simp only [chainLength, winternitzBits]
    omega
  calc evalWithAnswerFn f (recoverChain parameter lay tree leaf chainIdx digit
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value)))
      = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx
          (0 + digit.val) (chainLength - 1 - digit.val)
          (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 digit.val value))) := by
        rw [recoverChain, Nat.zero_add]
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0
          (digit.val + (chainLength - 1 - digit.val)) value) := (eval_chainWalk_add ..).symm
    _ = evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) value) := by
        rw [hdigit]
theorem eval_oneTimePublicKey (secret : ChainIndex → Digest) :
    evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret)
      = fun chainIdx => evalWithAnswerFn f
          (chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)) := by
  simp [oneTimePublicKey]
end SphincsSecurity.Concrete
end
