import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement

namespace SphincsSecurity.Concrete
open OracleComp
variable {α : Type} (f : QueryImpl HashSpec Id)
@[simp]
theorem evalWithAnswerFn_sequenceFin {n : Nat} (computation : Fin n → OracleComp HashSpec α) :
    evalWithAnswerFn f (sequenceFin computation) = fun index => evalWithAnswerFn f (computation index) := by
  induction n with
  | zero => funext index; exact index.elim0
  | succ n ih =>
      funext index
      simp only [sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure, ih]
      cases index using Fin.cases <;> rfl
end SphincsSecurity.Concrete
