import SigGolfCandidate.T3.FullCache.NativeMac
namespace SigGolfCandidate.T3.Security.FullGame
open OracleComp OracleSpec
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits
set_option backward.isDefEq.respectTransparency false

abbrev NonMac {α : Type} (program : M α) := AllQueriesSatisfy program MacGame.NonMac

theorem shortHash_nonMac (input : HashInput) : NonMac (shortHash input) :=
  SourceQueries.shortHash_allowed MacGame.NonMac (fun _ => trivial) input

theorem chain_nonMac (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    NonMac (chain lay tree leaf i start count value) := by
  unfold chain
  exact SourceQueries.foldlM_allowed _ _ _ (fun _ _ => shortHash_nonMac _) _

theorem leafHash_nonMac (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    NonMac (leafHash lay tree leaf ends) := shortHash_nonMac _

theorem nodeHash_nonMac (tag lay tree heap : Nat) (left right : Digest) :
    NonMac (nodeHash tag lay tree heap left right) := shortHash_nonMac _

theorem ftsLeaf_nonMac (index coord leaf : Nat) (value : Digest) :
    NonMac (ftsLeaf index coord leaf value) := shortHash_nonMac _

theorem forestPk_nonMac (index : Nat) (roots : List Digest) :
    NonMac (forestPk index roots) := shortHash_nonMac _

theorem digest_nonMac (rho : Digest) (message : Message) (counter : BitVec 32) :
    NonMac (digest rho message counter) :=
  SourceQueries.publicHash_allowed _ (fun _ => trivial) _

attribute [local aesop safe apply] SourceQueries.pure_allowed SourceQueries.bind_allowed
  SourceQueries.map_allowed SourceQueries.foldlM_allowed SourceQueries.mapM_allowed
  shortHash_nonMac chain_nonMac leafHash_nonMac nodeHash_nonMac ftsLeaf_nonMac
  forestPk_nonMac digest_nonMac
macro "public_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

theorem counterSearch_nonMac (lay : Layer) (tree leaf : Nat) (message : Digest × BitVec 96 × Digest)
    (counter fuel : Nat) : NonMac (counterSearch lay tree leaf message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; public_queries
  | succ fuel ih => unfold counterSearch; public_queries

theorem digestSearch_nonMac (rho : Digest) (message : Message) (counter fuel : Nat) :
    NonMac (digestSearch rho message counter fuel) := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; public_queries
  | succ fuel ih => unfold digestSearch; public_queries
end SigGolfCandidate.T3.Security.FullGame
