import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.T3M.Witness.Queries

namespace ClaudeWCT.W9.T3M
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M (PubGood isHash isPublic allQ_pure allQ_bind allQ_map allQ_ite allQ_foldlM allQ_mapM
  allQ_mono pubGood_shortHash pubGood_publicHash pubGood_nodeHashP pubGood_nodeHash pubGood_digest
  pubGood_layersP pubGood_expandLayers layersP)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
theorem pubGood_wctChainP (index coord child t start count : Nat) (p0 p1 v : Digest) :
    AllQueriesSatisfy (wctChainP index coord child t start count p0 p1 v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [wctChainInputP, bytesLE_length])) _
theorem pubGood_chain (index coord child t start count : Nat) (v : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord child t start count v) PubGood :=
  allQ_foldlM _ _ (fun _ _ => pubGood_shortHash _ (by simp [WCT9.chainInput, bytesLE_length, zero16])) _
theorem pubGood_leafHash (index coord child : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord child ends) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])
theorem pubGood_forestPk (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (WCT9.forestPk index roots) PubGood :=
  pubGood_shortHash _ (by simp [bytesLE_length])
theorem pubGood_wctCoordP (w : WBytes) (index : Nat) (coord : WCT9.Coord) (child : WCT9.Child)
    (word : WCT9.Rank) : AllQueriesSatisfy (wctCoordP w index coord child word) PubGood := by
  unfold wctCoordP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_wctChainP _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ => allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashP _ _ _ _ _ _ _) _
theorem pubGood_wctStep (w : WBytes) (N : HashOutput) (st : Option (List Digest)) (coord : WCT9.Coord) :
    AllQueriesSatisfy (wctStep w N st coord) PubGood := by
  unfold wctStep
  rcases st with _ | roots
  · exact allQ_pure _
  · exact allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_wctCoordP _ _ _ _ _) fun _ => allQ_pure _)
theorem pubGood_wctP (w : WBytes) (N : HashOutput) : AllQueriesSatisfy (wctP w N) PubGood := by
  unfold wctP
  refine allQ_bind (allQ_foldlM _ _ (pubGood_wctStep w N) _) fun r => ?_
  rcases r with _ | roots
  · exact allQ_pure _
  · exact allQ_map _ (pubGood_forestPk _ _)
theorem pubGood_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) PubGood := by
  rw [verifyP_eq_tail]
  refine allQ_bind ?_ fun r => ?_
  · unfold digestP; exact allQ_ite _ (allQ_pure _) (allQ_map _ (pubGood_digest _ _ _))
  · rcases r with _ | N
    · exact allQ_pure _
    unfold verifyTailP
    refine allQ_ite _ (allQ_pure _) (allQ_bind (pubGood_wctP _ _) fun r => ?_)
    rcases r with _ | root
    · exact allQ_pure _
    refine allQ_bind (pubGood_layersP _ _ _ _) fun r => ?_
    rcases r with _ | root <;> exact allQ_pure _
theorem pubGood_digestSearch (rho : Digest) (m : Message) : ∀ fuel counter,
    AllQueriesSatisfy (WCT9.digestSearch rho m counter fuel) PubGood := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact allQ_pure _
  | succ fuel ih =>
      intro counter
      unfold WCT9.digestSearch
      exact allQ_bind (pubGood_digest _ _ _) fun _ => allQ_ite _ (allQ_pure _) (ih _)
theorem pubGood_recoverCoordinate (sig : WCT9.Signature) (index : Nat) (output : HashOutput) (coord : WCT9.Coord) :
    AllQueriesSatisfy (WCT9.recoverCoordinate sig index output coord) PubGood := by
  unfold WCT9.recoverCoordinate
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_chain _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ => allQ_foldlM _ _ (fun _ _ => pubGood_nodeHash _ _ _ _ _ _) _
theorem pubGood_recoverFts (sig : WCT9.Signature) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (WCT9.recoverFts sig index output) PubGood := by
  unfold WCT9.recoverFts
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_recoverCoordinate _ _ _ _) fun _ => pubGood_forestPk _ _
theorem pubGood_recoverCoordinateP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput)
    (coord : WCT9.Coord) : AllQueriesSatisfy (recoverCoordinateP sig pads index output coord) PubGood := by
  unfold recoverCoordinateP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_wctChainP _ _ _ _ _ _ _ _ _) fun _ =>
    allQ_bind (pubGood_leafHash _ _ _ _) fun _ => allQ_foldlM _ _ (fun _ _ => pubGood_nodeHashP _ _ _ _ _ _ _) _
theorem pubGood_recoverFtsP (sig : WCT9.Signature) (pads : Pads) (index : Nat) (output : HashOutput) :
    AllQueriesSatisfy (recoverFtsP sig pads index output) PubGood := by
  unfold recoverFtsP
  exact allQ_bind (allQ_mapM _ _ fun _ => pubGood_recoverCoordinateP _ _ _ _ _) fun _ => pubGood_forestPk _ _
theorem pubGood_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) PubGood := by
  unfold expandN
  refine allQ_bind (pubGood_digestSearch _ _ _ _) fun r => ?_
  rcases r with _ | ⟨c, N⟩
  · exact allQ_pure _
  refine allQ_bind (pubGood_recoverFts _ _ _) fun root => ?_
  refine allQ_bind (pubGood_expandLayers _ _ _ _) fun r => ?_
  rcases r with _ | ⟨root', cs⟩
  · exact allQ_pure _
  exact allQ_ite _ (allQ_pure _) (allQ_pure _)
theorem pubGood_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) PubGood := allQ_map _ (pubGood_expandN m pk σ)
theorem hashOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isHash :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.hashGood.1
theorem hashOnly_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) isHash :=
  allQ_mono (pubGood_expandN m pk σ) fun _ h => h.hashGood.1
theorem hashOnly_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) isHash :=
  allQ_mono (pubGood_expandB m pk σ) fun _ h => h.hashGood.1
theorem publicOnly_verifyP (m : Message) (pk : Digest) (w : WBytes) : AllQueriesSatisfy (verifyP m pk w) isPublic :=
  allQ_mono (pubGood_verifyP m pk w) fun _ h => h.1
theorem publicOnly_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) isPublic := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.1
theorem publicOnly_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) isPublic := allQ_mono (pubGood_expandB m pk σ) fun _ h => h.1
theorem goodQ_verifyP (m : Message) (pk : Digest) (w : WBytes) :
    AllQueriesSatisfy (verifyP m pk w) Cost.GoodQuery := allQ_mono (pubGood_verifyP m pk w) fun _ h => h.2
theorem goodQ_expandN (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandN m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandN m pk σ) fun _ h => h.2
theorem goodQ_expandB (m : Message) (pk : Digest) (σ : WCT9.Signature) :
    AllQueriesSatisfy (expandB m pk σ) Cost.GoodQuery := allQ_mono (pubGood_expandB m pk σ) fun _ h => h.2
theorem hashOnly_honestProgramB (hk : AllQueriesSatisfy WCT9.Rev3.keygen isHash)
    (hs : ∀ c m, AllQueriesSatisfy (WCT9.Rev3.sign c m) isHash) (m : Message) :
    AllQueriesSatisfy (honestProgramB m) isHash := by
  unfold honestProgramB
  apply allQ_bind hk
  intro keys
  apply allQ_bind (hs _ _)
  intro sig
  rcases sig with _ | sig
  · exact allQ_pure _
  apply allQ_bind (hashOnly_expandB _ _ _)
  intro wb
  rcases wb with _ | wb
  · exact allQ_pure _
  exact hashOnly_verifyP _ _ _
end ClaudeWCT.W9.T3M
