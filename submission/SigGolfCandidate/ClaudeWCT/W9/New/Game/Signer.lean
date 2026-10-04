import SigGolfCandidate.ClaudeWCT.WCT9.Limits
import SigGolfCandidate.T3.FullCache.PayloadSeparation
import SigGolfCandidate.T3.FullCache.SourcePrelude

namespace ClaudeWCT.W9.T3.Security
open OracleComp OracleSpec SigGolfCandidate.T3
abbrev Signature : Type := ClaudeWCT.WCT9.Signature
abbrev signPayload : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.signPayload
abbrev sign : SigGolfCandidate.T3.Cache → Message → M (Option Signature) :=
  ClaudeWCT.WCT9.Rev3.sign
theorem sign_eq (cache : SigGolfCandidate.T3.Cache) (message : Message) : sign cache message = (do
    let tag ← privateMac cache.region
    if tag ≠ cache.tag then return none
    signPayload cache message) := rfl
namespace Signer
open ClaudeWCT.WCT9 (Coord Child Rank child rank Opening buildChild buildCoordinate)
open SigGolfCandidate.T3.Security
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
section allowed
variable (P : SigGolfCandidate.T3.Spec.Domain → Prop) (hpublic : ∀ input, P (.inl (.inr input)))
  (hseed : ∀ lay tree position index, P (.inr (.inl (header 8 lay tree position index))))
include hpublic in
theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) P := by
  unfold shortHash publicHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
    fun _ => SourceQueries.pure_allowed P _
include hseed in
theorem seed_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 8 lay tree position index) P := by
  unfold privatePair privateHash
  exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hseed _ _ _ _))
    fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem chain_allowed (index coord selected i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (WCT9.chain index coord selected i start count value) P := by
  unfold WCT9.chain
  exact SourceQueries.foldlM_allowed P _ _ (fun _ _ => shortHash_allowed P hpublic _) _
include hpublic in
theorem leafHash_allowed (index coord selected : Nat) (ends : List Digest) :
    AllQueriesSatisfy (WCT9.leafHash index coord selected ends) P := by
  unfold WCT9.leafHash
  exact shortHash_allowed P hpublic _
include hpublic hseed in
theorem buildChild_allowed (index coord selected : Nat) (word : Rank) :
    AllQueriesSatisfy (buildChild index coord selected word) P := by
  unfold buildChild
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state pair
    apply SourceQueries.bind_allowed P (seed_allowed P hseed _ _ _ _)
    intro seeds
    apply SourceQueries.foldlM_allowed P
    intro state half
    split
    · apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
      intro value
      apply SourceQueries.bind_allowed P (chain_allowed P hpublic _ _ _ _ _ _ _)
      intro _
      exact SourceQueries.pure_allowed P _
    · exact SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (leafHash_allowed P hpublic _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) P := by
  unfold nodeHash
  exact shortHash_allowed P hpublic _
include hpublic in
theorem heapBuild_allowed (index coord : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (WCT9.heapBuild index coord leaves) P := by
  unfold WCT9.heapBuild
  apply SourceQueries.foldlM_allowed P
  intro nodes heap
  exact SourceQueries.bind_allowed P (by unfold WCT9.wctNodeHash; exact nodeHash_allowed P hpublic _ _ _ _ _ _)
    fun _ => SourceQueries.pure_allowed P _
include hpublic hseed in
theorem buildCoordinate_allowed (index : Nat) (coord : Coord) (selected : Child) (word : Rank) :
    AllQueriesSatisfy (buildCoordinate index coord selected word) P := by
  unfold buildCoordinate
  apply SourceQueries.bind_allowed P
  · apply SourceQueries.foldlM_allowed P
    intro state j
    exact SourceQueries.bind_allowed P (buildChild_allowed P hpublic hseed _ _ _ _)
      fun _ => SourceQueries.pure_allowed P _
  · intro state
    exact SourceQueries.bind_allowed P (heapBuild_allowed P hpublic _ _ _)
      fun _ => SourceQueries.pure_allowed P _
include hpublic in
theorem forestPk_allowed (index : Nat) (pairs : List (Digest × Digest)) :
    AllQueriesSatisfy (WCT9.forestPk index pairs) P := by
  unfold WCT9.forestPk
  exact shortHash_allowed P hpublic _
omit hseed in
theorem layerCounterSearch_allowed'
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.layerCounterSearch
      apply SourceQueries.bind_allowed P (henc _ _ _ _ _)
      intro answer
      split
      · exact ih _
      · exact SourceQueries.pure_allowed P _
include hpublic in
theorem layerCounterSearch_allowed (lay : Layer) (tree leaf : Nat) (msg : WCT9.LayerMsg) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.layerCounterSearch lay tree leaf msg counter fuel) P :=
  layerCounterSearch_allowed' P (fun _ _ _ _ _ => shortHash_allowed P hpublic _) lay tree leaf msg counter fuel
omit hseed in
theorem signLayersBC_allowed' (cache : SigGolfCandidate.T3.Cache)
    (henc : ∀ lay tree leaf msg counter, AllQueriesSatisfy (shortHash (WCT9.layerEncodingInput lay tree leaf msg counter)) P)
    (hbuild : ∀ lay tree leaf digits, AllQueriesSatisfy (buildTree lay tree leaf digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P := by
  induction n generalizing msg with
  | zero => exact SourceQueries.pure_allowed P _
  | succ n ih =>
      unfold WCT9.signLayersBC
      apply SourceQueries.bind_allowed P (layerCounterSearch_allowed' P henc _ _ _ _ _ _)
      intro found
      split
      · split
        · exact SourceQueries.bind_allowed P (htop _ _) fun _ => SourceQueries.pure_allowed P _
        · apply SourceQueries.bind_allowed P (hbuild _ _ _ _)
          intro built
          apply SourceQueries.bind_allowed P (ih _)
          intro previous
          split
          · exact SourceQueries.pure_allowed P _
          · exact SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
include hpublic in
theorem signLayersBC_allowed (cache : SigGolfCandidate.T3.Cache)
    (hbuild : ∀ lay tree leaf digits, AllQueriesSatisfy (buildTree lay tree leaf digits) P)
    (htop : ∀ leaf digits, AllQueriesSatisfy (signTop cache leaf digits) P) (index n : Nat) (msg : WCT9.LayerMsg) :
    AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P :=
  signLayersBC_allowed' P cache (fun _ _ _ _ _ => shortHash_allowed P hpublic _) hbuild htop index n msg
include hpublic in
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (WCT9.digestSearch rho message counter fuel) P := by
  induction fuel generalizing counter with
  | zero => exact SourceQueries.pure_allowed P _
  | succ fuel ih =>
      unfold WCT9.digestSearch digest publicHash
      apply SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr (hpublic _))
      intro output
      split
      · exact SourceQueries.pure_allowed P _
      · exact ih _
include hpublic hseed in
theorem signPayloadWith_allowed (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hnonce : P (.inr (.inr (.inl message))))
    (hlayers : ∀ index n msg, AllQueriesSatisfy (WCT9.signLayersBC cache index n msg) P) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) P := by
  unfold WCT9.signPayloadWith privateNonce privateHash
  apply SourceQueries.bind_allowed P
  · exact SourceQueries.bind_allowed P ((allQueriesSatisfy_query_iff _ _).mpr hnonce)
      fun _ => SourceQueries.pure_allowed P _
  intro rho
  apply SourceQueries.bind_allowed P (digestSearch_allowed P hpublic _ _ _ _)
  intro found
  split
  · apply SourceQueries.bind_allowed P
    · apply SourceQueries.foldlM_allowed P
      intro state coord
      exact SourceQueries.bind_allowed P (buildCoordinate_allowed P hpublic hseed _ _ _ _)
        fun _ => SourceQueries.pure_allowed P _
    · intro state
      apply SourceQueries.bind_allowed P (forestPk_allowed P hpublic _ _)
      intro root
      apply SourceQueries.bind_allowed P (hlayers _ _ _)
      intro layers
      split
      · exact SourceQueries.pure_allowed P _
      · exact SourceQueries.pure_allowed P _
  · exact SourceQueries.pure_allowed P _
end allowed
theorem signPayloadWith_nonMac (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (WCT9.signPayloadWith limit cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_allowed _ (fun _ => trivial)
    (fun lay tree position index => ⟨SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 0,
      SiggolfT3Mac4.Source.non_mac_tweak 8 lay tree position index (by decide) 1⟩)
    limit cache message (SiggolfT3Mac4.Source.nonce_coordinate_other message)
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      SiggolfT3Mac4.Source.Payload.buildTree_allowed (SiggolfT3Mac4.Source.Payload.signTop_allowed cache) index n msg)
theorem signPayload_nonMac (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) SiggolfT3Mac4.Source.NonMac :=
  signPayloadWith_nonMac _ cache message
theorem signPayloadWith_hashOnly (limit : Nat) (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => trivial) (fun _ _ _ _ => trivial) limit cache message trivial
    (fun index n msg => signLayersBC_allowed _ (fun _ => trivial) cache
      (SourceQueries.buildTree_allowed SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial) (fun _ => trivial))
      (SourceQueries.signTop_allowed SourceReplay.IsHash (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) cache)
      index n msg)
theorem signPayload_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (signPayload cache message) :=
  signPayloadWith_hashOnly _ cache message
theorem signPayloadWith_avoids (protectedMessage : Message) (limit : Nat) (cache : SigGolfCandidate.T3.Cache)
    (message : Message) (hne : message ≠ protectedMessage) :
    NonceFreshness.Avoids protectedMessage (WCT9.signPayloadWith limit cache message) :=
  signPayloadWith_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery])
    (fun _ _ _ _ => by simp [NonceFreshness.nonceQuery]) limit cache message
    (by simpa [NonceFreshness.nonceQuery] using hne)
    (fun index n msg => signLayersBC_allowed _ (fun _ => by simp [NonceFreshness.nonceQuery]) cache
      (NonceFreshness.avoids_buildTree protectedMessage) (NonceFreshness.avoids_signTop protectedMessage cache)
      index n msg)
theorem signPayload_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (signPayload cache message) :=
  signPayloadWith_avoids protectedMessage _ cache message hne
theorem sign_hashOnly (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    SourceReplay.HashOnly (sign cache message) := by
  rw [sign_eq]
  apply SourceQueries.bind_allowed SourceReplay.IsHash
    (SourceQueries.privateMac_allowed SourceReplay.IsHash (fun _ => trivial) _)
  intro tag
  split_ifs
  · exact SourceQueries.pure_allowed _ _
  · exact signPayload_hashOnly cache message
theorem sign_avoids (protectedMessage : Message) (cache : SigGolfCandidate.T3.Cache) (message : Message)
    (hne : message ≠ protectedMessage) : NonceFreshness.Avoids protectedMessage (sign cache message) := by
  rw [sign_eq]
  apply NonceFreshness.avoids_bind protectedMessage (NonceFreshness.avoids_privateMac protectedMessage _)
  intro tag
  split_ifs
  · exact NonceFreshness.avoids_pure _ _
  · exact signPayload_avoids protectedMessage cache message hne
end Signer
end ClaudeWCT.W9.T3.Security
