import SigGolfCandidate.T3.FullCache.DomainSeparation
import SigGolfCandidate.T3.FullCache.CountedSigner

namespace SiggolfT3Mac4.Source.Payload
open OracleComp OracleSpec
open SigGolfCandidate.T3
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem pure_allowed {α : Type} (value : α) : AllQueriesSatisfy (pure value : M α) NonMac :=
  allQueriesSatisfy_pure _ _

theorem bind_allowed {α β : Type} {program : M α} {next : α → M β}
    (hp : AllQueriesSatisfy program NonMac) (hn : ∀ value, AllQueriesSatisfy (next value) NonMac) :
    AllQueriesSatisfy (program >>= next) NonMac := allQueriesSatisfy_bind hp hn

theorem map_allowed {α β : Type} (f : α → β) {program : M α}
    (hp : AllQueriesSatisfy program NonMac) : AllQueriesSatisfy (f <$> program) NonMac := by
  rw [map_eq_bind_pure_comp]
  exact bind_allowed hp fun _ => pure_allowed _

theorem foldlM_allowed {α β : Type} (items : List β) (f : α → β → M α)
    (h : ∀ a b,AllQueriesSatisfy (f a b) NonMac) (initial : α) :
    AllQueriesSatisfy (items.foldlM f initial) NonMac := by
  induction items generalizing initial with
  | nil => exact pure_allowed _
  | cons a items ih =>
      rw [List.foldlM_cons]
      exact bind_allowed (h initial a) ih

theorem mapM_allowed {α β : Type} (items : List α) (f : α → M β)
    (h : ∀ a,AllQueriesSatisfy (f a) NonMac) : AllQueriesSatisfy (items.mapM f) NonMac := by
  induction items with
  | nil => exact pure_allowed _
  | cons a items ih =>
      rw [List.mapM_cons]
      exact bind_allowed (h a) fun _ => bind_allowed ih fun _ => pure_allowed _

theorem map_allowed_iff {α β : Type} (f : α → β) (program : M α) :
    AllQueriesSatisfy (f <$> program) NonMac ↔ AllQueriesSatisfy program NonMac := by
  induction program using OracleComp.inductionOn with
  | pure value => simp only [map_pure,allQueriesSatisfy_pure]
  | query_bind input next ih =>
      simp only [map_bind,allQueriesSatisfy_query_bind_iff,ih]

theorem publicHash_allowed (input : HashInput) : AllQueriesSatisfy (publicHash input) NonMac :=
  (allQueriesSatisfy_query_iff _ _).mpr trivial

theorem privatePair_allowed (tag lay tree position index : Nat) (htag : tag % 256 ≠ 14) :
    AllQueriesSatisfy (privatePair tag lay tree position index) NonMac := by
  unfold privatePair
  apply bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr
      ⟨non_mac_tweak tag lay tree position index htag 0, non_mac_tweak tag lay tree position index htag 1⟩
  · intro _; exact pure_allowed _

theorem wotsPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 0 lay tree position index) NonMac :=
  privatePair_allowed 0 lay tree position index (by decide)

theorem maskPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 13 lay tree position index) NonMac :=
  privatePair_allowed 13 lay tree position index (by decide)

theorem ftsPair_allowed (lay tree position index : Nat) :
    AllQueriesSatisfy (privatePair 8 lay tree position index) NonMac :=
  privatePair_allowed 8 lay tree position index (by decide)

theorem privateNonce_allowed (message : Message) : AllQueriesSatisfy (privateNonce message) NonMac := by
  unfold privateNonce
  apply bind_allowed
  · exact (allQueriesSatisfy_query_iff _ _).mpr (nonce_coordinate_other message)
  · intro _; exact pure_allowed _

attribute [local aesop safe apply] pure_allowed bind_allowed map_allowed foldlM_allowed mapM_allowed
  publicHash_allowed wotsPair_allowed maskPair_allowed ftsPair_allowed privateNonce_allowed
macro "source_queries" : tactic => `(tactic| aesop (config := { maxRuleApplications := 1000 }))

theorem shortHash_allowed (input : HashInput) : AllQueriesSatisfy (shortHash input) NonMac := by
  unfold shortHash; source_queries
attribute [local aesop safe apply] shortHash_allowed
theorem mask_allowed (level index : Nat) : AllQueriesSatisfy (mask level index) NonMac := by
  unfold mask pairedMask; source_queries
attribute [local aesop safe apply] mask_allowed
theorem chain_allowed (lay : Layer) (tree leaf i start count : Nat) (value : Digest) :
    AllQueriesSatisfy (chain lay tree leaf i start count value) NonMac := by
  unfold chain; source_queries
attribute [local aesop safe apply] chain_allowed
theorem leafHash_allowed (lay : Layer) (tree leaf : Nat) (ends : List Digest) :
    AllQueriesSatisfy (leafHash lay tree leaf ends) NonMac := by
  unfold leafHash; source_queries
attribute [local aesop safe apply] leafHash_allowed
theorem nodeHash_allowed (tag lay tree heap : Nat) (left right : Digest) :
    AllQueriesSatisfy (nodeHash tag lay tree heap left right) NonMac := by
  unfold nodeHash; source_queries
attribute [local aesop safe apply] nodeHash_allowed
theorem buildLeaf_allowed (lay : Layer) (tree leaf : Nat) (digits : List Nat) (signatureOnly : Bool) :
    AllQueriesSatisfy (buildLeaf lay tree leaf digits signatureOnly) NonMac := by
  unfold buildLeaf; source_queries
attribute [local aesop safe apply] buildLeaf_allowed
theorem buildLevel_allowed (tag lay tree h level : Nat) (nodes : List Digest) :
    AllQueriesSatisfy (buildLevel tag lay tree h level nodes) NonMac := by
  unfold buildLevel; source_queries
attribute [local aesop safe apply] buildLevel_allowed
theorem buildLevels_allowed (tag lay tree h : Nat) (leaves : List Digest) :
    AllQueriesSatisfy (buildLevels tag lay tree h leaves) NonMac := by
  unfold buildLevels; source_queries
attribute [local aesop safe apply] buildLevels_allowed
theorem buildTree_allowed (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    AllQueriesSatisfy (buildTree lay tree selected digits) NonMac := by
  unfold buildTree; source_queries
attribute [local aesop safe apply] buildTree_allowed
theorem keygenPayload_allowed : AllQueriesSatisfy keygenPayload NonMac := by
  unfold keygenPayload maskedLevel pairedMask; source_queries

theorem counterSearch_allowed (lay : Layer) (tree leaf : Nat) (message : Digest) (counter fuel : Nat) :
    AllQueriesSatisfy (counterSearch lay tree leaf message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero => unfold counterSearch; source_queries
  | succ fuel ih => unfold counterSearch; source_queries
attribute [local aesop safe apply] counterSearch_allowed
theorem digest_allowed (rho : Digest) (message : Message) (counter : BitVec 32) :
    AllQueriesSatisfy (digest rho message counter) NonMac := by
  unfold digest; source_queries
attribute [local aesop safe apply] digest_allowed
theorem digestSearch_allowed (rho : Digest) (message : Message) (counter fuel : Nat) :
    AllQueriesSatisfy (digestSearch rho message counter fuel) NonMac := by
  induction fuel generalizing counter with
  | zero => unfold digestSearch; source_queries
  | succ fuel ih => unfold digestSearch; source_queries
attribute [local aesop safe apply] digestSearch_allowed
theorem ftsLeaf_allowed (index coord leaf : Nat) (secret : Digest) :
    AllQueriesSatisfy (ftsLeaf index coord leaf secret) NonMac := by
  unfold ftsLeaf; source_queries
attribute [local aesop safe apply] ftsLeaf_allowed
theorem buildFts_allowed (index coord : Nat) : AllQueriesSatisfy (buildFts index coord) NonMac := by
  unfold buildFts; source_queries
attribute [local aesop safe apply] buildFts_allowed
theorem forestPk_allowed (index : Nat) (roots : List Digest) :
    AllQueriesSatisfy (forestPk index roots) NonMac := by
  unfold forestPk; source_queries
attribute [local aesop safe apply] forestPk_allowed
theorem topPath_allowed (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) : AllQueriesSatisfy (topPath cache leaf) NonMac := by
  unfold topPath; source_queries
attribute [local aesop safe apply] topPath_allowed
theorem signTop_allowed (cache : SigGolfCandidate.T3.Cache) (leaf : Nat) (digits : List Nat) :
    AllQueriesSatisfy (signTop cache leaf digits) NonMac := by
  unfold signTop; source_queries
attribute [local aesop safe apply] signTop_allowed
theorem signLayers_allowed (cache : SigGolfCandidate.T3.Cache) (index n : Nat) (message : Digest) :
    AllQueriesSatisfy (signLayers cache index n message) NonMac := by
  induction n generalizing message with
  | zero => unfold signLayers; source_queries
  | succ n ih => unfold signLayers; source_queries
attribute [local aesop safe apply] signLayers_allowed
theorem signPayload_allowed (cache : SigGolfCandidate.T3.Cache) (message : Message) :
    AllQueriesSatisfy (signPayload cache message) NonMac := by
  unfold signPayload; source_queries

end SiggolfT3Mac4.Source.Payload
