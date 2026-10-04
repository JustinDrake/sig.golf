import SigGolfCandidate.ClaudeWCT.WCT9.Queries
import SigGolfCandidate.T3.Secc.WotsMaskBase
import SigGolfCandidate.T3.Secc.WotsEncodingCongr
import SigGolfCandidate.T3.Secc.WotsTransportShort
import SigGolfCandidate.T3.Secc.SeccSufRoute
import SigGolfCandidate.T3.Secc.WotsStructuralHonest

namespace ClaudeWCT.WCT9.Wots
open OracleComp OracleSpec SigGolfCandidate.T3 SigGolfCandidate.T3.Correctness SigGolfCandidate.T3.Cost
open SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem queried_query (A : Answers) (q : Query) :
    SourceReplay.queried A (liftM (SigGolfCandidate.T3.Spec.query q) : M (SigGolfCandidate.T3.Spec.Range q)) = [q] := by
  have := SourceReplay.queried_query_bind A q (fun x => (pure x : M _))
  simpa only [bind_pure, SourceReplay.queried_pure] using this
theorem respects_query {S : Query → Prop} {q : Query} (hq : S q) :
    Mask.Respects S (liftM (SigGolfCandidate.T3.Spec.query q) : M (SigGolfCandidate.T3.Spec.Range q)) := by
  intro T T' hT
  refine ⟨?_, by rw [queried_query, queried_query]⟩
  rw [show evalWithAnswerFn T (liftM (SigGolfCandidate.T3.Spec.query q)) = T q from simulateQ_spec_query T q,
    show evalWithAnswerFn T' (liftM (SigGolfCandidate.T3.Spec.query q)) = T' q from simulateQ_spec_query T' q]
  exact hT q hq
theorem respects_of_allQueriesSatisfy {S : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p S) : Mask.Respects S p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Mask.Respects.pure' a
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact Mask.Respects.bind (respects_query hq) fun u => ih u (hf u)
theorem shortRespects_of_allQueriesSatisfy {α : Type} {p : M α}
    (h : AllQueriesSatisfy p Ref.ShortQuery) : Ref.ShortRespects p := fun A T hAT =>
  (respects_of_allQueriesSatisfy h A T hAT).1
theorem queriesSat_of_allQueriesSatisfy {Q : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p Q) (T : Answers) : Structural.QueriesSat T Q p := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Structural.QueriesSat.pure' a
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact Structural.QueriesSat.bind (Structural.QueriesSat.query hq) (ih _ (hf _))
theorem allQueriesSatisfy_mono {P Q : Query → Prop} {α : Type} {p : M α}
    (h : AllQueriesSatisfy p P) (hPQ : ∀ q, P q → Q q) : AllQueriesSatisfy p Q := by
  induction p using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind q f ih =>
      obtain ⟨hq, hf⟩ := (allQueriesSatisfy_query_bind_iff _ _ _).mp h
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨hPQ _ hq, fun u => ih u (hf u)⟩
theorem tag_mod {tag : Nat} (h : tag = 3 ∨ tag = 6 ∨ tag = 15) :
    tag % 256 ≠ 0 ∧ tag % 256 ≠ 1 ∧ tag % 256 ≠ 4 ∧ tag % 256 ≠ 12 := by
  rcases h with rfl | rfl | rfl <;> decide
theorem tag_mod' {tag lay : Nat} (h : (tag = 3 ∧ 4 ≤ lay ∧ lay < 13) ∨ tag = 6 ∨ tag = 15) :
    tag % 256 ≠ 0 ∧ tag % 256 ≠ 1 ∧ tag % 256 ≠ 4 ∧ tag % 256 ≠ 12 :=
  tag_mod (by rcases h with ⟨rfl, -⟩ | h | h <;> simp_all)
theorem ftsChainHeader_ne_wots (index coord selected t step : Nat) :
    ∀ (l : Layer) tr leaf i st, ftsChainHeader index coord selected t step ≠ chainHeader l tr leaf i st :=
  fun l tr leaf i st => ftsChainHeaderP_ne_chainHeader _ _ _ _ _ 0 l tr leaf i st
theorem ftsChainHeader_ne_header' (index coord selected t step : Nat) :
    ∀ l tr p ix, ftsChainHeader index coord selected t step ≠ header 4 l tr p ix :=
  fun l tr p ix => ftsChainHeaderP_ne_header _ _ _ _ _ 0 4 l tr p ix
theorem hdrTag_ftsChain {input : HashInput} {index coord selected t step : Nat}
    (h : SigGolfCandidate.T3M.Extract.hdrBlock input = bytesLE 16 (ftsChainHeader index coord selected t step)) :
    Security.BPB.hdrTag input = 1 := by
  unfold Security.BPB.hdrTag
  rw [h, bytesLE16_first_toNat, show (ftsChainHeader index coord selected t step).toNat % 256 = 128 + 4 * (t % 8)
    from ftsChainHeaderP_firstByte _ _ _ _ _ 0, if_pos (by omega)]
theorem ftsQuery_untouched {index : Nat} (a : ChainAddr) {q : Query} (h : FtsQuery index q) :
    Mask.Untouched a q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨tag, lay, position, idx, htag, hblock⟩
    · exact Mask.untouched_of_hdr a input _ hblock (ftsChainHeader_ne_wots _ _ _ _ _)
    · exact Mask.untouched_of_hdr a input _ hblock
        (fun _ _ _ _ _ => Ne.symm (chainHeader_ne_header _ _ _ _ _ _ _ _ _ _))
  · obtain ⟨coord, selected, pair, -, -, -, rfl⟩ := (show FtsSeed index tweak from h)
    exact Mask.untouched_privatePair a (by decide) _ _ _ _
  · exact h.elim
theorem ftsQuery_nonEnc {index : Nat} {q : Query} (h : FtsQuery index q) : Enc.NonEnc q := by
  rcases q with (coin | input) | (tweak | other)
  · exact h.elim
  · rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨tag, lay, position, idx, htag, hblock⟩
    · exact Enc.nonEnc_of_hdr input _ hblock (ftsChainHeader_ne_header' _ _ _ _ _)
    · exact Enc.nonEnc_of_hdr input _ hblock (Enc.tag_ne_four (tag_mod' htag).2.2.1 _ _ _ _)
  · trivial
  · trivial
theorem ftsQuery_short {index : Nat} {q : Query} (h : FtsQuery index q) : Ref.ShortQuery q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · have := FtsInput.length_le (show FtsInput index input from h)
    show input.length ≤ SeccLaw.maxInputLength
    unfold SeccLaw.maxInputLength
    omega
  · trivial
  · trivial
theorem ftsQuery_notDigest {index : Nat} {q : Query} (h : FtsQuery index q) : BPB.NotDigestQ q := by
  rcases q with (coin | input) | (tweak | other)
  · trivial
  · show BPB.hdrTag input ≠ 12
    rcases FtsInput.hdrBlock (show FtsInput index input from h) with
      ⟨coord, selected, t, step, hblock⟩ | ⟨tag, lay, position, idx, htag, hblock⟩
    · rw [hdrTag_ftsChain hblock]; decide
    · rw [BPB.hdrTag_eq hblock]
      exact (tag_mod' htag).2.2.2
  · trivial
  · trivial
namespace Mask
variable (a : ChainAddr) (index : Nat)
theorem respects_chain (coord selected t start count : Nat) (value : Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  refine Wots.Mask.Respects.foldlM _ _ (fun step _ v => Wots.Mask.Respects.shortHash _ ?_) _
  unfold chainInput
  rw [List.append_assoc (zero16 ++ _)]
  exact Wots.Mask.untouched_of_hdr a _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [zero16]))
    (ftsChainHeader_ne_wots _ _ _ _ _)
theorem respects_leafHash (coord selected : Nat) (ends : List Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  rw [wctHeader_eq_header _ _ _ _ _ (by decide)]
  exact Wots.Mask.Respects.shortHash _ (Wots.Mask.untouched_prefixed a _ _ (by decide) _ _ _ _)
theorem respects_forestPk (pairs : List (Digest × Digest)) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact Wots.Mask.Respects.shortHash _ (Wots.Mask.untouched_prefixed a _ _ (by decide) _ _ _ _)
theorem respects_wctNodeHash (coord heap : Nat) (left right : Digest) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (WCT9.wctNodeHash coord index heap left right) := by
  unfold WCT9.wctNodeHash
  exact Wots.Mask.respects_nodeHash a 3 _ _ _ _ _ (by decide)
theorem respects_buildChild (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (buildChild index coord selected word) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildChild_queries index coord selected word hcoord hsel)
    fun _ => ftsQuery_untouched a)
theorem respects_buildCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (buildCoordinate index coord selected word) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildCoordinate_queries index coord selected word)
    fun _ => ftsQuery_untouched a)
theorem respects_forestRows (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (forestRows index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output)
    fun _ => ftsQuery_untouched a)
theorem respects_signForest (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (signForest index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output)
    fun _ => ftsQuery_untouched a)
theorem respects_recoverCoordinate (sig : Signature) (output : HashOutput) (coord : Coord) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (recoverCoordinate sig index output coord) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverCoordinate_queries index sig output coord)
    fun _ => ftsQuery_untouched a)
theorem respects_recoverFts (sig : Signature) (output : HashOutput) :
    Wots.Mask.Respects (Wots.Mask.Untouched a) (recoverFts sig index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_untouched a)
end Mask
section Programs
variable (index : Nat)
namespace Enc
theorem respects_chain (coord selected t start count : Nat) (value : Digest) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  refine Wots.Mask.Respects.foldlM _ _ (fun step _ v => Wots.Mask.Respects.shortHash _ ?_) _
  unfold chainInput
  rw [List.append_assoc (zero16 ++ _)]
  exact Wots.Enc.nonEnc_of_hdr _ _ (hdrBlock_pad64_prefix _ _ _ (by simp [zero16]))
    (ftsChainHeader_ne_header' _ _ _ _ _)
theorem respects_leafHash (coord selected : Nat) (ends : List Digest) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  rw [wctHeader_eq_header _ _ _ _ _ (by decide)]
  exact Wots.Mask.Respects.shortHash _ (Wots.Enc.nonEnc_prefixed _ _ (by decide) _ _ _ _)
theorem respects_forestPk (pairs : List (Digest × Digest)) :
    Wots.Mask.Respects Wots.Enc.NonEnc (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk forestInput
  rw [show zero16 = bytesLE 16 (0 : Digest) by decide]
  exact Wots.Mask.Respects.shortHash _ (Wots.Enc.nonEnc_prefixed _ _ (by decide) _ _ _ _)
theorem respects_buildChild (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    Wots.Mask.Respects Wots.Enc.NonEnc (buildChild index coord selected word) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildChild_queries index coord selected word hcoord hsel)
    fun _ => ftsQuery_nonEnc)
theorem respects_buildCoordinate (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Mask.Respects Wots.Enc.NonEnc (buildCoordinate index coord selected word) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (buildCoordinate_queries index coord selected word)
    fun _ => ftsQuery_nonEnc)
theorem respects_forestRows (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (forestRows index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output) fun _ => ftsQuery_nonEnc)
theorem respects_signForest (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (signForest index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output) fun _ => ftsQuery_nonEnc)
theorem respects_recoverFts (sig : Signature) (output : HashOutput) :
    Wots.Mask.Respects Wots.Enc.NonEnc (recoverFts sig index output) :=
  respects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_nonEnc)
end Enc
namespace Ref
theorem chain_respects (coord selected t start count : Nat) (value : Digest) :
    Wots.Ref.ShortRespects (WCT9.chain index coord selected t start count value) := by
  unfold WCT9.chain
  exact Wots.Ref.ShortRespects.foldlM _ _ (fun step _ v => Wots.Ref.ShortRespects.shortHash _
    (Wots.Ref.short_of_le _ (by rw [chainInput_length]; omega))) value
theorem leafHash_respects (coord selected : Nat) (ends : List Digest) (hlen : ends.length ≤ 200) :
    Wots.Ref.ShortRespects (WCT9.leafHash index coord selected ends) := by
  unfold WCT9.leafHash
  apply Wots.Ref.ShortRespects.shortHash
  apply Wots.Ref.short_of_le
  simp only [List.length_append, bytesLE_length, digest_list_bytes_length, List.length_drop]
  omega
theorem forestPk_respects (pairs : List (Digest × Digest)) (hlen : pairs.length ≤ 100) :
    Wots.Ref.ShortRespects (WCT9.forestPk index pairs) := by
  unfold WCT9.forestPk
  apply Wots.Ref.ShortRespects.shortHash
  apply Wots.Ref.short_of_le
  simp only [forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_length]
  omega
theorem buildChild_respects (coord selected : Nat) (word : Rank) (hcoord : coord < 9) (hsel : selected < 128) :
    Wots.Ref.ShortRespects (buildChild index coord selected word) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildChild_queries index coord selected word hcoord hsel) fun _ => ftsQuery_short)
theorem buildCoordinate_respects (coord : Coord) (selected : Child) (word : Rank) :
    Wots.Ref.ShortRespects (buildCoordinate index coord selected word) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono
    (buildCoordinate_queries index coord selected word) fun _ => ftsQuery_short)
theorem forestRows_respects (output : HashOutput) : Wots.Ref.ShortRespects (forestRows index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (forestRows_queries index output)
    fun _ => ftsQuery_short)
theorem signForest_respects (output : HashOutput) : Wots.Ref.ShortRespects (signForest index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (signForest_queries index output)
    fun _ => ftsQuery_short)
theorem recoverFts_respects (sig : Signature) (output : HashOutput) :
    Wots.Ref.ShortRespects (recoverFts sig index output) :=
  shortRespects_of_allQueriesSatisfy (allQueriesSatisfy_mono (recoverFts_queries index sig output)
    fun _ => ftsQuery_short)
theorem honestForest_short {A T : Answers} (hAT : Wots.Ref.ShortAgree A T) (output : HashOutput) :
    honestForest A index = honestForest T index := by
  rw [← signForest_root A index output, ← signForest_root T index output,
    signForest_respects index output A T hAT]
end Ref
namespace BPB
theorem forestRows_ok (output : HashOutput) : AllQueriesSatisfy (forestRows index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (forestRows_queries index output) fun _ => ftsQuery_notDigest
theorem signForest_ok (output : HashOutput) : AllQueriesSatisfy (signForest index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (signForest_queries index output) fun _ => ftsQuery_notDigest
theorem recoverFts_ok (sig : Signature) (output : HashOutput) :
    AllQueriesSatisfy (recoverFts sig index output) Security.BPB.NotDigestQ :=
  allQueriesSatisfy_mono (recoverFts_queries index sig output) fun _ => ftsQuery_notDigest
end BPB
namespace Structural
theorem sat_signForest_shape (T : Answers) (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsQuery index) (signForest index output) :=
  queriesSat_of_allQueriesSatisfy (signForest_queries index output) T
theorem sat_recoverFts_shape (T : Answers) (sig : Signature) (output : HashOutput) :
    Wots.Structural.QueriesSat T (FtsQuery index) (recoverFts sig index output) :=
  queriesSat_of_allQueriesSatisfy (recoverFts_queries index sig output) T
end Structural
end Programs
end ClaudeWCT.WCT9.Wots
