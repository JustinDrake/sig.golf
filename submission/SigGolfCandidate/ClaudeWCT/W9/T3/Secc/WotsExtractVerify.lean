import SigGolfCandidate.T3.Secc.WotsExtractVerify
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEventsGood
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsExtractLayer
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.VerifyP
import SigGolfCandidate.ClaudeWCT.W9.New.G3b.Shared

namespace ClaudeWCT.W9.T3.Security.WotsExtract
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open SigGolfCandidate.T3.Security.Wots (LeafAddr ChainAddr Entry low encodingRow entriesOf)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3.Security.Wots
open ClaudeWCT.W9.T3M.WctExtract (wctChainP_eq_hashPath wctChainInputP_block4 queried_hashPath queried_mapM
  hdrBlock_block4W leafHash_eq_shortHash hdrBlock_merkleInput recoverCoordinateP_dec forestPk_eq_shortHash)
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wrho wdc layersP)
open SigGolfCandidate.T3.Security.WotsExtract (SourceLeaf SourceChain mem_entriesOf entriesOf_mono)
open SigGolfCandidate.T3.Correctness (Answers)
open SphincsSecurity (bytesLE bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem layersP_wots_walk (answers : Answers) (w : WBytes) (index : Nat) (hidx : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ root : Digest,
    evalWithAnswerFn answers (layersP w index n root) = some (Extract.walkTarget answers index 0) →
    WotsPrimitiveSrc answers (entriesOf answers (queried answers (layersP w index n root))) ∨
    ((∀ l : Layer, l.val < n → Extract.Good answers w index l) ∧ root = Extract.walkTarget answers index n)
  | 0, _, root, h => by
      right
      refine ⟨fun l hl => absurd hl (Nat.not_lt_zero _), ?_⟩
      simpa [layersP] using h
  | n + 1, hn, root, h => by
      classical
      obtain ⟨digits, hframe, hrest, henc, hqL, hqR⟩ := Extract.layersP_succ_split answers w index n root _ h
      have hval : (Fin.ofNat 4 n : Layer).val = n := by simp; omega
      rcases layersP_wots_walk answers w index hidx n (by omega) _ hrest with hprim | ⟨hgood, hv⟩
      · exact Or.inl (hprim.mono (entriesOf_mono hqR))
      · rw [Extract.walkTarget_root answers index n (by omega)] at hv
        rcases layer_wots answers w index (Fin.ofNat 4 n) root digits hidx hframe
            (queried answers (layersP w index (n + 1) root)) henc hqL hv with hprim | ⟨hmsg, hgoodn⟩
        · exact Or.inl hprim
        · right
          have hmsg' : Extract.honestMsg answers index (Fin.ofNat 4 n) = Extract.walkTarget answers index (n + 1) := by
            have hl : (Fin.ofNat 4 n : Layer) = ⟨n, by omega⟩ := Fin.ext hval
            simp only [Extract.walkTarget, dif_pos (show n < 4 by omega), hl]
          refine ⟨fun l hl => ?_, hmsg.trans hmsg'⟩
          by_cases hle : l.val < n
          · exact hgood l hle
          · have hl : l = Fin.ofNat 4 n := Fin.ext (by rw [hval]; omega)
            subst hl
            exact hgoodn
theorem verifyP_walk_wots (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers
              (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
            Extract.honestForest answers (N.toNat % 2 ^ 31) ∧
          ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := WctExtract.verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have htop : Extract.walkTarget answers (N.toNat % 2 ^ 31) 0 = pk := by
    rw [hpk]; simp only [Extract.walkTarget, route_top_tree _ hidx]
  rcases layersP_wots_walk answers w (N.toNat % 2 ^ 31) hidx 4 le_rfl _ (by rw [hlay, htop]) with hprim | ⟨hgood, hroot⟩
  · exact Or.inl (hprim.mono (entriesOf_mono hqL))
  · right
    refine ⟨fun l => hgood l l.isLt, ?_, hqF⟩
    rw [hroot]
    simp [Extract.walkTarget, Extract.honestMsg]
def FtsPos : Extract.Pos → Prop
  | .wctChain .. => True
  | .wctLeaf .. => True
  | .wctNode .. => True
  | .forest _ => True
  | _ => False
def FtsQueryPos (actual : HashInput) : Prop :=
  ∃ pos : Extract.Pos, pos.Bounded ∧ PosSource pos ∧ FtsPos pos ∧
    Extract.hdrBlock actual = bytesLE 16 pos.hdr
theorem chain_queries_pos (answers : Answers) (index coord child t d : Nat) (hd : d ≤ 3) (p0 p1 v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 7) :
    ∀ q ∈ queried answers (wctChainP index coord child t (3 - d) d p0 p1 v),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [wctChainP_eq_hashPath, queried_hashPath] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  obtain ⟨hi, hc, hj, ht⟩ := hb
  refine ⟨_, rfl, .wctChain index coord child t (3 - d + s), ⟨hi, hc, hj, ht, by omega⟩,
    ⟨hi, hc, hj, ht, by omega⟩, trivial, ?_⟩
  simp only [pathInput, wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr]
theorem leaf_queries_pos (answers : Answers) (index coord child : Nat) (ends : List Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128) :
    ∀ q ∈ queried answers (WCT9.leafHash index coord child ends),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [leafHash_eq_shortHash, queried_shortHash] at hq
  rw [List.mem_singleton] at hq
  subst hq
  obtain ⟨hi, hc, hj⟩ := hb
  refine ⟨_, rfl, .wctLeaf index coord child, ⟨hi, hc, hj⟩, ⟨hi, hc, hj⟩, trivial, ?_⟩
  rw [Extract.hdrBlock_wctLeafInput]
  rfl
theorem merkle_queries_pos (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat) (hj : j < 128)
    (hidx : index < 2 ^ 31) (path pads : Nat → Digest) (leaf : Digest) :
    ∀ q ∈ queried answers (hashPath (merkleInput 11 c.val index 7 j path pads) 7 leaf),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  have hn : j / 2 ^ (s + 1) < 2 ^ (7 - s - 1) := by
    have := Correctness.div_pow_bound (node := j) (height := 7) (start := 0) (level := s + 1) (by omega)
      (by norm_num; omega)
    simpa [Nat.sub_sub] using this
  refine ⟨_, rfl, .wctNode index c.val s (j / 2 ^ (s + 1)), ⟨hidx, c.isLt, hs, hn⟩, ⟨hidx, c.isLt, hs, hn⟩,
    trivial, ?_⟩
  rw [pathInput, hdrBlock_merkleInput]
  rfl
theorem coord_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord) :
    ∀ q ∈ queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hj := (WCT9.child N c).isLt
  rw [recoverCoordinateP_dec] at hq
  rw [queried_bind, queried_bind] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [queried_mapM] at hq
    obtain ⟨t, -, hq⟩ := List.mem_flatMap.mp hq
    exact chain_queries_pos answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val
      (WCT9.digit (WCT9.rank N c) t) (WCT9.digit_le_three _ t) _ _ _ ⟨hidx, c.isLt, hj, t.isLt⟩ q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact leaf_queries_pos answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val _ ⟨hidx, c.isLt, hj⟩ q hq
  · exact merkle_queries_pos answers (N.toNat % 2 ^ 31) c (WCT9.child N c).val hj hidx _ _ _ q hq
theorem fts_queries_pos (answers : Answers) (N : HashOutput) (w : WBytes) :
    ∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
      ∃ actual, q = .inl (.inr actual) ∧ FtsQueryPos actual := by
  intro q hq
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  unfold recoverFtsP at hq
  rw [queried_bind, forestPk_eq_shortHash, queried_shortHash] at hq
  rcases List.mem_append.mp hq with hq | hq
  · rw [queried_mapM] at hq
    obtain ⟨c, -, hq⟩ := List.mem_flatMap.mp hq
    exact coord_queries_pos answers N w c q hq
  · rw [List.mem_singleton] at hq
    subst hq
    refine ⟨_, rfl, .forest (N.toNat % 2 ^ 31), by exact lt_trans hidx (by norm_num), hidx, trivial, ?_⟩
    rw [Extract.hdrBlock_forestInput]
    rfl
theorem structuralHitSrc_of_fts_hitIn (answers : Answers) (N : HashOutput) (w : WBytes)
    (h : Extract.HitIn answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N))) :
    StructuralHitSrc answers (entriesOf answers
      (queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N))) := by
  obtain ⟨pos, actual, hb, hq, hh, hs⟩ := h
  obtain ⟨actual', hqe, pos', hb', hsrc', hfts', hdr'⟩ := fts_queries_pos answers N w _ hq
  have hae : actual = actual' := by simpa using hqe
  subst hae
  have hkey' : Extract.canonicalHeader (Extract.hdrBlock actual) = bytesLE 16 pos'.hdr := by
    rw [hdr', Extract.Pos.canonicalHeader_eq hb']
  have hhdr : pos.hdr = pos'.hdr := by
    apply bytesLE_injective (n := 16)
    have hkey := hs.symm.trans hkey'
    rw [Extract.hdrBlock_honestInput, Extract.Pos.canonicalHeader_eq hb] at hkey
    exact hkey
  have hpos : pos = pos' := Extract.Pos.hdr_injective hb hb' hhdr
  subst hpos
  refine ⟨pos, actual, _, mem_entriesOf hq, Extract.posOf_key_eq hb (by rw [hs, Extract.hdrBlock_honestInput, Extract.Pos.canonicalHeader_eq hb]), hb,
    hsrc', ?_, hh⟩
  cases pos <;> trivial
theorem fts_structural (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
      Extract.honestForest answers (N.toNat % 2 ^ 31)) :
    StructuralHitSrc answers (entriesOf answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N))) ∨
      WctExtract.WctHonest answers N w :=
  (WctExtract.wct_extract answers N w hS hrun).imp_left (structuralHitSrc_of_fts_hitIn answers N w)
theorem verifyP_wots_cases_src (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitiveSrc answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N w)) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_walk_wots answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hprim | ⟨hgood, hR, hqV⟩
  · exact Or.inl hprim
  rcases fts_structural answers N w hS hR with hhit | hshape
  · exact Or.inl (Or.inr (Or.inl (structuralHitSrc_mono hhit (entriesOf_mono hqV))))
  · exact Or.inr ⟨hgood, hshape⟩
end ClaudeWCT.W9.T3.Security.WotsExtract
namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wrho wdc)
open ClaudeWCT.W9.T3.Security.WotsExtract
open SigGolfCandidate.T3.Security.Wots (entriesOf)
open SigGolfCandidate.T3.Correctness (Answers)
theorem verifyP_wots_cases (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (WotsPrimitive answers (entriesOf answers (queried answers (verifyP m pk w))) ∨
       ((∀ l : Layer, Extract.Good answers w (N.toNat % 2 ^ 31) l) ∧ WctExtract.WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hcase⟩ := verifyP_wots_cases_src answers m pk w hpk hv
  exact ⟨N, hdc, hN, hdq, hS, hcase.imp_left WotsPrimitiveSrc.toPrimitive⟩
end ClaudeWCT.W9.T3.Security.Wots
