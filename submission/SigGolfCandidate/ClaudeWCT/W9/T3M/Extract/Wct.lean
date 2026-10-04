import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Queries
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Header
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Defs
import SigGolfCandidate.ClaudeWCT.WCT9.Correctness

namespace ClaudeWCT.W9.T3M.WctExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3M (wdig wrho wdc nodeHashP sibOff)
open Correctness (Answers treeValue TreeLevels)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
theorem queried_mapM {α β : Type} (answers : Answers) (f : α → M β) :
    ∀ l : List α, queried answers (l.mapM f) = l.flatMap fun a => queried answers (f a)
  | [] => rfl
  | a :: l => by
      rw [List.mapM_cons, queried_bind, queried_bind, queried_mapM answers f l]
      simp
theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp
theorem queried_hashPath (answers : Answers) (input : Nat → Digest → HashInput) (initial : Digest) :
    ∀ count, queried answers (hashPath input count initial) =
      (List.range count).map fun step => .inl (.inr (pad64 (pathInput answers input initial step)))
  | 0 => rfl
  | count + 1 => by
      rw [hashPath_succ, queried_bind, queried_hashPath answers input initial count, List.range_succ,
        List.map_append, queried_shortHash]
      rfl
theorem pathValue_honest (answers : Answers) (input : Nat → Digest → HashInput) (honestInput : Nat → HashInput)
    (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) : ∀ step, step ≤ count → pathValue answers input initial step = target step := by
  intro step
  induction step with
  | zero => intro _; exact h0
  | succ step ih =>
      intro hs
      rw [pathValue_succ, pathInput, ih (by omega), honest step (by omega), reference step (by omega)]
theorem queried_hashPath_honest (answers : Answers) (input : Nat → Digest → HashInput)
    (honestInput : Nat → HashInput) (target : Nat → Digest) (initial : Digest) (count : Nat)
    (reference : ∀ step, step < count →
      evalWithAnswerFn answers (shortHash (honestInput step)) = target (step + 1))
    (honest : ∀ step, step < count → input step (target step) = honestInput step)
    (h0 : initial = target 0) :
    ∀ q ∈ queried answers (hashPath input count initial), ∃ step, step < count ∧
      q = .inl (.inr (pad64 (honestInput step))) := by
  intro q hq
  rw [queried_hashPath] at hq
  obtain ⟨step, hs, rfl⟩ := List.mem_map.mp hq
  have hs := List.mem_range.mp hs
  refine ⟨step, hs, ?_⟩
  rw [pathInput, pathValue_honest answers input honestInput target initial count reference honest h0 step hs.le,
    honest step hs]
theorem hdrBlock_block4W (a b c d : Digest) : Extract.hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold Extract.hdrBlock block4
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 a)]
  rw [List.take_append_of_le_length (by simp [bytesLE_length]), List.take_of_length_le (by simp [bytesLE_length])]
theorem hdrBlock_listInput (first : Digest) (hdr : BitVec 128) (rest : List Digest) :
    Extract.hdrBlock (pad64 (Extract.listInput first hdr rest)) = bytesLE 16 hdr := by
  unfold Extract.hdrBlock pad64 Extract.listInput
  rw [List.append_assoc, List.append_assoc, List.drop_left' (bytesLE_length 16 first)]
  rw [List.take_append_of_le_length (by simp [bytesLE_length]), List.take_of_length_le (by simp [bytesLE_length])]
theorem flatMap_bytesLE_length (l : List Digest) : (l.flatMap (bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem flatMap_bytesLE_injective : ∀ (l l' : List Digest), l.length = l'.length →
    l.flatMap (bytesLE 16) = l'.flatMap (bytesLE 16) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, a' :: l', h, he => by
      simp only [List.flatMap_cons] at he
      obtain ⟨ha, hl⟩ := List.append_inj he (by simp only [bytesLE_length])
      rw [bytesLE_injective ha, flatMap_bytesLE_injective l l' (by simpa using h) hl]
theorem pad64_injective_of_length {x y : HashInput} (hl : x.length = y.length) (h : pad64 x = pad64 y) : x = y := by
  unfold pad64 at h
  rw [hl] at h
  exact (List.append_inj h hl).1
theorem listInput_injective {hdr : BitVec 128} {ds ds' : List Digest}
    (hds : ds.length = ds'.length) (hpos : 0 < ds.length)
    (h : pad64 (Extract.listInput (ds.getD 0 0) hdr (ds.drop 1)) =
      pad64 (Extract.listInput (ds'.getD 0 0) hdr (ds'.drop 1))) : ds = ds' := by
  have hlen : (Extract.listInput (ds.getD 0 0) hdr (ds.drop 1)).length =
      (Extract.listInput (ds'.getD 0 0) hdr (ds'.drop 1)).length := by
    simp only [Extract.listInput, List.length_append, bytesLE_length, flatMap_bytesLE_length, List.length_drop, hds]
  have h := pad64_injective_of_length hlen h
  unfold Extract.listInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h1, -⟩ := List.append_inj h12 (by simp only [bytesLE_length])
  have hd := flatMap_bytesLE_injective _ _ (by simp only [List.length_drop, hds]) h3
  have h0 := bytesLE_injective h1
  rcases ds with _ | ⟨a, t⟩
  · simp at hpos
  rcases ds' with _ | ⟨a', t'⟩
  · simp at hds
  simp only [List.getD_cons_zero] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at hd
  rw [h0, hd]
section chain
variable (answers : Answers) (index coord child t : Nat)
theorem wctChainInputP_block4 (step : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainInputP index coord child t step pa pb pc v =
      block4 pa (WCT9.ftsChainHeaderP index coord child t step pb) pc v := rfl
theorem wctChainInput_block4' (step : Nat) (v : Digest) :
    WCT9.chainInput index coord child t step v = block4 0 (WCT9.ftsChainHeader index coord child t step) 0 v := by
  rw [← wctChainInputP_zero, wctChainInputP_block4]; rfl
theorem canonicalHeader_ftsChainHeaderP (step : Nat) (pb : BitVec 64) :
    Extract.canonicalHeader (bytesLE 16 (WCT9.ftsChainHeaderP index coord child t step pb)) =
      Extract.canonicalHeader (bytesLE 16 (WCT9.ftsChainHeader index coord child t step)) := by
  unfold WCT9.ftsChainHeader WCT9.ftsChainHeaderP
  apply SigGolfCandidate.T3M.Extract.canonicalHeader_high_irrelevant
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (WCT9.ftsChainLow_lt ..) (by decide)),
    WCT9.ftsChainLow_byte0]
  omega
theorem wctChainP_eq_hashPath (start count : Nat) (pa : Digest) (pb : BitVec 64) (pc v : Digest) :
    wctChainP index coord child t start count pa pb pc v =
      hashPath (fun step value => wctChainInputP index coord child t (start + step) pa pb pc value) count v :=
  foldlM_range'_eq_hashPath (fun step value => wctChainInputP index coord child t step pa pb pc value) start count v
theorem wctValue_succ (s : Nat) :
    evalWithAnswerFn answers (shortHash (WCT9.chainInput index coord child t s
      (Extract.wctValue answers index coord child t s))) = Extract.wctValue answers index coord child t (s + 1) := by
  unfold Extract.wctValue
  rw [WCT9.eval_chain_add answers index coord child t 0 s 1]
  simp [WCT9.chain]
theorem honestInput_wctChain (s : Nat) :
    Extract.honestInput answers (.wctChain index coord child t s) =
      WCT9.chainInput index coord child t s (Extract.wctValue answers index coord child t s) := by
  simp only [Extract.honestInput, Extract.pad64_wctChainInput]
theorem chain_extract (d : Nat) (hd : d ≤ 3) (pa : Digest) (pb : BitVec 64) (pc v : Digest)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128 ∧ t < 7)
    (reaches : evalWithAnswerFn answers (wctChainP index coord child t (3 - d) d pa pb pc v) =
      Extract.wctValue answers index coord child t 3) :
    (v = Extract.wctValue answers index coord child t (3 - d) ∧ (0 < d → pa = 0 ∧ pb = 0 ∧ pc = 0) ∧
      ∀ q ∈ queried answers (wctChainP index coord child t (3 - d) d pa pb pc v), ∃ s, 3 - d ≤ s ∧ s < 3 ∧
        q = .inl (.inr (Extract.honestInput answers (.wctChain index coord child t s)))) ∨
    Extract.HitIn answers (queried answers (wctChainP index coord child t (3 - d) d pa pb pc v)) := by
  rw [wctChainP_eq_hashPath] at reaches ⊢
  have href : ∀ step, step < d →
      evalWithAnswerFn answers (shortHash (WCT9.chainInput index coord child t (3 - d + step)
        (Extract.wctValue answers index coord child t (3 - d + step)))) =
        Extract.wctValue answers index coord child t (3 - d + (step + 1)) := by
    intro step _
    rw [wctValue_succ, Nat.add_assoc]
  have hparse : ∀ step, step < d → ∀ value,
      pad64 (wctChainInputP index coord child t (3 - d + step) pa pb pc value) =
        pad64 (WCT9.chainInput index coord child t (3 - d + step)
          (Extract.wctValue answers index coord child t (3 - d + step))) →
      value = Extract.wctValue answers index coord child t (3 - d + step) ∧ (pa = 0 ∧ pb = 0 ∧ pc = 0) := by
    intro step _ value heq
    rw [wctChainInputP_block4, wctChainInput_block4', pad64_block4, pad64_block4] at heq
    obtain ⟨h0, hh, h1, hv⟩ := block4_injective heq
    have hpb := congrArg (fun x : BitVec 128 => x.extractLsb' 64 64) hh
    simp only [WCT9.ftsChainHeader, WCT9.ftsChainHeaderP_high] at hpb
    exact ⟨hv, h0, hpb, h1⟩
  have h := hashPath_extract answers
    (fun step value => wctChainInputP index coord child t (3 - d + step) pa pb pc value)
    (fun step => WCT9.chainInput index coord child t (3 - d + step)
      (Extract.wctValue answers index coord child t (3 - d + step)))
    (fun step => Extract.wctValue answers index coord child t (3 - d + step))
    (fun _ => pa = 0 ∧ pb = 0 ∧ pc = 0) v d href hparse
    (by rw [show 3 - d + d = 3 by omega]; exact reaches)
  rcases h with ⟨hv, hgood⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by simpa using hv, fun hd0 => hgood 0 hd0, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers
      (fun step value => wctChainInputP index coord child t (3 - d + step) pa pb pc value)
      (fun step => WCT9.chainInput index coord child t (3 - d + step)
        (Extract.wctValue answers index coord child t (3 - d + step)))
      (fun step => Extract.wctValue answers index coord child t (3 - d + step)) v d href
      (fun step hs => by
        obtain ⟨h0, hB, h1⟩ := hgood step hs
        simp only [h0, hB, h1, wctChainInputP_zero]) hv q hq
    refine ⟨3 - d + step, by omega, by omega, ?_⟩
    rw [honestInput_wctChain, Extract.pad64_wctChainInput]
  · right
    obtain ⟨hi, hc, hj, ht⟩ := hb
    refine ⟨.wctChain index coord child t (3 - d + step), _, ⟨hi, hc, hj, ht, by omega⟩, hq, ?_, ?_⟩
    · rw [honestInput_wctChain, ← Extract.pad64_wctChainInput]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, pathInput]
      simp only [wctChainInputP_block4, pad64_block4, hdrBlock_block4W, Extract.Pos.hdr]
      exact canonicalHeader_ftsChainHeaderP index coord child t _ _
end chain
theorem leafHash_eq_shortHash (index coord child : Nat) (ends : List Digest) :
    WCT9.leafHash index coord child ends = shortHash (Extract.wctLeafInput index coord child ends) := by
  unfold WCT9.leafHash Extract.wctLeafInput Extract.listInput
  rw [WCT9.leaf_header_eq]
theorem childRoot_eq_out (answers : Answers) (index coord child : Nat) :
    WCT9.childRoot answers index coord child =
      (answers (.inl (.inr (Extract.honestInput answers (.wctLeaf index coord child))))).extractLsb' 0 128 := by
  unfold WCT9.childRoot
  rw [leafHash_eq_shortHash, eval_shortHash]
  rfl
theorem wctEnds_length (answers : Answers) (index coord child : Nat) :
    (Extract.wctEnds answers index coord child).length = 7 := by
  simp [Extract.wctEnds]
theorem leaf_extract (answers : Answers) (index coord child : Nat) (ends : List Digest) (hlen : ends.length = 7)
    (hb : index < 2 ^ 31 ∧ coord < 9 ∧ child < 128)
    (reaches : evalWithAnswerFn answers (WCT9.leafHash index coord child ends) =
      WCT9.childRoot answers index coord child) :
    (ends = Extract.wctEnds answers index coord child ∧
      queried answers (WCT9.leafHash index coord child ends) =
        [.inl (.inr (Extract.honestInput answers (.wctLeaf index coord child)))]) ∨
    Extract.HitIn answers (queried answers (WCT9.leafHash index coord child ends)) := by
  rw [leafHash_eq_shortHash] at reaches ⊢
  rw [queried_shortHash]
  by_cases heq : pad64 (Extract.wctLeafInput index coord child ends) =
      Extract.honestInput answers (.wctLeaf index coord child)
  · left
    refine ⟨listInput_injective (by rw [hlen, wctEnds_length]) (by omega) heq, by rw [heq]⟩
  · right
    refine ⟨.wctLeaf index coord child, _, hb, List.mem_singleton_self _, ⟨heq, ?_⟩, ?_⟩
    · rw [eval_shortHash] at reaches
      rw [reaches, childRoot_eq_out]
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, Extract.hdrBlock_wctLeafInput]
      rfl
theorem merkleInput_tree_reference_le (answers : Answers) (tag lay tree height completed leaf : Nat)
    (levels : List (List Digest)) (leaves : List Digest)
    (htree : TreeLevels answers tag lay tree height leaves completed levels)
    (hleaf : leaf < 2 ^ height) (step : Nat) (hstep : step < completed) (hc : completed ≤ height) :
    evalWithAnswerFn answers (shortHash
      (merkleInput tag lay tree height leaf
        (fun j => treeValue levels j (leaf / 2 ^ j ^^^ 1)) (fun _ => 0)
        step (treeValue levels step (leaf / 2 ^ step)))) =
      treeValue levels (step + 1) (leaf / 2 ^ (step + 1)) := by
  unfold merkleInput
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rw [← nodeHash_eq_shortHash]
  have hparent : leaf / 2 ^ (step + 1) < 2 ^ (height - (step + 1)) := by
    simpa using Correctness.div_pow_bound (start := 0) (level := step + 1)
      (node := leaf) (height := height) (by omega) (by simpa using hleaf)
  have hp := htree.2.2 step hstep (leaf / 2 ^ (step + 1)) hparent
  simpa only [treeValue, Nat.sub_sub] using hp.symm
section merkle
variable (answers : Answers) (index : Nat) (c : WCT9.Coord) (j : Nat)
def mTarget (step : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) step (j / 2 ^ step)
def mPath (l : Nat) : Digest := treeValue (Extract.ftsLevels answers index c.val) l (j / 2 ^ l ^^^ 1)
theorem ftsLevels_treeLevels :
    TreeLevels answers 3 (WCT9.nodeLayer c.val) index 7 (WCT9.coordLeaves answers index c) 6
      (Extract.ftsLevels answers index c.val) :=
  WCT9.coordinate_treeLevels answers index c
theorem merkle_reference (hj : j < 128) : ∀ step, step < 6 →
    evalWithAnswerFn answers (shortHash (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j)
      (fun _ => 0) step (mTarget answers index c j step))) = mTarget answers index c j (step + 1) :=
  fun step hstep => merkleInput_tree_reference_le answers 3 (WCT9.nodeLayer c.val) index 7 6 j _ _
    (ftsLevels_treeLevels answers index c) (by norm_num; omega) step hstep (by decide)
theorem ftsLevels_leaf (hj : j < 128) :
    treeValue (Extract.ftsLevels answers index c.val) 0 j = WCT9.childRoot answers index c.val j := by
  unfold Extract.ftsLevels
  rw [WCT9.heapLevels_value _ 0 j (by omega) (by simpa using hj)]
  have hg := (WCT9.coordNodes_graph answers index c).2.1 (2 ^ (7 - 0) + j) (by norm_num) (by norm_num; omega)
  rw [show Extract.ftsNodes answers index c.val = WCT9.coordNodes answers index c from rfl, hg,
    show 2 ^ (7 - 0) + j - 128 = j by norm_num]
  unfold WCT9.coordLeaves
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_ofFn]
theorem mTarget_zero (hj : j < 128) : mTarget answers index c j 0 = WCT9.childRoot answers index c.val j := by
  unfold mTarget
  rw [pow_zero, Nat.div_one, ftsLevels_leaf answers index c j hj]
theorem merkle_honestInput (step : Nat) :
    pad64 (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j) (fun _ => 0) step
      (mTarget answers index c j step)) =
      Extract.honestInput answers (.wctNode index c.val step (j / 2 ^ (step + 1))) := by
  unfold merkleInput mPath mTarget
  dsimp only
  rw [Correctness.sibling_pair, Correctness.div_pow_succ]
  rfl
theorem hdrBlock_merkleInput (path pads : Nat → Digest) (step : Nat) (value : Digest) :
    Extract.hdrBlock (pad64 (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads step value)) =
      bytesLE 16 (header 3 (WCT9.nodeLayer c.val) index 0 (2 ^ (7 - step - 1) + j / 2 ^ (step + 1))) := by
  unfold merkleInput
  dsimp only
  split <;> rw [Extract.hdrBlock_nodeInputP]
theorem merkle_extract (hidx : index < 2 ^ 31) (hj : j < 128) (path pads : Nat → Digest) (leaf : Digest)
    (reaches : evalWithAnswerFn answers (hashPath (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads) 6
      leaf) = mTarget answers index c j 6) :
    (leaf = WCT9.childRoot answers index c.val j ∧
      (∀ l, l < 6 → path l = mPath answers index c j l ∧ pads l = 0) ∧
      ∀ q ∈ queried answers (hashPath (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads) 6 leaf),
        ∃ l, l < 6 ∧ q = .inl (.inr (Extract.honestInput answers (.wctNode index c.val l (j / 2 ^ (l + 1)))))) ∨
    Extract.HitIn answers (queried answers
      (hashPath (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads) 6 leaf)) := by
  have hR := merkle_reference answers index c j hj
  have h := merklePath_extract answers 3 (WCT9.nodeLayer c.val) index 7 j 6 path pads (mPath answers index c j)
    (mTarget answers index c j) leaf hR reaches
  rcases h with ⟨h0, hall⟩ | ⟨step, hstep, hq, hhit⟩
  · left
    refine ⟨by rw [h0, mTarget_zero answers index c j hj], hall, fun q hq => ?_⟩
    obtain ⟨step, hs, rfl⟩ := queried_hashPath_honest answers
      (merkleInput 3 (WCT9.nodeLayer c.val) index 7 j path pads)
      (fun step => merkleInput 3 (WCT9.nodeLayer c.val) index 7 j (mPath answers index c j) (fun _ => 0) step
        (mTarget answers index c j step))
      (mTarget answers index c j) leaf 6 hR
      (fun step hs => by unfold merkleInput; rw [(hall step hs).1, (hall step hs).2]) h0 q hq
    exact ⟨step, hs, by rw [merkle_honestInput]⟩
  · right
    have hn : j / 2 ^ (step + 1) < 2 ^ (7 - step - 1) := by
      have := Correctness.div_pow_bound (node := j) (height := 7) (start := 0) (level := step + 1) (by omega)
        (by norm_num; omega)
      simpa [Nat.sub_sub] using this
    refine ⟨.wctNode index c.val step (j / 2 ^ (step + 1)), _, ⟨hidx, c.isLt, hstep, hn⟩, hq, ?_, ?_⟩
    · rw [← merkle_honestInput]; exact hhit
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, pathInput, hdrBlock_merkleInput]
      rfl
end merkle
theorem recoverCoordinateP_dec (N : HashOutput) (w : WBytes) (index : Nat) (c : WCT9.Coord) :
    recoverCoordinateP (witDecP N w).signature (padDecP N w) index N c =
      ((List.finRange 7).mapM (fun t => wctChainP index c.val (WCT9.child N c).val t.val
          (3 - WCT9.digit (WCT9.rank N c) t) (WCT9.digit (WCT9.rank N c) t)
          (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
          (wreveal w c.val t.val (WCT9.digit (WCT9.rank N c) t))) >>= fun ends =>
        WCT9.leafHash index c.val (WCT9.child N c).val ends >>= fun leaf =>
          hashPath (merkleInput 3 (WCT9.nodeLayer c.val) index 7 (WCT9.child N c).val
            (wsib w c.val (WCT9.child N c).val) (wmpad w c.val)) 6 leaf >>= fun top =>
          pure (if (WCT9.child N c).val / 2 ^ 6 % 2 = 0 then (top, wsib w c.val (WCT9.child N c).val 6)
            else (wsib w c.val (WCT9.child N c).val 6, top))) := by
  unfold recoverCoordinateP
  rfl
theorem pair_parse (levels : List (List Digest)) (j : Nat) (hj : j < 128) (top other : Digest)
    (h : (if j / 2 ^ 6 % 2 = 0 then (top, other) else (other, top)) =
      (treeValue levels 6 0, treeValue levels 6 1)) :
    top = treeValue levels 6 (j / 2 ^ 6) ∧ other = treeValue levels 6 (j / 2 ^ 6 ^^^ 1) := by
  have hq : j / 2 ^ 6 < 2 := by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    norm_num; omega
  rcases (show j / 2 ^ 6 = 0 ∨ j / 2 ^ 6 = 1 by omega) with h0 | h0 <;> rw [h0] at h ⊢ <;>
    simp only [Nat.zero_mod, Nat.one_mod, if_true, if_false, one_ne_zero, Prod.mk.injEq] at h <;>
    exact ⟨by first | exact h.1 | exact h.2, by first | exact h.2 | exact h.1⟩
theorem coord_extract (answers : Answers) (N : HashOutput) (w : WBytes) (c : WCT9.Coord)
    (reaches : evalWithAnswerFn answers
        (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c) =
      Extract.ftsPair answers (N.toNat % 2 ^ 31) c.val) :
    ((∀ q ∈ queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c),
        HonestQ answers N c q) ∧ CoordHonest answers N w c) ∨
    Extract.HitIn answers
      (queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c)) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hj := (WCT9.child N c).isLt
  rw [recoverCoordinateP_dec] at reaches ⊢
  rw [queried_bind, queried_bind, queried_bind]
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at reaches
  simp only [queried_pure, List.append_nil]
  generalize hE : evalWithAnswerFn answers ((List.finRange 7).mapM (fun t => wctChainP (N.toNat % 2 ^ 31) c.val
      (WCT9.child N c).val t.val (3 - WCT9.digit (WCT9.rank N c) t) (WCT9.digit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.digit (WCT9.rank N c) t)))) = ends at reaches ⊢
  generalize hL : evalWithAnswerFn answers (WCT9.leafHash (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val ends) =
    leaf at reaches ⊢
  generalize hT : evalWithAnswerFn answers (hashPath (merkleInput 3 (WCT9.nodeLayer c.val) (N.toNat % 2 ^ 31) 7
    (WCT9.child N c).val (wsib w c.val (WCT9.child N c).val) (wmpad w c.val)) 6 leaf) = top at reaches
  obtain ⟨htop, hsib6⟩ := pair_parse (Extract.ftsLevels answers (N.toNat % 2 ^ 31) c.val) (WCT9.child N c).val hj
    top _ reaches
  rcases merkle_extract answers (N.toNat % 2 ^ 31) c (WCT9.child N c).val hidx hj _ _ leaf
      (by rw [hT, htop]; rfl) with ⟨hleaf, hsib, hqM⟩ | hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_right _ hq))
  have hlen : ends.length = 7 := by rw [← hE, Correctness.eval_mapM]; simp
  rcases leaf_extract answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val ends hlen ⟨hidx, c.isLt, hj⟩
    (hL.trans hleaf) with ⟨hends, hqL⟩ | hhit
  swap
  · exact Or.inr (hhit.mono fun q hq => List.mem_append_right _ (List.mem_append_left _ hq))
  have hend : ∀ t : Fin 7, evalWithAnswerFn answers (wctChainP (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val
      (3 - WCT9.digit (WCT9.rank N c) t) (WCT9.digit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.digit (WCT9.rank N c) t))) =
      Extract.wctValue answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val 3 := by
    intro t
    subst hE
    rw [Correctness.eval_mapM] at hends
    have h := List.getElem_of_eq hends (i := t.val) (by simp)
    simpa only [List.getElem_map, List.getElem_finRange, Extract.wctEnds, List.getElem_ofFn, Fin.cast_mk,
      Fin.eta, Fin.cast_eq_self] using h
  have hch := fun t : Fin 7 => chain_extract answers (N.toNat % 2 ^ 31) c.val (WCT9.child N c).val t.val
    (WCT9.digit (WCT9.rank N c) t) (WCT9.digit_le_three _ t) _ _ _ _ ⟨hidx, c.isLt, hj, t.isLt⟩ (hend t)
  by_cases hhit : ∃ t : Fin 7, Extract.HitIn answers (queried answers (wctChainP (N.toNat % 2 ^ 31) c.val
      (WCT9.child N c).val t.val (3 - WCT9.digit (WCT9.rank N c) t) (WCT9.digit (WCT9.rank N c) t)
      (wcpads w c.val t.val).1 (wcHeaderPad w c.val t.val) (wcpads w c.val t.val).2
      (wreveal w c.val t.val (WCT9.digit (WCT9.rank N c) t))))
  · obtain ⟨t, ht⟩ := hhit
    exact Or.inr (ht.mono fun q hq => List.mem_append_left _
      (by rw [queried_mapM]; exact List.mem_flatMap.mpr ⟨t, List.mem_finRange t, hq⟩))
  · push Not at hhit
    have hgood := fun t => (hch t).resolve_right (hhit t)
    left
    refine ⟨fun q hq => ?_, ⟨fun t => ⟨(hgood t).1, fun hd => ?_⟩, fun l hl => ?_⟩⟩
    · rcases List.mem_append.mp hq with hq | hq
      · rw [queried_mapM] at hq
        obtain ⟨t, -, hq⟩ := List.mem_flatMap.mp hq
        obtain ⟨s, h1, h2, rfl⟩ := (hgood t).2.2 q hq
        exact Or.inl ⟨t, s, h1, h2, rfl⟩
      rcases List.mem_append.mp hq with hq | hq
      · rw [hqL] at hq
        rw [List.mem_singleton.mp hq]
        exact Or.inr (Or.inl rfl)
      · obtain ⟨l, hl, rfl⟩ := hqM q hq
        exact Or.inr (Or.inr ⟨l, hl, rfl⟩)
    · obtain ⟨h0, hB, h1⟩ := (hgood t).2.1 hd
      exact ⟨Prod.ext h0 h1, hB⟩
    · by_cases hl6 : l < 6
      · exact ⟨(hsib l hl6).1, fun _ => (hsib l hl6).2⟩
      · have hl6' : l = 6 := by omega
        subst hl6'
        exact ⟨hsib6, fun h => absurd h (by decide)⟩
theorem forestPk_eq_shortHash (index : Nat) (pairs : List (Digest × Digest)) :
    WCT9.forestPk index pairs = shortHash (Extract.forestInput index pairs) := rfl
theorem forest_pairs_injective {index : Nat} {ps qs : List (Digest × Digest)} (hl : ps.length = qs.length)
    (h : pad64 (Extract.forestInput index ps) = pad64 (Extract.forestInput index qs)) : ps = qs := by
  have hlen : (Extract.forestInput index ps).length = (Extract.forestInput index qs).length := by
    simp only [Extract.forestInput, WCT9.forestInput, zero16, List.length_append, List.length_replicate,
      bytesLE_length, WCT9.pairs_bytes_length, hl]
  have h := pad64_injective_of_length hlen h
  unfold Extract.forestInput WCT9.forestInput at h
  obtain ⟨-, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  exact WCT9.pairs_bytes_injective hl hp
theorem wct_extract (answers : Answers) (N : HashOutput) (w : WBytes) (_hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
      Extract.honestForest answers (N.toNat % 2 ^ 31)) :
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N)) ∨
      WctHonest answers N w := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  unfold WctHonest
  unfold recoverFtsP at hrun ⊢
  rw [queried_bind]
  rw [evalWithAnswerFn_bind] at hrun
  rw [Correctness.eval_mapM] at hrun ⊢
  rw [forestPk_eq_shortHash, queried_shortHash]
  rw [forestPk_eq_shortHash, eval_shortHash] at hrun
  generalize hR : (List.finRange 9).map (fun c => evalWithAnswerFn answers
    (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c)) = pairs at hrun ⊢
  have hlen : pairs.length = 9 := by rw [← hR]; simp
  by_cases heq : pad64 (Extract.forestInput (N.toNat % 2 ^ 31) pairs) =
      Extract.honestInput answers (.forest (N.toNat % 2 ^ 31))
  · have hpairs : pairs = Extract.ftsPairsHonest answers (N.toNat % 2 ^ 31) :=
      forest_pairs_injective (by rw [hlen, Extract.ftsPairsHonest_length]) heq
    have hc : ∀ c : WCT9.Coord, evalWithAnswerFn answers
        (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c) =
        Extract.ftsPair answers (N.toNat % 2 ^ 31) c.val := by
      intro c
      have := congrArg (fun l => l.getD c.val (0, 0)) (hR.trans hpairs)
      simpa [Extract.ftsPairsHonest, List.getD_eq_getElem?_getD] using this
    by_cases hhit : ∃ c : WCT9.Coord, Extract.HitIn answers
        (queried answers (recoverCoordinateP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N c))
    · obtain ⟨c, hcq⟩ := hhit
      exact Or.inl (hcq.mono fun q hq => List.mem_append_left _
        (by rw [queried_mapM]; exact List.mem_flatMap.mpr ⟨c, List.mem_finRange c, hq⟩))
    · push Not at hhit
      have hgood := fun c => (coord_extract answers N w c (hc c)).resolve_right (hhit c)
      right
      refine ⟨fun q hq => ?_, fun c => (hgood c).2⟩
      rcases List.mem_append.mp hq with hq | hq
      · rw [queried_mapM] at hq
        obtain ⟨c, -, hq⟩ := List.mem_flatMap.mp hq
        exact Or.inr ⟨c, (hgood c).1 q hq⟩
      · rw [List.mem_singleton.mp hq, heq]
        exact Or.inl rfl
  · left
    refine ⟨.forest (N.toNat % 2 ^ 31), _, lt_trans hidx (by norm_num), List.mem_append_right _
      (List.mem_singleton_self _), ⟨heq, ?_⟩, ?_⟩
    · rw [hrun]
      unfold Extract.honestForest
      rw [forestPk_eq_shortHash, eval_shortHash]
      rfl
    · unfold Extract.SameHeader
      rw [Extract.hdrBlock_honestInput, Extract.hdrBlock_forestInput]
      rfl
def WctExtractSpecN (WctShaped : Answers → HashOutput → WBytes → Prop) : Prop :=
  ∀ (answers : Answers) (N : HashOutput) (w : WBytes), Shaped N w →
    evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
      Extract.honestForest answers (N.toNat % 2 ^ 31) →
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N)) ∨
      WctShaped answers N w
theorem wctExtractSpecN_holds : WctExtractSpecN WctHonest := wct_extract
theorem eval_rejectTail (answers : Answers) (w : WBytes) (N : HashOutput) :
    evalWithAnswerFn answers (rejectTail w N) = false := by
  unfold rejectTail
  split
  · rfl
  · rw [evalWithAnswerFn_map]
theorem shaped_of_verifyP (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    (wdc w).toNat < WCT9.digestAttemptLimit ∧ Shaped (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w := by
  classical
  rw [verifyP_normal] at hv
  by_cases hdc : (wdc w).toNat ≥ WCT9.digestAttemptLimit
  · rw [if_pos hdc] at hv; simp at hv
  rw [if_neg hdc, evalWithAnswerFn_bind] at hv
  refine ⟨by omega, ?_⟩
  by_contra hS
  rw [if_neg hS, eval_rejectTail] at hv
  exact Bool.false_ne_true hv
theorem verifyP_walk_wct (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      evalWithAnswerFn answers (layersBC w (N.toNat % 2 ^ 31) 4 (.forest (evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N)))) = some pk ∧
      (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N),
        q ∈ queried answers (verifyP m pk w)) ∧
      (∀ q ∈ queried answers (layersBC w (N.toNat % 2 ^ 31) 4 (.forest (evalWithAnswerFn answers
          (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N)))),
        q ∈ queried answers (verifyP m pk w)) := by
  classical
  obtain ⟨hdc, hS⟩ := shaped_of_verifyP answers m pk w hv
  rw [verifyP_eq_tail] at hv ⊢
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg (by omega)]
  rw [hD, bind_map_left] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv hS ⊢
  refine ⟨N, hdc, rfl, ?_, hS, ?_⟩
  · apply List.mem_append_left
    unfold digest publicHash
    rw [show (liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) : M HashOutput) =
      liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) >>= pure from (bind_pure _).symm,
      queried_query_bind]
    exact List.mem_cons_self
  dsimp only at hv ⊢
  try unfold verifyTailP at hv ⊢
  rw [if_neg (by simp [gateOk_of_admissible hS])] at hv ⊢
  rw [wctP_shaped N w hS, bind_map_left] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers
    (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) = root at hv ⊢
  dsimp only at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hL : evalWithAnswerFn answers (layersBC w (N.toNat % 2 ^ 31) 4 (.forest root)) = ll at hv ⊢
  rcases ll with _ | root'
  · simp at hv
  simp only [evalWithAnswerFn_pure, beq_iff_eq] at hv
  subst hv
  exact ⟨rfl, fun q hq => List.mem_append_right _ (List.mem_append_left _ hq),
    fun q hq => List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hq))⟩
theorem verifyP_wct_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) N) =
          Extract.honestForest answers (N.toNat % 2 ^ 31) →
        Extract.HitIn answers (queried answers (verifyP m pk w)) ∨ WctHonest answers N w) := by
  obtain ⟨N, hdc, hN, hdq, hS, -, hqF, -⟩ := verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, fun hroot => ?_⟩
  rcases wct_extract answers N w hS hroot with hhit | hhon
  · exact Or.inl (hhit.mono hqF)
  · exact Or.inr hhon
def LayersWalkSpec (LayerEvent : Answers → WBytes → Nat → List Spec.Domain → Prop)
    (LayersGood : Answers → WBytes → Nat → Prop) : Prop :=
  ∀ (answers : Answers) (w : WBytes) (index : Nat) (root : Digest) (qs : List Spec.Domain), index < 2 ^ 31 →
    (∀ q ∈ queried answers (layersBC w index 4 (.forest root)), q ∈ qs) →
    evalWithAnswerFn answers (layersBC w index 4 (.forest root)) = some (Extract.honestRoot answers 0 0) →
    LayerEvent answers w index qs ∨ (LayersGood answers w index ∧ root = Extract.honestForest answers index)
theorem verifyP_extract {LayerEvent : Answers → WBytes → Nat → List Spec.Domain → Prop}
    {LayersGood : Answers → WBytes → Nat → Prop} (hL : LayersWalkSpec LayerEvent LayersGood)
    (answers : Answers) (m : Message) (pk : Digest) (w : WBytes) (hpk : pk = Extract.honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < WCT9.digestAttemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (Extract.HitIn answers (queried answers (verifyP m pk w)) ∨
        LayerEvent answers w (N.toNat % 2 ^ 31) (queried answers (verifyP m pk w)) ∨
        (LayersGood answers w (N.toNat % 2 ^ 31) ∧ WctHonest answers N w)) := by
  obtain ⟨N, hdc, hN, hdq, hS, hlay, hqF, hqL⟩ := verifyP_walk_wct answers m pk w hv
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hL answers w (N.toNat % 2 ^ 31) _ _ (Nat.mod_lt _ (by norm_num)) hqL (hpk ▸ hlay) with hev | ⟨hgood, hroot⟩
  · exact Or.inr (Or.inl hev)
  rcases wct_extract answers N w hS hroot with hhit | hhon
  · exact Or.inl (hhit.mono hqF)
  · exact Or.inr (Or.inr ⟨hgood, hhon⟩)
end ClaudeWCT.W9.T3M.WctExtract
