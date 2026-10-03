import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CanonGraphHonest
import SigGolfCandidate.ClaudeWCT.W9.New.Positions.FtsBridge
import SigGolfCandidate.ClaudeWCT.W9.T3M.Extract.Layer
import SigGolfCandidate.ClaudeWCT.WCT9.Honest
import SigGolfCandidate.T3.Secc.WotsStructuralHonest

namespace ClaudeWCT.W9.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3.Security.Wots.Structural
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf
def HonestQuery (T : Answers) : SigGolfCandidate.T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ ∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p
  | _ => True
theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial
theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr ⟨p, hp, rfl⟩
theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)
theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privatePair tag lay tree position index) := by
  unfold SigGolfCandidate.T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.mask level index) := by
  unfold SigGolfCandidate.T3.mask SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)
theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateMac region) := by
  unfold SigGolfCandidate.T3.privateMac SigGolfCandidate.T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)
theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.maskedLevel nodes level) := by
  unfold SigGolfCandidate.T3.maskedLevel SigGolfCandidate.T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)
theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.privateNonce message) := by
  unfold SigGolfCandidate.T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)
theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded → Extract.hdrBlock x ≠ bytesLE 16 p.hdr) : Extract.posOf x = none := by
  unfold Extract.posOf
  rw [dif_neg]
  rintro ⟨p, hb, he⟩
  exact h p hb he
theorem header_ne_hdr {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 5 ∧ t % 256 ≠ 6 ∧
    t % 256 ≠ 11 ∧ t % 256 ≠ 15) (l tr pos ix : Nat) (p : Extract.Pos) : header t l tr pos ix ≠ p.hdr := by
  obtain ⟨h1, h2, h3, h5, h6, h11, h15⟩ := ht
  cases p <;> simp only [Extract.Pos.hdr] <;> exact Mask.header_ne_of_tag (by omega)
theorem posOf_prefixed_none {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 5 ∧
    t % 256 ≠ 6 ∧ t % 256 ≠ 11 ∧ t % 256 ≠ 15) (x : Digest) (rest : HashInput) (l tr pos ix : Nat) :
    Extract.posOf (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr pos ix) ++ rest)) = none := by
  apply posOf_eq_none
  intro p _ he
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix] at he
  exact header_ne_hdr ht l tr pos ix p (bytesLE_injective he)
theorem posOf_encoding (lay : Layer) (tree leaf : Nat) (message : Digest) (counter : BitVec 32) :
    Extract.posOf (pad64 (encodingInput lay tree leaf message counter)) = none := by
  unfold encodingInput
  exact posOf_prefixed_none (by decide) _ _ _ _ _ _
theorem posOf_digest (rho : Digest) (message : Message) (counter : BitVec 32) :
    Extract.posOf (pad64 (digestInput rho message counter)) = none := by
  unfold digestInput
  exact posOf_prefixed_none (by decide) _ _ _ _ _ _
theorem sat_counterSearch (T : Answers) (lay : Layer) (tree leaf : Nat) (message : Digest) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (counterSearch lay tree leaf message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [SigGolfCandidate.T3.counterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_encoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _
theorem sat_digest (T : Answers) (rho : Digest) (message : Message) (counter : BitVec 32) :
    QueriesSat T (HonestQuery T) (digest rho message counter) :=
  sat_publicHash _ (Or.inl (posOf_digest _ _ _))
theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.digestSearch rho message counter fuel) :=
  ClaudeWCT.WCT9.Wots.Structural.sat_digestSearch_of T _ rho message fun _ => Or.inl (posOf_digest _ _ _)
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 256) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.chain lay tree leaf i start count
      (honestChainValue T lay tree leaf i (leafSeed T lay tree leaf i) start)) := by
  induction count with
  | zero => rw [chain_zero]; exact QueriesSat.pure' _
  | succ count ih =>
      rw [Correctness.chain_add lay tree leaf i start count 1]
      refine QueriesSat.bind (ih (by omega)) ?_
      rw [eval_honestChain]
      intro q hq
      rw [queried_chain_one, List.mem_singleton] at hq
      rw [hq]
      exact honestQuery_honest T (.chain lay tree leaf i (start + count)) ⟨htree, hleaf, hi, by omega⟩
theorem sat_leafHalf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (pair : Nat) (rows : List Digest × List Digest)
    (half : Nat) (hh : half < 2) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (Correctness.leafHalf lay tree leaf digits signatureOnly pair
      (evalWithAnswerFn T (privatePair 0 lay.val tree pair leaf)) rows half) := by
  unfold Correctness.leafHalf
  by_cases hi : chainCount lay ≤ 2 * pair + half
  · simp only [hi, ite_true]
    exact QueriesSat.pure' _
  · simp only [hi, ite_false]
    rw [← Correctness.leafSeed_pair T lay tree leaf pair half hh]
    have hd := hvalid (2 * pair + half) (by omega)
    have hw := Mask.width_le lay (2 * pair + half)
    have hc := Mask.chainCount_le lay
    refine QueriesSat.bind ?_ ?_
    · rw [← honestChainValue_zero T lay tree leaf (2 * pair + half) (leafSeed T lay tree leaf (2 * pair + half))]
      exact sat_chain T lay tree leaf _ 0 _ htree hleaf (by omega) (by omega)
    · change QueriesSat T (HonestQuery T) (if signatureOnly = true then _ else
        (SigGolfCandidate.T3.chain lay tree leaf (2 * pair + half) (digits.getD (2 * pair + half) 0)
          (maxDigit lay (2 * pair + half) - digits.getD (2 * pair + half) 0)
          (honestChainValue T lay tree leaf (2 * pair + half) (leafSeed T lay tree leaf (2 * pair + half))
            (digits.getD (2 * pair + half) 0)) >>= _))
      split
      · exact QueriesSat.pure' _
      · exact QueriesSat.bind (sat_chain T lay tree leaf _ _ _ htree hleaf (by omega) (by omega))
          (QueriesSat.pure' _)
theorem sat_leafRows (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (Correctness.leafRows lay tree leaf digits signatureOnly) := by
  unfold Correctness.leafRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun pair _ rows _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_privatePair T _ _ _ _ _) ?_
  exact QueriesSat.foldlM_range 2 _ (fun _ _ => True) rows trivial (fun half hh rows' _ =>
    ⟨sat_leafHalf T lay tree leaf digits hvalid signatureOnly pair rows' half hh htree hleaf, trivial⟩)
theorem sat_buildLeaf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.buildLeaf lay tree leaf digits signatureOnly) := by
  rw [Correctness.buildLeaf_eq]
  refine QueriesSat.bind (sat_leafRows T lay tree leaf digits hvalid signatureOnly htree hleaf) ?_
  cases signatureOnly
  · have hr := Correctness.eval_leafRows_correct T lay tree leaf digits hvalid false
    have hn : chainCount lay ≤ 2 * ((chainCount lay + 1) / 2) := by omega
    simp only [Correctness.LeafRows, Bool.false_eq_true, ite_false, min_eq_right hn] at hr
    have he := Correctness.list_eq_range_map _ (leafEnd T lay tree leaf) _ hr.1
      (fun i hi => hr.2.2.1 i (by rw [hr.1]; exact hi))
    simp only [Bool.false_eq_true, ite_false]
    refine QueriesSat.bind ?_ (QueriesSat.pure' _)
    rw [he, Extract.leafHash_eq_shortHash]
    exact sat_shortHash _ (honestQuery_honest T (.leaf lay tree leaf) ⟨htree, hleaf⟩)
  · simp only [ite_true]
    exact QueriesSat.pure' _
theorem sat_treeRows (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) :
    QueriesSat T (HonestQuery T) (Correctness.treeRows lay tree selected digits) := by
  unfold Correctness.treeRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun leaf hleaf rows _ => ⟨?_, trivial⟩)
  have hd : Cost.ValidDigits lay (if leaf = selected then digits else []) := by
    split
    · exact hvalid
    · exact Cost.validDigits_nil lay
  have hl : leaf < 2 ^ 32 := by
    have : 2 ^ height lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le lay)
    omega
  refine QueriesSat.bind (sat_buildLeaf T lay tree leaf _ hd false htree hl) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildLeaf lay tree leaf (if leaf = selected then digits else []) false) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.pure' _
theorem honestQuery_treeNode (T : Answers) (lay : Layer) (tree : Nat) (htree : tree < 2 ^ 40) (level node : Nat)
    (hlevel : level < height lay)
    (hnode : node < ((builtTree T lay tree).getD level []).length / 2) :
    HonestQuery T (nodeQuery 3 lay.val tree (2 ^ (height lay - (level + 1)) + node)
      (treeValue (builtTree T lay tree) level (2 * node)) (treeValue (builtTree T lay tree) level (2 * node + 1))) := by
  have hshape := (Correctness.builtTree_correct T lay tree).1
  have hw := hshape.2 level (by omega)
  have hpow : 2 ^ (height lay - level) = 2 * 2 ^ (height lay - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine Or.inr ⟨.node lay tree level node, ⟨htree, hlevel, by rw [hw, hpow] at hnode; omega⟩, ?_⟩
  show pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - (level + 1)) + node) _ 0 _) =
    pad64 (nodeInputP 3 lay.val tree (2 ^ (height lay - level - 1) + node) _ 0 _)
  rw [Nat.sub_sub]
theorem sat_buildTree (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) :
    QueriesSat T (HonestQuery T) (SigGolfCandidate.T3.buildTree lay tree selected digits) := by
  rw [Correctness.buildTree_eq]
  refine QueriesSat.bind (sat_treeRows T lay tree selected digits hvalid htree) ?_
  rw [Correctness.eval_treeRows T lay tree selected digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  apply sat_buildLevels
  intro level hlevel node hnode
  exact honestQuery_treeNode T lay tree htree level node hlevel hnode
theorem honestQuery_of_fts (T : Answers) {index : Nat} (hindex : index < 2 ^ 31) {q : SigGolfCandidate.T3.Spec.Domain}
    (h : ClaudeWCT.WCT9.Wots.FtsHonestQuery T index q) : HonestQuery T q := by
  rcases q with (coin | x) | (tweak | other)
  · exact h.elim
  · obtain ⟨pos, hb, hx⟩ := Extract.ftsHonestQuery_pos hindex h
    exact Or.inr ⟨pos, hb, hx⟩
  · trivial
  · trivial
theorem sat_buildChild (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (coord : ClaudeWCT.WCT9.Coord)
    (child : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.buildChild index coord.val child.val word) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_buildChild T index coord child word).mono fun _ hq =>
    honestQuery_of_fts T hindex hq
theorem sat_buildCoordinate (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (coord : ClaudeWCT.WCT9.Coord)
    (selected : ClaudeWCT.WCT9.Child) (word : ClaudeWCT.WCT9.Rank) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.buildCoordinate index coord selected word) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_buildCoordinate T index coord selected word).mono fun _ hq =>
    honestQuery_of_fts T hindex hq
theorem sat_forestRows (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.forestRows index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_forestRows T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_forestPk (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) :
    QueriesSat T (HonestQuery T)
      (ClaudeWCT.WCT9.forestPk index (List.ofFn (ClaudeWCT.WCT9.coordinateRoot T index))) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_forestPk T index).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 31) (output : HashOutput) :
    QueriesSat T (HonestQuery T) (ClaudeWCT.WCT9.signForest index output) :=
  (ClaudeWCT.WCT9.Wots.Structural.sat_signForest T index output).mono fun _ hq => honestQuery_of_fts T hindex hq
theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTree T 0 0 0 [] (Cost.validDigits_nil 0) (by decide)) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildTree 0 0 0 []) = x
  obtain ⟨levels, values⟩ := x
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)
theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)
theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeaf T 0 0 leaf digits hvalid true (by decide) (by omega)) ?_
  generalize evalWithAnswerFn T (SigGolfCandidate.T3.buildLeaf 0 0 leaf digits true) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.bind (sat_topPath T cache leaf hleaf) (QueriesSat.pure' _)
theorem sat_signLayers (T : Answers) (cache : Cache) (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n msg, QueriesSat T (HonestQuery T) (signLayers cache index n msg) := by
  intro n
  induction n with
  | zero => intro _; exact QueriesSat.pure' _
  | succ n ih =>
      intro msg
      simp only [signLayers]
      refine QueriesSat.bind (sat_counterSearch T _ _ _ _ _ _) ?_
      cases hs : evalWithAnswerFn T (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none => exact QueriesSat.pure' _
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (Correctness.counterSearch_some T _ _ _ msg counterLimit 0 counter digits
            (by decide) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          dsimp only
          split_ifs with hn0
          · subst hn0
            refine QueriesSat.bind (sat_signTop T cache _ digits hvalid ?_) (QueriesSat.pure' _)
            have := route_leaf_bound index (Fin.ofNat 4 0)
            exact this
          · refine QueriesSat.bind (sat_buildTree T _ _ _ digits hvalid (Mask.route_tree_lt index hindex _)) ?_
            refine QueriesSat.bind (ih _) ?_
            generalize evalWithAnswerFn T (signLayers cache index n _) = r
            rcases r with _ | r <;> exact QueriesSat.pure' _
theorem sat_signPayload (T : Answers) (cache : Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (signPayload cache message) := by
  rw [show signPayload cache message = ClaudeWCT.WCT9.Rev3.signPayload cache message from rfl,
    ClaudeWCT.WCT9.Rev3.signPayload_eq]
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_digestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (ClaudeWCT.WCT9.digestSearch (evalWithAnswerFn T (privateNonce message)) message 0
    ClaudeWCT.WCT9.digestAttemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact QueriesSat.pure' _
  · dsimp only
    have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    refine QueriesSat.bind (sat_signForest T _ hindex _) ?_
    refine QueriesSat.bind (sat_signLayers T cache _ hindex 4 _) ?_
    generalize evalWithAnswerFn T (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
    rcases pieces with _ | pieces <;> exact QueriesSat.pure' _
theorem sat_authenticatedSign (T : Answers) (published : SigGolfCandidate.T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _
end ClaudeWCT.W9.T3.Security.Wots.Structural
