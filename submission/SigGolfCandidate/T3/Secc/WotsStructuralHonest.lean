import SigGolfCandidate.T3.Secc.WotsReference
import SigGolfCandidate.T3.Secc.WotsMask
import SigGolfCandidate.T3.Secc.CanonGraphHonest

/-!
# Stream S (1): R3's honest evaluation reads only canonical rows

Every public query that T3's honest programs issue under a table `T` (the offline evaluations R3 performs:
`keygen`, SEC's `FullGame.authenticatedSign`, the reference counter search and the honest roots it reads) is either
unparsed (`Extract.posOf = none`: encoding rows, digest rows) or the honest input `Extract.honestInput T p` at a
bounded position `p` (`HonestQuery`). Under G's `Agrees T labels` such a query is a canonical cell or sits at no
source node, so it is never a *structural row* (a non-cell row at a parsed source position).

`QueriesSat T Q program`: every query of the deterministic run satisfies `Q`, with closure lemmas for `pure`, `bind`,
`foldlM` (with a value invariant) and `mapM`. The value invariants are Core's closed forms (`Correctness.LeafRows`,
`TreeLevels`, `eval_treeRows`, `eval_ftsRows_correct`, `eval_forestRows`); no honest builder body is evaluated, and the
FTS levels are bridged through G's `ftsLevels_built` (never by unfolding `Extract.ftsLevels`).
-/

namespace SigGolfCandidate.T3.Security.Wots.Structural
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue leafRoot)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] SigGolfCandidate.T3.buildFts SigGolfCandidate.T3.buildTree SigGolfCandidate.T3.buildLeaf

/-! ## Query invariants along the deterministic run -/

/-- Every query of the deterministic run of `program` under `T` satisfies `Q`. -/
def QueriesSat (T : Answers) (Q : T3.Spec.Domain → Prop) {α : Type} (program : M α) : Prop :=
  ∀ q ∈ SourceReplay.queried T program, Q q

section QueriesSat
variable {T : Answers} {Q : T3.Spec.Domain → Prop}

theorem QueriesSat.pure' {α : Type} (x : α) : QueriesSat T Q (pure x : M α) := by
  intro q hq
  simp at hq

theorem QueriesSat.bind {α β : Type} {p : M α} {f : α → M β} (hp : QueriesSat T Q p)
    (hf : QueriesSat T Q (f (evalWithAnswerFn T p))) : QueriesSat T Q (p >>= f) := by
  intro q hq
  rw [SourceReplay.queried_bind, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hp q hq
  · exact hf q hq

theorem QueriesSat.map {α β : Type} {p : M α} (f : α → β) (hp : QueriesSat T Q p) : QueriesSat T Q (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact QueriesSat.bind hp (QueriesSat.pure' _)

theorem QueriesSat.query {q : T3.Spec.Domain} (h : Q q) : QueriesSat T Q (liftM (T3.Spec.query q)) := by
  intro q' hq'
  have he : SourceReplay.queried T (liftM (T3.Spec.query q) : M _) = [q] := by
    have := SourceReplay.queried_query_bind T q (fun x => (pure x : M _))
    simpa only [bind_pure, SourceReplay.queried_pure] using this
  rw [he, List.mem_singleton] at hq'
  rw [hq']
  exact h

theorem QueriesSat.foldlM_list {β γ : Type} (items : List β) (f : γ → β → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i (hi : i < items.length) state, Inv i state →
      QueriesSat T Q (f state items[i]) ∧ Inv (i + 1) (evalWithAnswerFn T (f state items[i]))) :
    QueriesSat T Q (items.foldlM f initial) := by
  induction items generalizing Inv initial with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.foldlM_cons]
      obtain ⟨hq, hi⟩ := hs 0 (by simp) initial h0
      refine QueriesSat.bind hq ?_
      exact ih (fun i => Inv (i + 1)) _ hi (fun i hi state hstate => hs (i + 1) (by simp; omega) state hstate)

theorem QueriesSat.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop) (initial : γ)
    (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state i) ∧ Inv (i + 1) (evalWithAnswerFn T (f state i))) :
    QueriesSat T Q ((List.range n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range]
    exact hs i (by simpa using hi) state hstate)

theorem QueriesSat.foldlM_range' {γ : Type} (start n : Nat) (f : γ → Nat → M γ) (Inv : Nat → γ → Prop)
    (initial : γ) (h0 : Inv 0 initial)
    (hs : ∀ i, i < n → ∀ state, Inv i state →
      QueriesSat T Q (f state (start + i)) ∧ Inv (i + 1) (evalWithAnswerFn T (f state (start + i)))) :
    QueriesSat T Q ((List.range' start n).foldlM f initial) :=
  QueriesSat.foldlM_list (List.range' start n) f Inv initial h0 (fun i hi state hstate => by
    simp only [List.getElem_range', Nat.one_mul]
    exact hs i (by simpa using hi) state hstate)

theorem QueriesSat.mapM {α β : Type} (items : List α) (f : α → M β) (hf : ∀ x ∈ items, QueriesSat T Q (f x)) :
    QueriesSat T Q (items.mapM f) := by
  induction items with
  | nil => exact QueriesSat.pure' _
  | cons x xs ih =>
      rw [List.mapM_cons]
      exact QueriesSat.bind (hf x List.mem_cons_self) (QueriesSat.bind
        (ih fun y hy => hf y (List.mem_cons_of_mem x hy)) (QueriesSat.pure' _))

theorem QueriesSat.mono {α : Type} {Q' : T3.Spec.Domain → Prop} {p : M α} (hp : QueriesSat T Q p)
    (h : ∀ q, Q q → Q' q) : QueriesSat T Q' p := fun q hq => h q (hp q hq)

end QueriesSat

theorem queried_shortHash' (T : Answers) (input : HashInput) :
    SourceReplay.queried T (shortHash input) = [.inl (.inr (pad64 input))] := rfl

theorem sat_shortHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (shortHash input) := by
  intro q hq
  rw [queried_shortHash', List.mem_singleton] at hq
  rw [hq]
  exact h

theorem sat_publicHash {T : Answers} {Q : T3.Spec.Domain → Prop} (input : HashInput)
    (h : Q (.inl (.inr (pad64 input)))) : QueriesSat T Q (publicHash input) :=
  QueriesSat.query h

/-! ## Honest queries -/

/-- An honest query under `T`: a coin, a private coordinate, or a public input that is unparsed or the honest input at
a bounded position. -/
def HonestQuery (T : Answers) : T3.Spec.Domain → Prop
  | .inl (.inr x) => Extract.posOf x = none ∨ ∃ p : Extract.Pos, p.Bounded ∧ x = Extract.honestInput T p
  | _ => True

theorem honestQuery_private (T : Answers) (c : Coordinate) : HonestQuery T (.inr c) := trivial

theorem honestQuery_honest (T : Answers) (p : Extract.Pos) (hp : p.Bounded) :
    HonestQuery T (.inl (.inr (Extract.honestInput T p))) := Or.inr ⟨p, hp, rfl⟩

theorem sat_privateHash (T : Answers) (c : Coordinate) :
    QueriesSat T (HonestQuery T) (T3.privateHash c) :=
  QueriesSat.query (honestQuery_private T c)

theorem sat_privatePair (T : Answers) (tag lay tree position index : Nat) :
    QueriesSat T (HonestQuery T) (T3.privatePair tag lay tree position index) := by
  unfold T3.privatePair
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)

theorem sat_mask (T : Answers) (level index : Nat) : QueriesSat T (HonestQuery T) (T3.mask level index) := by
  unfold T3.mask T3.pairedMask
  exact QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)

theorem sat_privateMac (T : Answers) (region : Region) : QueriesSat T (HonestQuery T) (T3.privateMac region) := by
  unfold T3.privateMac T3.privateMacKey
  exact QueriesSat.bind (QueriesSat.bind (sat_privateHash T _) (QueriesSat.bind
    (sat_privateHash T _) (QueriesSat.pure' _))) (QueriesSat.pure' _)

theorem sat_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    QueriesSat T (HonestQuery T) (T3.maskedLevel nodes level) := by
  unfold T3.maskedLevel T3.pairedMask
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun _ _ =>
    QueriesSat.bind (sat_privatePair T _ _ _ _ _) (QueriesSat.pure' _)) (QueriesSat.pure' _)

theorem sat_privateNonce (T : Answers) (message : Message) :
    QueriesSat T (HonestQuery T) (T3.privateNonce message) := by
  unfold T3.privateNonce
  exact QueriesSat.bind (sat_privateHash T _) (QueriesSat.pure' _)

/-! ### Unparsed inputs: encoding rows (tag 4) and digest rows (tag 12) -/

theorem posOf_eq_none {x : HashInput}
    (h : ∀ p : Extract.Pos, p.Bounded →
      Extract.canonicalHeader (Extract.hdrBlock x) ≠ bytesLE 16 p.hdr) : Extract.posOf x = none := by
  unfold Extract.posOf
  rw [dif_neg]
  rintro ⟨p, hb, he⟩
  exact h p hb he

/-- A header with a tag outside `{1, 2, 3, 9, 10, 11}` is no position header. -/
theorem header_ne_hdr {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 9 ∧ t % 256 ≠ 10 ∧
    t % 256 ≠ 11) (l tr pos ix : Nat) (p : Extract.Pos) : header t l tr pos ix ≠ p.hdr := by
  obtain ⟨h1, h2, h3, h9, h10, h11⟩ := ht
  cases p with
  | chain lay tree leaf i step => exact (chainHeader_ne_header lay tree leaf i step t l tr pos ix).symm
  | _ => simp only [Extract.Pos.hdr]; exact Mask.header_ne_of_tag (by omega)

theorem posOf_prefixed_none {t : Nat} (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 9 ∧
    t % 256 ≠ 10 ∧ t % 256 ≠ 11) (x : Digest) (rest : HashInput) (l tr pos ix : Nat) :
    Extract.posOf (pad64 (bytesLE 16 x ++ bytesLE 16 (header t l tr pos ix) ++ rest)) = none := by
  apply posOf_eq_none
  intro p _ he
  rw [Extract.hdrBlock_pad64 _ (by simp only [List.length_append, bytesLE_length]; omega),
    Extract.hdrBlock_prefix,
    Extract.canonicalHeader_marker_ne _ (by rw [header_firstByte]; decide)] at he
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
      simp only [T3.counterSearch]
      refine QueriesSat.bind (sat_shortHash _ (Or.inl (posOf_encoding _ _ _ _ _))) ?_
      split
      · exact ih _
      · exact QueriesSat.pure' _

theorem sat_digest (T : Answers) (rho : Digest) (message : Message) (counter : BitVec 32) :
    QueriesSat T (HonestQuery T) (digest rho message counter) :=
  sat_publicHash _ (Or.inl (posOf_digest _ _ _))

theorem sat_digestSearch (T : Answers) (rho : Digest) (message : Message) :
    ∀ fuel counter, QueriesSat T (HonestQuery T) (digestSearch rho message counter fuel) := by
  intro fuel
  induction fuel with
  | zero => intro counter; exact QueriesSat.pure' _
  | succ fuel ih =>
      intro counter
      simp only [T3.digestSearch]
      refine QueriesSat.bind (sat_digest T _ _ _) ?_
      split
      · exact QueriesSat.pure' _
      · exact ih _

/-! ### Chains -/

private theorem canonicalHeader_low (hdr : Digest) :
    (Extract.canonicalHeader (bytesLE 16 hdr)).take 8 = bytesLE 8 (hdr.extractLsb' 0 64) := by
  have he : hdr = hdr.extractLsb' 64 64 ++ hdr.extractLsb' 0 64 :=
    (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := hdr)).symm
  conv_lhs => rw [he, Extract.bytesLE_header_words]
  unfold Extract.canonicalHeader
  split_ifs <;> simp [List.take_append, bytesLE_length]

private theorem low_ne_of_firstByte (x y : BitVec 128)
    (hc : 128 ≤ x.toNat % 256) (hr : y.toNat % 256 = 1) :
    x.extractLsb' 0 64 ≠ y.extractLsb' 0 64 := by
  intro he
  have hv := congrArg BitVec.toNat he
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one] at hv
  omega

private theorem chain_low_ne_header (lay : Layer) (tree leaf i step tag roleLay roleTree pos ix : Nat) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 ≠
      (header tag roleLay roleTree pos ix).extractLsb' 0 64 :=
  low_ne_of_firstByte _ _ (chainHeader_firstByte lay tree leaf i step)
    (header_firstByte tag roleLay roleTree pos ix)

/-- Source-only spill coordinates are not graph positions, even after witness-pad normalization. -/
theorem posOf_chain_offgraph (lay : Layer) (tree leaf i step : Nat) (value : Digest)
    (hoff : chainHeaderSpill tree leaf i step ≠ 0) :
    Extract.posOf (pad64 (chainInput lay tree leaf i step value)) = none := by
  apply posOf_eq_none
  intro p hb he
  rw [chainInput_padded, Extract.hdrBlock, chainInput_header] at he
  have hn := congrArg (List.take 8) he
  rw [canonicalHeader_low] at hn
  have hp : (bytesLE 16 p.hdr).take 8 = bytesLE 8 (p.hdr.extractLsb' 0 64) := by
    rw [← Extract.Pos.canonicalHeader_eq hb]
    exact canonicalHeader_low _
  rw [hp] at hn
  have hlo := bytesLE_injective hn
  cases p with
  | chain lay' tree' leaf' i' step' =>
      exact chainHeader_offgraph_low_ne hoff hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hlo
  | _ => exact chain_low_ne_header _ _ _ _ _ _ _ _ _ _ hlo

theorem chain_zero (lay : Layer) (tree leaf i start : Nat) (v : Digest) :
    chain lay tree leaf i start 0 v = pure v := rfl

theorem queried_chain_one (T : Answers) (lay : Layer) (tree leaf i s : Nat) (v : Digest) :
    SourceReplay.queried T (chain lay tree leaf i s 1 v) = [.inl (.inr (pad64 (chainInput lay tree leaf i s v)))] := rfl

theorem eval_honestChain (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) (start count : Nat) :
    evalWithAnswerFn T (chain lay tree leaf i start count (honestChainValue T lay tree leaf i seed start)) =
      honestChainValue T lay tree leaf i seed (start + count) := by
  unfold honestChainValue
  rw [Correctness.eval_chain_add]
  simp only [Nat.zero_add]

theorem honestChainValue_zero (T : Answers) (lay : Layer) (tree leaf i : Nat) (seed : Digest) :
    honestChainValue T lay tree leaf i seed 0 = seed := rfl

/-- A chain run from the honest value at `start`, at a bounded address, issues only honest chain rows. -/
theorem sat_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat)
    (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) (hi : i < 2 ^ 24) (hcount : start + count ≤ 256) :
    QueriesSat T (HonestQuery T) (T3.chain lay tree leaf i start count
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
      by_cases hoff : chainHeaderSpill tree leaf i (start + count) = 0
      · have hg : tree < 2^31 ∧ leaf < 4096 ∧ i < 64 ∧ start + count < 8 := by
          unfold chainHeaderSpill at hoff
          omega
        exact honestQuery_honest T (.chain lay tree leaf i (start + count)) hg
      · exact Or.inl (posOf_chain_offgraph lay tree leaf i (start + count) _ hoff)

/-! ### Leaves -/

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
        (T3.chain lay tree leaf (2 * pair + half) (digits.getD (2 * pair + half) 0)
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

/-- The honest leaf builder (any valid word) issues only honest chain rows and the honest leaf-pk input. -/
theorem sat_buildLeaf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (signatureOnly : Bool) (htree : tree < 2 ^ 40) (hleaf : leaf < 2 ^ 32) :
    QueriesSat T (HonestQuery T) (T3.buildLeaf lay tree leaf digits signatureOnly) := by
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

/-! ### Merkle levels -/

/-- The query of one node hash (`nodeHash_eq_shortHash`). -/
def nodeQuery (tag lay tree heap : Nat) (left right : Digest) : T3.Spec.Domain :=
  .inl (.inr (pad64 (nodeInputP tag lay tree heap left 0 right)))

theorem sat_nodeHash {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree heap : Nat) (left right : Digest)
    (h : Q (nodeQuery tag lay tree heap left right)) : QueriesSat T Q (T3.nodeHash tag lay tree heap left right) := by
  rw [nodeHash_eq_shortHash]
  exact sat_shortHash _ h

theorem sat_buildLevel {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h level : Nat)
    (nodes : List Digest)
    (hq : ∀ i, i < nodes.length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - level) + i) (nodes.getD (2 * i) 0) (nodes.getD (2 * i + 1) 0))) :
    QueriesSat T Q (T3.buildLevel tag lay tree h level nodes) := by
  unfold T3.buildLevel
  exact QueriesSat.mapM _ _ (fun i hi => sat_nodeHash _ _ _ _ _ _ (hq i (List.mem_range.mp hi)))

/-- One step of the `buildLevels` fold. -/
def levelsStep (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) : M (List (List Digest)) := do
  let nodes ← T3.buildLevel tag lay tree h level (levels.getD (level - 1) [])
  pure (levels ++ [nodes])

/-- The first `n` levels of `buildLevels`. -/
def levelsFold (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) : M (List (List Digest)) :=
  (List.range' 1 n).foldlM (levelsStep tag lay tree h) [leaves]

theorem buildLevels_eq_fold (tag lay tree h : Nat) (leaves : List Digest) :
    T3.buildLevels tag lay tree h leaves = levelsFold tag lay tree h leaves h := rfl

theorem eval_levelsStep (T : Answers) (tag lay tree h : Nat) (levels : List (List Digest)) (level : Nat) :
    evalWithAnswerFn T (levelsStep tag lay tree h levels level) =
      levels ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h level (levels.getD (level - 1) []))] := by
  simp only [levelsStep, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

/-- The level fold only appends. -/
theorem eval_levelsSteps_append (T : Answers) (tag lay tree h : Nat) (levels : List Nat) :
    ∀ state : List (List Digest), ∃ extra,
      evalWithAnswerFn T (levels.foldlM (levelsStep tag lay tree h) state) = state ++ extra := by
  induction levels with
  | nil => intro state; exact ⟨[], by simp⟩
  | cons x xs ih =>
      intro state
      rw [List.foldlM_cons, evalWithAnswerFn_bind, eval_levelsStep]
      obtain ⟨extra, he⟩ := ih (state ++ [evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))])
      exact ⟨[evalWithAnswerFn T (T3.buildLevel tag lay tree h x (state.getD (x - 1) []))] ++ extra,
        by rw [he, List.append_assoc]⟩

theorem levelsFold_succ (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    levelsFold tag lay tree h leaves (n + 1) =
      (levelsFold tag lay tree h leaves n >>= fun state => levelsStep tag lay tree h state (1 + n)) := by
  unfold levelsFold
  rw [List.range'_concat, List.foldlM_append]
  simp only [Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]

theorem levelsFold_length (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n : Nat) :
    (evalWithAnswerFn T (levelsFold tag lay tree h leaves n)).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [levelsFold_succ, evalWithAnswerFn_bind, eval_levelsStep, List.length_append, ih]
      simp

theorem levelsFold_prefix (T : Answers) (tag lay tree h : Nat) (leaves : List Digest) (n m : Nat) (hnm : n ≤ m) :
    ∃ extra, evalWithAnswerFn T (levelsFold tag lay tree h leaves m) =
      evalWithAnswerFn T (levelsFold tag lay tree h leaves n) ++ extra := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold levelsFold
  rw [← List.range'_append_1, List.foldlM_append, evalWithAnswerFn_bind]
  exact eval_levelsSteps_append T tag lay tree h _ _

/-- **Merkle levels**: every node query of `buildLevels` hashes two children of the *final* levels `R`. -/
theorem sat_buildLevels {T : Answers} {Q : T3.Spec.Domain → Prop} (tag lay tree h : Nat)
    (leaves : List Digest)
    (hq : ∀ level, level < h → ∀ node,
      node < ((evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)).getD level []).length / 2 →
      Q (nodeQuery tag lay tree (2 ^ (h - (level + 1)) + node)
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node))
        (treeValue (evalWithAnswerFn T (T3.buildLevels tag lay tree h leaves)) level (2 * node + 1)))) :
    QueriesSat T Q (T3.buildLevels tag lay tree h leaves) := by
  rw [buildLevels_eq_fold] at hq ⊢
  unfold levelsFold
  refine QueriesSat.foldlM_range' 1 h _
    (fun i state => state = evalWithAnswerFn T (levelsFold tag lay tree h leaves i)) _ rfl ?_
  intro i hi state hstate
  subst hstate
  refine ⟨?_, ?_⟩
  · unfold levelsStep
    refine QueriesSat.bind (sat_buildLevel _ _ _ _ _ _ ?_) (QueriesSat.pure' _)
    intro node hnode
    have hlen := levelsFold_length T tag lay tree h leaves i
    obtain ⟨extra, hext⟩ := levelsFold_prefix T tag lay tree h leaves i h (by omega)
    have hget : (evalWithAnswerFn T (levelsFold tag lay tree h leaves h)).getD i [] =
        (evalWithAnswerFn T (levelsFold tag lay tree h leaves i)).getD i [] := by
      rw [hext, List.getD_append _ _ _ _ (by omega)]
    have h1 : 1 + i - 1 = i := by omega
    have h2 : h - (1 + i) = h - (i + 1) := by omega
    rw [h1] at hnode ⊢
    rw [h2]
    have := hq i hi node (by rw [hget]; exact hnode)
    simpa only [treeValue, hget] using this
  · rw [levelsFold_succ, evalWithAnswerFn_bind]

/-! ### Hypertree trees -/

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
  generalize evalWithAnswerFn T (T3.buildLeaf lay tree leaf (if leaf = selected then digits else []) false) = x
  obtain ⟨root, values⟩ := x
  exact QueriesSat.pure' _

/-- Honest Merkle-node queries of a bounded tree are its honest node inputs. -/
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

/-- **The honest tree builder** (any selected leaf, valid word) issues only honest queries. -/
theorem sat_buildTree (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) (htree : tree < 2 ^ 40) :
    QueriesSat T (HonestQuery T) (T3.buildTree lay tree selected digits) := by
  rw [Correctness.buildTree_eq]
  refine QueriesSat.bind (sat_treeRows T lay tree selected digits hvalid htree) ?_
  rw [Correctness.eval_treeRows T lay tree selected digits hvalid]
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  apply sat_buildLevels
  intro level hlevel node hnode
  exact honestQuery_treeNode T lay tree htree level node hlevel hnode

/-! ### FTS trees and the forest -/

theorem sat_ftsRows (T : Answers) (index coord : Nat) (hindex : index < 2 ^ 40) (hcoord : coord < 256) :
    QueriesSat T (HonestQuery T) (Correctness.ftsRows index coord) := by
  unfold Correctness.ftsRows
  refine QueriesSat.foldlM_range _ _ (fun _ _ => True) _ trivial (fun pair hpair state _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_privatePair T _ _ _ _ _) ?_
  generalize hp : evalWithAnswerFn T (T3.privatePair 8 coord index 0 pair) = lr
  obtain ⟨left, right⟩ := lr
  have hleft : left = CanonGraph.ftsSecretNat T index coord (2 * pair) := by
    unfold CanonGraph.ftsSecretNat
    rw [show 2 * pair / 2 = pair by omega, if_pos (by omega), hp]
  have hright : right = CanonGraph.ftsSecretNat T index coord (2 * pair + 1) := by
    unfold CanonGraph.ftsSecretNat
    rw [show (2 * pair + 1) / 2 = pair by omega, if_neg (by omega), hp]
  have hleaf : ∀ leaf secret, leaf < 2048 → secret = CanonGraph.ftsSecretNat T index coord leaf →
      QueriesSat T (HonestQuery T) (ftsLeaf index coord leaf secret) := by
    intro leaf secret hl hs
    rw [ftsLeaf_eq_shortHash]
    refine sat_shortHash _ (Or.inr ⟨.ftsLeaf index coord leaf, ⟨hcoord, hindex, by omega⟩, ?_⟩)
    show pad64 (ftsLeafInputP index coord leaf 0 secret 0) =
      pad64 (ftsLeafInputP index coord leaf 0 (Extract.ftsSecret T index coord leaf) 0)
    rw [CanonGraph.ftsSecret_nat T index coord leaf hl, hs]
  exact QueriesSat.bind (hleaf _ _ (by omega) hleft) (QueriesSat.bind (hleaf _ _ (by omega) hright)
    (QueriesSat.pure' _))

/-- The honest FTS tree builder issues only honest FTS leaf and node inputs. -/
theorem sat_buildFts (T : Answers) (index coord : Nat) (hindex : index < 2 ^ 40) (hcoord : coord < 7) :
    QueriesSat T (HonestQuery T) (buildFts index coord) := by
  rw [Correctness.buildFts_eq]
  refine QueriesSat.bind (sat_ftsRows T index coord hindex (by omega)) ?_
  refine QueriesSat.bind ?_ (QueriesSat.pure' _)
  have hrows := Correctness.eval_ftsRows_correct T index coord
  have hlevels := Correctness.eval_buildLevels_correct T 10 coord index 11
    (evalWithAnswerFn T (Correctness.ftsRows index coord)).1 (by rw [hrows.1]; rfl)
  have hR : evalWithAnswerFn T (T3.buildLevels 10 coord index 11 (evalWithAnswerFn T (Correctness.ftsRows index coord)).1) =
      (evalWithAnswerFn T (buildFts index coord)).1 := by
    rw [Correctness.buildFts_eq]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  apply sat_buildLevels
  intro level hlevel node hnode
  have hw := hlevels.1.2 level (by omega)
  have hpow : 2 ^ (11 - level) = 2 * 2 ^ (11 - level - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hw, hpow] at hnode
  have hnode' : node < 2 ^ (11 - level - 1) := by omega
  refine Or.inr ⟨.ftsNode index coord level node, ⟨by omega, hindex, hlevel, hnode'⟩, ?_⟩
  show pad64 (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node) _ 0 _) =
    pad64 (nodeInputP 10 coord index (2 ^ (11 - level - 1) + node)
      (treeValue (Extract.ftsLevels T index coord) level (2 * node)) 0
      (treeValue (Extract.ftsLevels T index coord) level (2 * node + 1)))
  rw [CanonGraph.ftsLevels_built T index coord level (2 * node) hlevel (by omega),
    CanonGraph.ftsLevels_built T index coord level (2 * node + 1) hlevel (by omega), hR, Nat.sub_sub]

theorem sat_signForest (T : Answers) (index : Nat) (hindex : index < 2 ^ 40) (chosen : List Selection) :
    QueriesSat T (HonestQuery T) (Correctness.signForest index chosen) := by
  unfold Correctness.signForest
  refine QueriesSat.foldlM_range 7 _ (fun _ _ => True) _ trivial (fun coord hc state _ => ⟨?_, trivial⟩)
  refine QueriesSat.bind (sat_buildFts T index coord hindex hc) ?_
  generalize evalWithAnswerFn T (buildFts index coord) = x
  obtain ⟨levels, secrets⟩ := x
  exact QueriesSat.pure' _

/-- The honest forest pk query (over the honest FTS roots) is the honest forest input. -/
theorem sat_forestPk (T : Answers) (index : Nat) (hindex : index < 2 ^ 40) :
    QueriesSat T (HonestQuery T) (forestPk index (Correctness.forestRoots T index 7)) := by
  rw [Extract.forestPk_eq_shortHash]
  refine sat_shortHash _ (Or.inr ⟨.forest index, hindex, ?_⟩)
  show pad64 (Extract.forestInput index (Correctness.forestRoots T index 7)) =
    pad64 (Extract.forestInput index (Extract.ftsRootsHonest T index))
  rw [CanonGraph.ftsRoots_built]
  rfl

/-! ### Key generation -/

theorem sat_keygenPayload (T : Answers) : QueriesSat T (HonestQuery T) keygenPayload := by
  rw [Correctness.keygenPayload_eq]
  unfold Correctness.cachePayloadProgram
  refine QueriesSat.bind (sat_buildTree T 0 0 0 [] (Cost.validDigits_nil 0) (by decide)) ?_
  generalize evalWithAnswerFn T (T3.buildTree 0 0 0 []) = x
  obtain ⟨levels, values⟩ := x
  exact QueriesSat.bind (QueriesSat.mapM _ _ fun level _ => sat_maskedLevel T _ _) (QueriesSat.pure' _)

/-- **Honest key generation issues only honest queries.** -/
theorem sat_keygen (T : Answers) : QueriesSat T (HonestQuery T) keygen := by
  unfold keygen
  refine QueriesSat.bind (sat_keygenPayload T) ?_
  generalize evalWithAnswerFn T keygenPayload = x
  obtain ⟨publicKey, region⟩ := x
  exact QueriesSat.bind (sat_privateMac T _) (QueriesSat.pure' _)

/-! ### Signing -/

theorem sat_topPath (T : Answers) (cache : Cache) (leaf : Nat) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (topPath cache leaf) := by
  unfold topPath
  exact QueriesSat.mapM _ _ fun level _ => QueriesSat.bind (sat_mask T _ _) (QueriesSat.pure' _)

theorem sat_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits 0 digits) (hleaf : leaf < 4096) :
    QueriesSat T (HonestQuery T) (signTop cache leaf digits) := by
  unfold signTop
  refine QueriesSat.bind (sat_buildLeaf T 0 0 leaf digits hvalid true (by decide) (by omega)) ?_
  generalize evalWithAnswerFn T (T3.buildLeaf 0 0 leaf digits true) = x
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

/-- **The honest payload signer issues only honest queries** (any cache, any message). -/
theorem sat_signPayload (T : Answers) (cache : Cache) (message : Message) :
    QueriesSat T (HonestQuery T) (signPayload cache message) := by
  rw [Correctness.signPayload_eq]
  refine QueriesSat.bind (sat_privateNonce T message) ?_
  refine QueriesSat.bind (sat_digestSearch T _ _ _ _) ?_
  generalize evalWithAnswerFn T (digestSearch (evalWithAnswerFn T (privateNonce message)) message 0 attemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · exact QueriesSat.pure' _
  · dsimp only
    have hindex : output.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
    refine QueriesSat.bind (sat_signForest T _ (by omega) _) ?_
    rw [Correctness.eval_signForest]
    dsimp only
    refine QueriesSat.bind (sat_forestPk T _ (by omega)) ?_
    refine QueriesSat.bind (sat_signLayers T cache _ hindex 4 _) ?_
    generalize evalWithAnswerFn T (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
    rcases pieces with _ | pieces <;> exact QueriesSat.pure' _

/-- **SEC's authenticated signer issues only honest queries.** -/
theorem sat_authenticatedSign (T : Answers) (published : T3.Cache) (request : Request) :
    QueriesSat T (HonestQuery T) (FullGame.authenticatedSign published request) := by
  unfold FullGame.authenticatedSign
  refine QueriesSat.bind (sat_privateMac T _) ?_
  split
  · exact sat_signPayload T _ _
  · exact QueriesSat.pure' _

end SigGolfCandidate.T3.Security.Wots.Structural
