import SigGolfCandidate.Equiv.Verify
import SigGolfCandidate.Equiv.Sched

/-!
# Expansion (PORS+FP, counters recomputed)

* `expandRef_eq`: the reference expansion is the relabelled abstract expansion `aExpand`
  (`expandLayers_eq`: the counter phase, from `searchCounter_eq`, `verifyLeaf_eq`, `foldPath_eq`).
* `witOf_compress` / `aExpand_compress` (relation R2): every successful expansion decodes
  (`witSig`/`witDec`) to a signature that compresses back to the input, whatever its counters.
* `expandOf_honest` (relation R4): an honest-shaped signature (the honest opening of admissible leaves)
  expands to a partial witness that decodes to the signature itself with zero counters and, with any
  counters written (`Ref.withCounters`), to the signature with those counters.
* `padOf_of_mem_support_aExpand_relabel`: every witness the abstract expansion outputs has zero W1a pads.

The witness layout lemmas are stated for `witOf sig v vs segs cs = Ref.withCounters (Ref.witnessBody
sig v vs segs) cs` (the W1a partial witness, 16384 bytes, with the counters `cs` written at
`Ref.ctrOff`): the partial witness `Ref.witnessList` is `cs = []` (`witnessList_withCounters_nil`).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message Signature LayerSignature)
open SphincsSecurity.Concrete (sequenceFin treeIndexAt leafIndexAt encodingSearch recoverChain leafHash
  treeFold signaturePath)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## The counter phase and the whole expansion -/

/-- **The counter phase**: on any 16384-byte partial witness, the reference counter phase is the
relabelled abstract one (`searchCounter_eq`, `verifyLeaf_eq`, `foldPath_eq`). -/
theorem expandLayers_eq (wl : List Byte) (hl : wl.length = 16384) (index : Index) (n : Nat)
    (hn : n ≤ 5) (M : Digest) :
    Ref.expandLayers wl index n (dv M) = relabel fmtQ (aLayers index (witSig wl) n M) := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n ih =>
  match n, hn with
  | 0, _ => simp [Ref.expandLayers, aLayers]
  | 1, _ =>
    let lay : Layer := ⟨0, by decide⟩
    have hr := route_eq index lay
    simp only [lay] at hr
    have hs := searchCounter_eq lay (treeIndexAt index lay) (leafIndexAt index lay) M Ref.cMax 0
      (by decide)
    simp only [lay, Fin.val_mk] at hs
    unfold Ref.expandLayers aLayers
    simp only [hr]
    rw [hs, show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
    rcases r with _ | ⟨c, enc⟩ <;> rfl
  | k + 2, hk =>
    let lay : Layer := ⟨k + 1, by show k + 1 < 5; omega⟩
    have hr := route_eq index lay
    simp only [lay] at hr
    have hs := searchCounter_eq lay (treeIndexAt index lay) (leafIndexAt index lay) M Ref.cMax 0
      (by decide)
    simp only [lay, Fin.val_mk] at hs
    unfold Ref.expandLayers aLayers
    rw [dif_pos (show k + 1 < SphincsSecurity.numLayers by show k + 1 < 5; omega)]
    simp only [hr]
    rw [hs, show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
    rcases r with _ | ⟨c, enc⟩
    · rfl
    · have hv := verifyLeaf_eq wl hl lay (treeIndexAt index lay) (leafIndexAt index lay) enc
      have hp := witPath_eq wl hl lay
      simp only [lay] at hv hp
      simp only [Option.map_some]
      rw [hv]
      simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun ends => ?_
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun v => ?_
      rw [hp]
      have hfold := foldPath_eq (Ref.nodeInput lay (treeIndexAt index lay))
        (fun lam j l r => SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
          (.node lay (treeIndexAt index lay) lam j) (SphincsSecurity.Concrete.nodePayload l r))
        (hash16_node lay _) (leafIndexAt index lay) (signaturePath (witSig wl) lay)
        (fun k v => treeFold (m := AComp) 0 lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath (witSig wl) lay) k v)
        (fun v => rfl) (fun l v => rfl) (SphincsSecurity.layerHeight lay) v
      rw [hfold, bind_map_left]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun root => ?_
      rw [ih (k + 1) (by omega) (by omega) root]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
      rcases r with _ | cs <;> rfl

/-- **expand**: the reference expansion is the relabelled abstract expansion (any abstract key). -/
theorem expandRef_eq (m : Bytes 32) (pk : Bytes 16) (pk' : SphincsSecurity.PublicKey)
    (σ : Bytes 6032) :
    Ref.expandRef m pk σ = relabel fmtQ (aExpand m pk' σ) := by
  have hr : dv (Ref.ofList 16 (Ref.sigRho (Ref.toList σ))) = Ref.sigRho (Ref.toList σ) :=
    Ref.toList_ofList 16 _ (by simp [Ref.sigRho, Ref.slice, Ref.length_toList])
  have hσ : (Ref.toList σ).length = Ref.sigBytes := Ref.length_toList σ
  unfold Ref.expandRef Ref.expandList aExpand
  rw [← hr, digest_eq pk'.root _ m]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, bind_assoc, pure_bind]
  rw [show Ref.ofList 16 (dv (Ref.ofList 16 (Ref.sigRho (Ref.toList σ)))) =
    Ref.ofList 16 (Ref.sigRho (Ref.toList σ)) from Ref.ofList_toList _]
  refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun d => ?_
  cases hx : Ref.expandOf (Ref.toList σ) d.toNat with
  | none => simp
  | some w0 =>
    have hl : w0.length = 16384 := Ref.length_of_expandOf _ hσ _ _ hx
    simp only
    rw [idxOf_eq, leavesOf_eq, porsRoot_eq _ _ hl, bind_map_left]
    simp only [relabel_bind, bind_assoc]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
    rcases r with _ | M
    · simp
    · simp only [Option.map_some]
      rw [show Ref.nLayers = SphincsSecurity.numLayers from rfl,
        expandLayers_eq w0 hl _ SphincsSecurity.numLayers (le_refl 5)]
      simp only [relabel_bind, bind_assoc]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
      rcases r with _ | cs <;> simp

/-! ## Generic list facts -/

theorem getD_append_right'' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_append_left'' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wbytes_eq_slice (w : List Byte) (q n : Nat) (h : q + n ≤ w.length) :
    Ref.wbytes w q n = Ref.slice w q n := by
  apply List.ext_getElem
  · simp [Ref.wbytes, Ref.slice]; omega
  · intro i h1 h2
    simp only [Ref.wbytes, Ref.slice, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp [Ref.wbytes] at h1; omega)]
    rfl

theorem slice_slice (l : List Byte) (a n b m : Nat) (h : b + m ≤ n) :
    Ref.slice (Ref.slice l a n) b m = Ref.slice l (a + b) m := by
  simp only [Ref.slice, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-- The auth-count prefix sums of segment bytes: `sum_{i < j} (bs_i mod 16)`. -/
def asum (bs : List Nat) (j : Nat) : Nat := ((bs.take j).map (· % 16)).sum

theorem asum_succ (bs : List Nat) (j : Nat) (hj : j < bs.length) :
    asum bs (j + 1) = asum bs j + bs.getD j 0 % 16 := by
  simp only [asum, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.getD_eq_getElem?_getD, Option.getD_some, Nat.add_zero]

theorem asum_mono (bs : List Nat) {j k : Nat} (h : j ≤ k) : asum bs j ≤ asum bs k := by
  unfold asum
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem asum_length (bs : List Nat) : asum bs bs.length = (bs.map (· % 16)).sum := by
  simp [asum]

/-! ## The segment stream -/

/-- The stream of `Ref.segStream` from auth item `r` on. -/
def streamAux (sig : List Byte) : Nat → List Nat → List Byte
  | _, [] => []
  | r, b :: bs => [Ref.byte b] ++ Ref.zeros 7 ++
      ((List.range (b % 16)).map fun i => Ref.sigAuth sig (r + i)).flatten ++ streamAux sig (r + b % 16) bs

theorem foldl_streamStep (sig : List Byte) : ∀ (bs : List Nat) (acc : List Byte) (r : Nat),
    bs.foldl (Ref.streamStep sig) (acc, r) = (acc ++ streamAux sig r bs, r + (bs.map (· % 16)).sum)
  | [], acc, r => by simp [streamAux]
  | b :: bs, acc, r => by
    rw [List.foldl_cons]
    have e : Ref.streamStep sig (acc, r) b = (acc ++ [Ref.byte b] ++ Ref.zeros 7 ++
        ((List.range (b % 16)).map fun i => Ref.sigAuth sig (r + i)).flatten, r + b % 16) := rfl
    rw [e, foldl_streamStep sig bs]
    simp [streamAux, List.append_assoc, Nat.add_assoc]

theorem segStream_eq (sig : List Byte) (segs : List Nat) :
    Ref.segStream sig segs = streamAux sig 0 segs := by
  unfold Ref.segStream
  rw [foldl_streamStep]
  simp

section stream
variable (sig : List Byte) (hsig : sig.length = 6032)
include hsig

theorem length_sigAuth (k : Nat) (hk : k < 117) : (Ref.sigAuth sig k).length = 16 := by
  unfold Ref.sigAuth Ref.sigItem
  exact length_slice _ _ _ (by rw [hsig]; unfold Ref.porsK; omega)

theorem length_chunk (r a : Nat) (h : r + a ≤ 117) :
    ((List.range a).map fun i => Ref.sigAuth sig (r + i)).flatten.length = 16 * a := by
  rw [map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigAuth sig hsig _ (by omega))]

theorem length_streamAux : ∀ (bs : List Nat) (r : Nat), r + (bs.map (· % 16)).sum ≤ 117 →
    (streamAux sig r bs).length = 8 * bs.length + 16 * (bs.map (· % 16)).sum
  | [], r, _ => by simp [streamAux]
  | b :: bs, r, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [streamAux, List.length_append, List.length_singleton, Ref.length_zeros,
      length_chunk sig hsig r (b % 16) (by omega),
      length_streamAux bs (r + b % 16) (by omega), List.length_cons, List.map_cons, List.sum_cons,
      List.length_nil]
    ring

theorem getD_streamAux : ∀ (bs : List Nat) (r j : Nat), r + (bs.map (· % 16)).sum ≤ 117 →
    j < bs.length →
    (streamAux sig r bs).getD (8 * j + 16 * asum bs j) 0 = Ref.byte (bs.getD j 0)
  | [], r, j, _, hj => by simp at hj
  | b :: bs, r, j, h, hj => by
    simp only [List.map_cons, List.sum_cons] at h
    cases j with
    | zero => simp [streamAux, asum]
    | succ j =>
      have ha : asum (b :: bs) (j + 1) = b % 16 + asum bs j := by simp [asum]
      rw [ha]
      unfold streamAux
      rw [getD_append_right'' _ _ _ _ (by
        simp only [List.length_append, List.length_singleton, Ref.length_zeros,
          length_chunk sig hsig r (b % 16) (by omega)]; omega)]
      simp only [List.length_append, List.length_singleton, Ref.length_zeros,
        length_chunk sig hsig r (b % 16) (by omega)]
      rw [show 8 * (j + 1) + 16 * (b % 16 + asum bs j) - (1 + 7 + 16 * (b % 16)) =
        8 * j + 16 * asum bs j by omega]
      rw [getD_streamAux bs (r + b % 16) j (by omega) (by simpa using hj)]
      rfl

theorem slice_streamAux : ∀ (bs : List Nat) (r j i : Nat), r + (bs.map (· % 16)).sum ≤ 117 →
    j < bs.length → i < bs.getD j 0 % 16 →
    Ref.slice (streamAux sig r bs) (8 * j + 16 * asum bs j + 8 + 16 * i) 16 =
      Ref.sigAuth sig (r + asum bs j + i)
  | [], r, j, i, _, hj, _ => by simp at hj
  | b :: bs, r, j, i, h, hj, hi => by
    simp only [List.map_cons, List.sum_cons] at h
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hi
      simp only [asum, List.take_zero, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero]
      unfold streamAux
      rw [List.append_assoc, slice_append_right _ _ _ (16 * i) _ (by simp),
        slice_append_left _ _ _ _ (by rw [length_chunk sig hsig r (b % 16) (by omega)]; omega),
        map_range_eq_ofFn,
        slice_flatten_ofFn _ 16 ⟨i, hi⟩ 0 16 _ (fun k _ => length_sigAuth sig hsig _ (by omega))
          (by simp [length_sigAuth sig hsig _ (show r + i < 117 by omega)]) (by ring),
        slice_full _ _ (length_sigAuth sig hsig _ (by omega))]
    | succ j =>
      simp only [List.getD_cons_succ] at hi
      have ha : asum (b :: bs) (j + 1) = b % 16 + asum bs j := by simp [asum]
      rw [ha]
      unfold streamAux
      rw [slice_append_right _ _ _ (8 * j + 16 * asum bs j + 8 + 16 * i) _ (by
        simp only [List.length_append, List.length_singleton, Ref.length_zeros,
          length_chunk sig hsig r (b % 16) (by omega)]; omega)]
      rw [slice_streamAux bs (r + b % 16) j i (by omega) (by simpa using hj) hi]
      congr 1; omega

end stream

/-- Consecutive chunks of auth items, read back in order. -/
theorem chunks_eq (bs : List Nat) (f : Nat → List Byte) :
    ∀ k, k ≤ bs.length →
      ((List.range k).map fun j =>
          ((List.range (bs.getD j 0 % 16)).map fun i => f (asum bs j + i)).flatten).flatten =
        ((List.range (asum bs k)).map f).flatten := by
  intro k
  induction k with
  | zero => intro _; simp [asum]
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega),
      asum_succ bs k (by omega), List.range_add, List.map_append, List.flatten_append]
    simp [List.map_map, Function.comp_def]

/-! ## The witness layout -/

/-- The partial witness `Ref.witnessBody` (16384 bytes, zero counters and pads) with the counters `cs`
written (`Ref.withCounters`; `cs = []` writes zeros). -/
abbrev witOf (sig : List Byte) (v vs segs : List Nat) (cs : List Nat) : List Byte :=
  Ref.withCounters (Ref.witnessBody sig v vs segs) cs

theorem slice_take (l : List Byte) (k x len : Nat) (h : x + len ≤ k) :
    Ref.slice (l.take k) x len = Ref.slice l x len := by
  unfold Ref.slice
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-! ### Reading through `Ref.withCounters`

The counters occupy `[2392, 2396)` and `[2944, 2960)`; every other byte is the partial witness's. -/
section transfer
variable (w0 : List Byte) (cs : List Nat) (hw : 2960 ≤ w0.length)
include hw

theorem length_take_2392 : (w0.take 2392).length = 2392 := by rw [List.length_take]; omega

theorem length_slice_2396 : (Ref.slice w0 2396 548).length = 548 := by
  simp only [Ref.slice, List.length_take, List.length_drop]; omega

theorem slice_withCounters_lo (x len : Nat) (h : x + len ≤ 2392) :
    Ref.slice (Ref.withCounters w0 cs) x len = Ref.slice w0 x len := by
  rw [withCounters_eq, List.append_assoc, List.append_assoc, List.append_assoc,
    slice_append_left _ _ _ _ (by rw [length_take_2392 w0 hw]; exact h), slice_take _ _ _ _ h]

theorem getD_withCounters_lo (x : Nat) (h : x < 2392) :
    (Ref.withCounters w0 cs).getD x 0 = w0.getD x 0 := by
  rw [withCounters_eq, List.append_assoc, List.append_assoc, List.append_assoc,
    getD_append_left'' _ _ _ _ (by rw [length_take_2392 w0 hw]; exact h),
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h, ← List.getD_eq_getElem?_getD]

theorem slice_withCounters_mid (x len : Nat) (h1 : 2396 ≤ x) (h2 : x + len ≤ 2944) :
    Ref.slice (Ref.withCounters w0 cs) x len = Ref.slice w0 x len := by
  rw [withCounters_eq,
    slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_take_2392 w0 hw, Ref.length_le32, length_slice_2396 w0 hw,
        length_le32s, List.length_map, List.length_range]; omega),
    slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_take_2392 w0 hw, Ref.length_le32, length_slice_2396 w0 hw]
      omega),
    slice_append_right _ _ _ (x - 2396) _ (by
      simp only [List.length_append, length_take_2392 w0 hw, Ref.length_le32]; omega),
    slice_slice _ _ _ _ _ (by omega), show 2396 + (x - 2396) = x by omega]

theorem slice_withCounters_hi (x len : Nat) (h : 2960 ≤ x) :
    Ref.slice (Ref.withCounters w0 cs) x len = Ref.slice w0 x len := by
  rw [withCounters_eq, slice_append_right _ _ _ (x - 2960) _ (by
      simp only [List.length_append, length_take_2392 w0 hw, Ref.length_le32, length_slice_2396 w0 hw,
        length_le32s, List.length_map, List.length_range]; omega)]
  have e1 : x - 2960 + 2960 = x := by omega
  have e2 : 2960 + (x - 2960) = x := by omega
  simp only [Ref.slice, List.drop_drop, e1, e2]

omit hw in
/-- Writing zero counters over zero counter bytes changes nothing. -/
theorem withCounters_nil_self (h4 : Ref.slice w0 2392 4 = Ref.zeros 4)
    (h16 : Ref.slice w0 2944 16 = Ref.zeros 16) : Ref.withCounters w0 [] = w0 := by
  have step : ∀ (a b : Nat), (w0.drop a).take b ++ w0.drop (a + b) = w0.drop a := by
    intro a b
    have hd : w0.drop (a + b) = (w0.drop a).drop b := by
      rw [List.drop_drop]; try ac_rfl
    rw [hd, List.take_append_drop]
  have e1 : Ref.le32 (([] : List Nat).getD 4 0) = Ref.zeros 4 := by decide
  have e2 : (((List.range 4).map (([] : List Nat).getD · 0)).map Ref.le32).flatten = Ref.zeros 16 := by
    decide
  rw [withCounters_eq, e1, e2, ← h4, ← h16]
  simp only [Ref.slice, List.append_assoc]
  rw [show (2960 : Nat) = 2944 + 16 from rfl, step, show (2944 : Nat) = 2396 + 548 from rfl, step,
    show (2396 : Nat) = 2392 + 4 from rfl, step, List.take_append_drop]

end transfer

section layout
variable (sig : List Byte) (hsig : sig.length = 6032) (v vs segs : List Nat) (hvs : vs.length = 15)
  (cs : List Nat)

/-- The partial witness: `head (272 bytes) ++ stream region (2120) ++ (0^8 ++ paths (544) ++ chain
array (13440))`. -/
theorem witnessBody_split : Ref.witnessBody sig v vs segs =
    (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
      ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten) ++
    (Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes ++
    (Ref.zeros 8 ++ ((List.range Ref.nLayers).map (Ref.sigPath sig)).flatten ++
      ((List.range Ref.nLayers).map (Ref.chainRegion sig)).flatten) := by
  simp only [Ref.witnessBody, List.append_assoc]
  rfl

include hsig in
theorem length_sigItem (i : Nat) (hi : i < 135) : (Ref.sigItem sig i).length = 16 :=
  length_slice _ _ _ (by rw [hsig]; omega)

include hsig hvs in
theorem length_head :
    (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
      ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten).length = 272 := by
  simp only [List.length_append, List.length_map, hvs, Ref.length_zeros]
  rw [show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega),
    map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigItem sig hsig _ (by
      have := j.isLt; unfold Ref.porsK at this; omega))]
  rfl

theorem length_E : ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes).length =
    2120 := by
  simp only [List.length_take, List.length_append, Ref.length_zeros]
  rw [Nat.min_eq_left (by omega)]
  exact Ref.streamBytes_eq

theorem layer_bound : ∀ l, l < 5 → Ref.sigLayerOff l + Ref.bodyBytes l ≤ 6032 := by decide

theorem layer_table : ∀ l, l < 5 →
    Ref.bodyBytes l = 672 + 16 * Ref.height l ∧ 2128 ≤ Ref.sigLayerOff l ∧
    16 * ((List.range l).map Ref.height).sum + 16 * Ref.height l ≤ 544 := by decide

include hsig in
theorem length_sigPath (l : Nat) (hl : l < 5) : (Ref.sigPath sig l).length = 16 * Ref.height l := by
  have := layer_bound l hl
  unfold Ref.sigPath
  exact length_slice _ _ _ (by rw [hsig]; simp only [Ref.bodyBytes, Ref.nChains] at this ⊢; omega)

include hsig in
theorem length_paths (k : Nat) (hk : k ≤ 5) :
    ((List.range k).map (Ref.sigPath sig)).flatten.length = 16 * ((List.range k).map Ref.height).sum := by
  rw [List.length_flatten, List.map_map, ← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro l hl
  rw [List.mem_range] at hl
  exact length_sigPath sig hsig l (by omega)

include hsig in
theorem length_P : ((List.range Ref.nLayers).map (Ref.sigPath sig)).flatten.length = 544 := by
  rw [length_paths sig hsig Ref.nLayers (by decide)]
  decide

include hsig in
theorem length_sigChain (lay : Nat) (hlay : lay < 5) (i : Nat) (hi : i < 42) :
    (Ref.sigChain sig lay i).length = 16 := by
  have := layer_bound lay hlay
  unfold Ref.sigChain
  exact length_slice _ _ _ (by rw [hsig]; simp only [Ref.bodyBytes, Ref.nChains] at this ⊢; omega)

include hsig in
theorem length_chainRegion (lay : Nat) (hlay : lay < 5) : (Ref.chainRegion sig lay).length = 2688 := by
  unfold Ref.chainRegion
  rw [map_range_eq_ofFn, length_flatten_ofFn _ 64 (fun i => by
    simp only [List.length_append, Ref.length_zeros, length_sigChain sig hsig lay hlay i.val i.isLt])]
  rfl

include hsig hvs in
theorem length_witnessBody : (Ref.witnessBody sig v vs segs).length = 16384 :=
  Ref.length_witnessList sig hsig v vs segs hvs

include hsig hvs in
theorem length_witOf : (witOf sig v vs segs cs).length = 16384 := by
  unfold witOf
  rw [length_withCounters _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega),
    length_witnessBody sig hsig v vs segs hvs]

/-! ### Slices of the partial witness -/

include hsig hvs in
theorem slice_body_c4 : Ref.slice (Ref.witnessBody sig v vs segs) 2392 4 = Ref.zeros 4 := by
  rw [witnessBody_split,
    slice_append_right _ _ _ 0 _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E]),
    slice_append_left _ _ _ _ (by rw [List.length_append, Ref.length_zeros, length_P sig hsig] ; omega),
    slice_append_left _ _ _ _ (by rw [Ref.length_zeros] ; omega)]
  rfl

include hsig hvs in
theorem slice_body_P (x len : Nat) (h : x + len ≤ 544) :
    Ref.slice (Ref.witnessBody sig v vs segs) (2400 + x) len =
      Ref.slice ((List.range Ref.nLayers).map (Ref.sigPath sig)).flatten x len := by
  rw [witnessBody_split,
    slice_append_right _ _ _ (8 + x) _ (by
      rw [List.length_append, length_head sig hsig v vs hvs, length_E] ; omega),
    slice_append_left _ _ _ _ (by rw [List.length_append, Ref.length_zeros, length_P sig hsig]; omega),
    slice_append_right _ _ _ x _ (by simp)]

include hsig hvs in
theorem slice_body_C (x len : Nat) :
    Ref.slice (Ref.witnessBody sig v vs segs) (2944 + x) len =
      Ref.slice ((List.range Ref.nLayers).map (Ref.chainRegion sig)).flatten x len := by
  rw [witnessBody_split,
    slice_append_right _ _ _ (552 + x) _ (by
      rw [List.length_append, length_head sig hsig v vs hvs, length_E] ; omega),
    slice_append_right _ _ _ x _ (by
      rw [List.length_append, Ref.length_zeros, length_P sig hsig])]

include hsig hvs in
/-- Inside chain block `(lay, i)` of the partial witness, the 48 bytes before the value are zero. -/
theorem slice_body_block (lay : Nat) (hlay : lay < 5) (i : Nat) (hi : i < 42) (r len : Nat)
    (h : r + len ≤ 48) :
    Ref.slice (Ref.witnessBody sig v vs segs) (Ref.blockOff lay i + r) len = Ref.zeros len := by
  rw [Ref.blockOff_eq, show 2944 + 2688 * lay + 64 * i + r = 2944 + (2688 * lay + (64 * i + r)) by ring,
    slice_body_C sig hsig v vs segs hvs, map_range_eq_ofFn,
    slice_flatten_ofFn _ 2688 (⟨lay, hlay⟩ : Fin Ref.nLayers) (64 * i + r) len (2688 * lay + (64 * i + r))
      (fun j _ => length_chainRegion sig hsig j.val j.isLt)
      (by rw [length_chainRegion sig hsig lay hlay]; omega) rfl]
  show Ref.slice (Ref.chainRegion sig lay) (64 * i + r) len = _
  unfold Ref.chainRegion
  rw [map_range_eq_ofFn,
    slice_flatten_ofFn _ 64 (⟨i, hi⟩ : Fin Ref.nChains) r len (64 * i + r)
      (fun j _ => by
        simp only [List.length_append, Ref.length_zeros, length_sigChain sig hsig lay hlay j.val j.isLt])
      (by simp only [List.length_append, Ref.length_zeros, length_sigChain sig hsig lay hlay i hi] ; omega)
      rfl]
  show Ref.slice (Ref.zeros 48 ++ Ref.sigChain sig lay i) r len = _
  rw [slice_append_left _ _ _ _ (by rw [Ref.length_zeros]; exact h)]
  simp only [Ref.slice, Ref.zeros, List.drop_replicate, List.take_replicate]
  congr 1; omega

include hsig hvs in
/-- The value slot of chain block `(lay, i)` holds the signature's chain value. -/
theorem slice_body_chain (lay : Nat) (hlay : lay < 5) (i : Nat) (hi : i < 42) :
    Ref.slice (Ref.witnessBody sig v vs segs) (Ref.blockOff lay i + 48) 16 =
      Ref.slice sig (Ref.sigLayerOff lay + 16 * i) 16 := by
  rw [Ref.blockOff_eq, show 2944 + 2688 * lay + 64 * i + 48 = 2944 + (2688 * lay + (64 * i + 48)) by ring,
    slice_body_C sig hsig v vs segs hvs, map_range_eq_ofFn,
    slice_flatten_ofFn _ 2688 (⟨lay, hlay⟩ : Fin Ref.nLayers) (64 * i + 48) 16 (2688 * lay + (64 * i + 48))
      (fun j _ => length_chainRegion sig hsig j.val j.isLt)
      (by rw [length_chainRegion sig hsig lay hlay]; omega) rfl]
  show Ref.slice (Ref.chainRegion sig lay) (64 * i + 48) 16 = _
  unfold Ref.chainRegion
  rw [map_range_eq_ofFn,
    slice_flatten_ofFn _ 64 (⟨i, hi⟩ : Fin Ref.nChains) 48 16 (64 * i + 48)
      (fun j _ => by
        simp only [List.length_append, Ref.length_zeros, length_sigChain sig hsig lay hlay j.val j.isLt])
      (by simp only [List.length_append, Ref.length_zeros, length_sigChain sig hsig lay hlay i hi] ; omega)
      rfl]
  show Ref.slice (Ref.zeros 48 ++ Ref.sigChain sig lay i) 48 16 = _
  rw [slice_append_right _ _ _ 0 _ (by simp)]
  exact slice_full _ _ (length_sigChain sig hsig lay hlay i hi)

include hsig hvs in
/-- Sibling `l` of layer `lay`'s path. -/
theorem slice_body_sib (lay : Nat) (hlay : lay < 5) (l : Nat) (hl : l < Ref.height lay) :
    Ref.slice (Ref.witnessBody sig v vs segs) (Ref.pathOff lay + 16 * l) 16 =
      Ref.slice sig (Ref.sigLayerOff lay + (672 + 16 * l)) 16 := by
  obtain ⟨-, -, t3⟩ := layer_table lay hlay
  rw [show Ref.pathOff lay + 16 * l = 2400 + (16 * ((List.range lay).map Ref.height).sum + 16 * l) by
        unfold Ref.pathOff; rw [Ref.wPaths_eq]; ring,
    slice_body_P sig hsig v vs segs hvs _ _ (by omega)]
  have hL : ((List.range Ref.nLayers).map (Ref.sigPath sig)).take lay =
      (List.range lay).map (Ref.sigPath sig) := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by unfold Ref.nLayers; omega)]
  have e := slice_flatten_take ((List.range Ref.nLayers).map (Ref.sigPath sig)) lay (16 * l) 16
    (by simp [Ref.nLayers]; omega) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by unfold Ref.nLayers; omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [length_sigPath sig hsig lay hlay]; omega)
  rw [hL, length_paths sig hsig lay (by omega)] at e
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by unfold Ref.nLayers; omega)]
  simp only [Option.map_some, Option.getD_some]
  unfold Ref.sigPath
  rw [slice_slice _ _ _ _ _ (by omega)]
  congr 1
  unfold Ref.nChains; ring

include hsig hvs in
/-- The partial witness is itself with zero counters written. -/
theorem witnessList_withCounters_nil :
    Ref.witnessList sig v vs segs = Ref.withCounters (Ref.witnessList sig v vs segs) [] := by
  refine (withCounters_nil_self _ (slice_body_c4 sig hsig v vs segs hvs) ?_).symm
  have := slice_body_block sig hsig v vs segs hvs 0 (by decide) 0 (by decide) 0 16 (by decide)
  rw [Ref.blockOff_eq] at this
  simpa using this

/-! ### Fields of the witness with counters -/

include hsig hvs in
theorem slice_W_head (x len : Nat) (h : x + len ≤ 272) :
    Ref.slice (witOf sig v vs segs cs) x len =
      Ref.slice (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
        ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten) x len := by
  unfold witOf
  rw [slice_withCounters_lo _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) x len (by omega),
    witnessBody_split,
    slice_append_left _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs]; omega),
    slice_append_left _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega)]

include hsig hvs in
theorem getD_W_head (x : Nat) (h : x < 272) :
    (witOf sig v vs segs cs).getD x 0 =
      (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
        ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten).getD x 0 := by
  unfold witOf
  rw [getD_withCounters_lo _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) x (by omega),
    witnessBody_split,
    getD_append_left'' _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs]; omega),
    getD_append_left'' _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega)]

include hsig hvs in
theorem slice_W_E (x len : Nat) (h : x + len ≤ 2120) :
    Ref.slice (witOf sig v vs segs cs) (272 + x) len =
      Ref.slice ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes) x len := by
  unfold witOf
  rw [slice_withCounters_lo _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) _ len (by omega),
    witnessBody_split,
    slice_append_left _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E]; omega),
    slice_append_right _ _ _ x _ (by rw [length_head sig hsig v vs hvs])]

include hsig hvs in
theorem getD_W_E (x : Nat) (h : x < 2120) :
    (witOf sig v vs segs cs).getD (272 + x) 0 =
      ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes).getD x 0 := by
  unfold witOf
  rw [getD_withCounters_lo _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) _ (by omega),
    witnessBody_split,
    getD_append_left'' _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E]; omega),
    getD_append_right'' _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega),
    length_head sig hsig v vs hvs, Nat.add_sub_cancel_left]

include hsig hvs in
theorem witRho_W : Ref.witRho (witOf sig v vs segs cs) = Ref.sigRho sig := by
  unfold Ref.witRho
  rw [slice_W_head sig hsig v vs segs hvs cs 0 16 (by omega), List.append_assoc, List.append_assoc,
    slice_append_left _ _ _ _ (by rw [show (Ref.sigRho sig).length = 16 from
      length_slice _ _ _ (by rw [hsig]; omega)]),
    slice_full _ _ (show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega))]

include hsig hvs in
theorem witSecret_W (s : Nat) (hs : s < 15) :
    Ref.witSecret (witOf sig v vs segs cs) s = Ref.sigItem sig s := by
  unfold Ref.witSecret
  rw [slice_W_head sig hsig v vs segs hvs cs _ 16 (by unfold Ref.wSec; omega)]
  rw [slice_append_right _ _ _ (16 * s) _ (by
    simp only [List.length_append, List.length_map, hvs, Ref.length_zeros]
    rw [show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega)]
    unfold Ref.wSec; omega)]
  rw [map_range_eq_ofFn, slice_flatten_ofFn (fun j : Fin Ref.porsK => Ref.sigItem sig j.val) 16 ⟨s, hs⟩
    0 16 (16 * s)
    (fun j _ => length_sigItem sig hsig _ (by have := j.isLt; unfold Ref.porsK at this; omega))
    (by rw [length_sigItem sig hsig _ (by simp; omega)]) (by ring),
    slice_full _ _ (length_sigItem sig hsig _ (by simp; omega))]

include hsig hvs in
theorem witPi_W (s : Nat) (hs : s < 15) :
    Ref.witPi (witOf sig v vs segs cs) s = (Ref.byte (8 * v.idxOf (vs.getD s 0))).toNat := by
  unfold Ref.witPi
  rw [getD_W_head sig hsig v vs segs hvs cs _ (by unfold Ref.wPi; omega), List.append_assoc,
    List.append_assoc,
    getD_append_right'' _ _ _ _ (by rw [show (Ref.sigRho sig).length = 16 from
      length_slice _ _ _ (by rw [hsig]; omega)]; unfold Ref.wPi; omega),
    show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega),
    getD_append_left'' _ _ _ _ (by simp [hvs]; unfold Ref.wPi; omega)]
  simp only [Ref.wPi, show 16 + s - 16 = s by omega, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl

/-! ### Layers -/

include hsig hvs in
theorem witChain_W (lay : Layer) (i : Nat) (hi : i < 42) :
    Ref.witChain (witOf sig v vs segs cs) lay.val i =
      Ref.slice sig (Ref.sigLayerOff lay.val + 16 * i) 16 := by
  have hlay : lay.val < 5 := lay.isLt
  unfold Ref.witChain witOf
  rw [slice_withCounters_hi _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) _ _
      (by rw [Ref.blockOff_eq]; omega)]
  exact slice_body_chain sig hsig v vs segs hvs lay.val hlay i hi

include hsig hvs in
theorem witSib_W (lay : Layer) (l : Nat) (hl : l < Ref.height lay.val) :
    Ref.witSib (witOf sig v vs segs cs) lay.val l =
      Ref.slice sig (Ref.sigLayerOff lay.val + (672 + 16 * l)) 16 := by
  have hlay : lay.val < 5 := lay.isLt
  obtain ⟨-, -, t3⟩ := layer_table lay.val hlay
  unfold Ref.witSib witOf
  rw [slice_withCounters_mid _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) _ _
      (by unfold Ref.pathOff; rw [Ref.wPaths_eq]; omega)
      (by unfold Ref.pathOff; rw [Ref.wPaths_eq]; omega)]
  exact slice_body_sib sig hsig v vs segs hvs lay.val hlay l hl

include hsig hvs in
/-- The pad bytes (`16 ≤ r`, `r + len ≤ 48` into the block) of every chain block are zero. -/
theorem slice_W_pad (lay : Layer) (i : Nat) (hi : i < 42) (r len : Nat) (hr : 16 ≤ r)
    (h : r + len ≤ 48) :
    Ref.slice (witOf sig v vs segs cs) (Ref.blockOff lay.val i + r) len = Ref.zeros len := by
  have hlay : lay.val < 5 := lay.isLt
  unfold witOf
  rw [slice_withCounters_hi _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) _ _
      (by rw [Ref.blockOff_eq]; omega)]
  exact slice_body_block sig hsig v vs segs hvs lay.val hlay i hi r len h

include hsig hvs in
theorem witCounter_W (lay : Layer) :
    Ref.slice (witOf sig v vs segs cs) (Ref.ctrOff lay.val) 4 = Ref.le32 (cs.getD lay.val 0) :=
  slice_withCounters_ctrOff _ _ (by rw [length_witnessBody sig hsig v vs segs hvs]; omega) lay.val lay.isLt

/-- A layer read at the signature offsets, with the counter `cs[lay]`. -/
def sigLayerOf (sig : List Byte) (cs : List Nat) (lay : Layer) : LayerSignature lay :=
  ⟨Ref.ofList 4 (Ref.le32 (cs.getD lay.val 0)),
    fun i => Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 16 * i.val) 16),
    fun l => Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + (672 + 16 * l.val)) 16)⟩

include hsig hvs in
theorem witLayer_W (lay : Layer) :
    witLayer (witOf sig v vs segs cs) lay = sigLayerOf sig cs lay := by
  unfold witLayer sigLayerOf
  congr 1
  · rw [witCounter_W sig hsig v vs segs hvs cs lay]
  · funext i
    rw [witChain_W sig hsig v vs segs hvs cs lay i.val i.isLt]
  · funext l
    rw [witSib_W sig hsig v vs segs hvs cs lay l.val (by rw [height_eq]; exact l.isLt)]


/-! ### The stream region -/

theorem ofFn_segAt_nodes (w : List Byte) (p : Nat) :
    List.ofFn (segAt w p).nodes = (List.range (Ref.wbyte w p % 16)).map fun i => wdig w (p + 8 + 16 * i) :=
  (map_range_eq_ofFn (Ref.wbyte w p % 16) (fun i => wdig w (p + 8 + 16 * i))).symm

section streamFacts
variable (hsegs : segs.length = 29) (hb : ∀ b ∈ segs, b < 256)
  (hn : (segs.map (· % 16)).sum ≤ 117)

include hsig hn in
theorem length_segStream :
    (Ref.segStream sig segs).length = 8 * segs.length + 16 * (segs.map (· % 16)).sum := by
  rw [segStream_eq, length_streamAux sig hsig segs 0 (by omega)]

include hsig hvs hsegs hn in
theorem getD_W_seg (j : Nat) (hj : j < 29) :
    (witOf sig v vs segs cs).getD (272 + (8 * j + 16 * asum segs j)) 0 =
      Ref.byte (segs.getD j 0) := by
  have ha : asum segs j ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  have hL := length_segStream sig hsig segs hn
  rw [getD_W_E sig hsig v vs segs hvs cs _ (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by rw [Ref.streamBytes_eq]; omega),
    ← List.getD_eq_getElem?_getD, getD_append_left'' _ _ _ _ (by rw [hL]; omega), segStream_eq,
    getD_streamAux sig hsig segs 0 j (by omega) (by omega)]

include hsig hvs hsegs hn in
theorem slice_W_node (j i : Nat) (hj : j < 29) (hi : i < segs.getD j 0 % 16) :
    Ref.slice (witOf sig v vs segs cs) (272 + (8 * j + 16 * asum segs j + 8 + 16 * i)) 16 =
      Ref.sigAuth sig (asum segs j + i) := by
  have ha : asum segs (j + 1) ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  rw [asum_succ segs j (by omega)] at ha
  have hL := length_segStream sig hsig segs hn
  rw [slice_W_E sig hsig v vs segs hvs cs _ _ (by omega)]
  rw [slice_take _ _ _ _ (by rw [Ref.streamBytes_eq]; omega),
    slice_append_left _ _ _ _ (by rw [hL]; omega), segStream_eq,
    slice_streamAux sig hsig segs 0 j i (by omega) (by omega) hi, Nat.zero_add]

include hsig hvs hsegs hb hn in
theorem segPtr_W (j : Nat) (hj : j ≤ 29) :
    segPtr (witOf sig v vs segs cs) j = 272 + (8 * j + 16 * asum segs j) := by
  induction j with
  | zero => simp [segPtr, asum, Ref.wStream, Ref.wSec, Ref.porsK]
  | succ j ih =>
    rw [segPtr, ih (by omega)]
    unfold Ref.wbyte
    rw [getD_W_seg sig hsig v vs segs hvs cs hsegs hn j (by omega), Ref.byte_toNat,
      asum_succ segs j (by omega)]
    have : segs.getD j 0 < 256 := hb _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
    rw [Nat.mod_eq_of_lt this]
    ring

include hsig hvs hsegs hb hn in
theorem wbyte_segPtr_W (j : Nat) (hj : j < 29) :
    Ref.wbyte (witOf sig v vs segs cs) (segPtr (witOf sig v vs segs cs) j) =
      segs.getD j 0 := by
  rw [segPtr_W sig hsig v vs segs hvs cs hsegs hb hn j (by omega)]
  unfold Ref.wbyte
  rw [getD_W_seg sig hsig v vs segs hvs cs hsegs hn j hj, Ref.byte_toNat]
  exact Nat.mod_eq_of_lt (hb _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _))

include hsig hvs hsegs hb hn in
theorem dv_node_W (j i : Nat) (hj : j < 29) (hi : i < segs.getD j 0 % 16) :
    dv (wdig (witOf sig v vs segs cs) (segPtr (witOf sig v vs segs cs) j + 8 + 16 * i)) =
      Ref.sigAuth sig (asum segs j + i) := by
  have hW : (witOf sig v vs segs cs).length = 16384 := length_witOf sig hsig v vs segs hvs cs
  have ha : asum segs (j + 1) ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  rw [asum_succ segs j (by omega)] at ha
  rw [dv_wdig, segPtr_W sig hsig v vs segs hvs cs hsegs hb hn j (by omega),
    wbytes_eq_slice _ _ _ (by rw [hW]; omega),
    show 272 + (8 * j + 16 * asum segs j) + 8 + 16 * i = 272 + (8 * j + 16 * asum segs j + 8 + 16 * i)
      by ring,
    slice_W_node sig hsig v vs segs hvs cs hsegs hn j i hj hi]

include hsig hvs hsegs hb hn in
/-- The authentication nodes the decoder reads are the signature's first `n` auth items. -/
theorem authNodes_W :
    ((authNodes (witSig (witOf sig v vs segs cs))).map dv).flatten =
      ((List.range (segs.map (· % 16)).sum).map (Ref.sigAuth sig)).flatten := by
  unfold authNodes
  rw [List.map_flatten, List.map_ofFn, List.flatten_flatten]
  have e : ∀ j : Fin SphincsSecurity.ftsSegments,
      ((List.map dv ∘ fun j => List.ofFn ((witSig (witOf sig v vs segs cs)).fts.segments j).nodes) j)
        = (List.range (segs.getD j.val 0 % 16)).map fun i => Ref.sigAuth sig (asum segs j.val + i) := by
    intro j
    have hj : j.val < 29 := j.isLt
    simp only [Function.comp_apply, witSig, witFts]
    rw [ofFn_segAt_nodes, List.map_map, wbyte_segPtr_W sig hsig v vs segs hvs cs hsegs hb hn j.val hj]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact dv_node_W sig hsig v vs segs hvs cs hsegs hb hn j.val i hj hi
  rw [List.ofFn_inj.mpr (funext e)]
  have e3 : ∀ (F : Nat → List Byte) (G : Fin SphincsSecurity.ftsSegments → List Byte),
      (∀ j, G j = F j.val) → List.ofFn G = (List.range SphincsSecurity.ftsSegments).map F :=
    fun F G h => by rw [map_range_eq_ofFn]; exact List.ofFn_inj.mpr (funext h)
  rw [List.map_ofFn, e3 (fun j => ((List.range (segs.getD j 0 % 16)).map
    fun i => Ref.sigAuth sig (asum segs j + i)).flatten)
    (List.flatten ∘ fun x : Fin SphincsSecurity.ftsSegments =>
      (List.range (segs.getD x.val 0 % 16)).map fun i => Ref.sigAuth sig (asum segs x.val + i))
    (fun j => rfl)]
  rw [show SphincsSecurity.ftsSegments = segs.length by rw [hsegs]; rfl, chunks_eq segs _ _ (le_refl _),
    asum_length]

end streamFacts

include hsig in
theorem layerBytes_of (S : Signature) (lay : Layer) (h : S.layers lay = sigLayerOf sig cs lay) :
    layerBytes S lay = Ref.slice sig (Ref.sigLayerOff lay.val) (Ref.bodyBytes lay.val) := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  obtain ⟨t3, -, -⟩ := layer_table lay.val hl
  have hb := layer_bound lay.val hl
  have hh := height_eq lay
  unfold layerBytes
  rw [h]
  simp only [sigLayerOf]
  have ec : (List.ofFn fun i : Fin SphincsSecurity.numChains =>
      dv (Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 16 * i.val) 16))).flatten =
      Ref.slice sig (Ref.sigLayerOff lay.val) (16 * 42) := by
    rw [← flatten_ofFn_slices]
    congr 1
    exact List.ofFn_inj.mpr (funext fun i => dv_ofList_slice _ _ (by
      have := i.isLt; simp only [SphincsSecurity.numChains] at this; rw [hsig]; omega))
  have ep : (List.ofFn fun l : Fin (SphincsSecurity.layerHeight lay) =>
      dv (Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + (672 + 16 * l.val)) 16))).flatten =
      Ref.slice sig (Ref.sigLayerOff lay.val + 672) (16 * SphincsSecurity.layerHeight lay) := by
    rw [← flatten_ofFn_slices]
    congr 1
    refine List.ofFn_inj.mpr (funext fun l => ?_)
    have := l.isLt
    rw [dv_ofList_slice _ _ (by rw [hsig]; omega)]
    congr 1; ring
  rw [ec, ep, ← slice_split]
  congr 1
  rw [t3, hh]

end layout

/-! ## R2 -/

theorem segByte_raw : ∀ a, a < 16 → ∀ m p : Bool,
    (a ||| (if m then 16 else 0) ||| 32 * (if p then 1 else 0)) =
      a + (if m then 16 else 0) + 32 * (if p then 1 else 0) := by decide

theorem segByte_val (sg : SphincsSecurity.Concrete.ScheduleSegment) (h : sg.reads.length < 16) :
    segByte sg = sg.reads.length + (if sg.merge then 16 else 0) + 32 * (if sg.parity then 1 else 0) :=
  segByte_raw _ h _ _

/-- The digest leaves of `N` as a slot map. -/
def leavesN (N : Nat) : IndexGroup → FtsLeaf := fun r => ⟨Ref.leafOf N r.val, Nat.mod_lt _ (by decide)⟩

theorem leavesOf_leavesN (N : Nat) : Ref.leavesOf N = List.ofFn fun r => (leavesN N r).val := by
  unfold Ref.leavesOf
  rw [map_range_eq_ofFn]
  rfl

/-- What a successful `expandOf` knows: the admissible leaves, the schedule, the zero slots. -/
theorem expandOf_some (sig : List Byte) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf sig N = some wl) :
    let vs := Ref.sortLeaves (Ref.leavesOf N)
    (Ref.leavesOf N).Nodup ∧ Ref.octopusSize vs ≤ 117 ∧
      (∀ i, (Ref.schedule vs).2.length ≤ i → i < 117 → Ref.sigAuth sig i = Ref.zeros 16) ∧
      wl = Ref.witnessList sig (Ref.leavesOf N) vs (Ref.schedule vs).1 := by
  unfold Ref.expandOf at h
  dsimp only at h
  split at h
  · cases h
  next hnd =>
  split at h
  · cases h
  next hoct =>
  split at h
  · cases h
  next hz =>
  cases h
  refine ⟨by simpa using hnd, by unfold Ref.porsM at hoct; omega, ?_, rfl⟩
  intro i hi1 hi2
  have hz' : (List.range' (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length
      (Ref.porsM - (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length)).all
      (fun i => Ref.sigAuth sig i == Ref.zeros 16) = true := by simpa using hz
  have := List.all_eq_true.mp hz' i (List.mem_range'_1.mpr ⟨hi1, by unfold Ref.porsM; omega⟩)
  simpa using this

/-- The schedule facts for the leaves of any `N` passing `expandOf`'s checks. -/
theorem sched_facts (N : Nat) (hnd : (Ref.leavesOf N).Nodup)
    (hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 117) :
    let sched := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves (leavesN N))
    SphincsSecurity.Concrete.AdmissibleLeaves (leavesN N) ∧
    Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves (leavesN N) ∧
    Ref.schedule (Ref.sortLeaves (Ref.leavesOf N)) =
      (sched.map segByte, (sched.map (·.reads)).flatten) ∧
    sched.length = 29 ∧ (∀ s ∈ sched, s.reads.length ≤ 14 ∧ ∀ p ∈ s.reads, p.1 < 14 ∧ p.2 < 2 ^ (14 - p.1)) ∧
    ((sched.map (·.reads)).flatten).length ≤ 117 ∧
    ((sched.map segByte).map (· % 16)).sum = ((sched.map (·.reads)).flatten).length ∧
    (∀ b ∈ sched.map segByte, b < 256) := by
  intro sched
  have hsort : Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves (leavesN N) := by
    rw [leavesOf_leavesN, sortLeaves_eq]
  have hadm : SphincsSecurity.Concrete.AdmissibleLeaves (leavesN N) := by
    refine ⟨?_, ?_⟩
    · rw [leavesOf_leavesN, List.nodup_ofFn] at hnd
      exact fun a b e => hnd (congrArg Fin.val e)
    · rw [← hsort]; exact hoct
  obtain ⟨hl, hr, ht⟩ := schedule_admissible (leavesN N) hadm
  refine ⟨hadm, hsort, ?_, hl, hr, ?_, ?_, ?_⟩
  · rw [hsort]
    exact schedule_ref _ (fun v hv => by
      simp only [SphincsSecurity.Concrete.sortedLeaves, List.mem_map] at hv
      obtain ⟨r, _, rfl⟩ := hv
      exact (leavesN N r).isLt)
  · rw [ht, ← octopusSize_eq, ← hsort]; exact hoct
  · rw [List.map_map, List.length_flatten, List.map_map]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro sg hsg
    simp only [Function.comp_apply]
    rw [segByte_val sg (by have := (hr sg hsg).1; omega)]
    have := (hr sg hsg).1
    split <;> split <;> omega
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨sg, hsg, rfl⟩ := hb
    rw [segByte_val sg (by have := (hr sg hsg).1; omega)]
    have := (hr sg hsg).1
    split <;> split <;> omega

theorem sigAuth_eq (sig : List Byte) (i : Nat) : Ref.sigAuth sig i = Ref.slice sig (256 + 16 * i) 16 := by
  unfold Ref.sigAuth Ref.sigItem Ref.porsK
  congr 1; ring

/-- **R2 on byte lists**: the partial witness of a signature passing `expandOf`'s checks, with any
counters written, decodes to a signature whose compact form is the input. -/
theorem compressList_witOf (sig : List Byte) (hsig : sig.length = 6032) (N : Nat)
    (hnd : (Ref.leavesOf N).Nodup) (hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 117)
    (hz : ∀ i, (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length ≤ i → i < 117 →
      Ref.sigAuth sig i = Ref.zeros 16) (cs : List Nat) :
    compressList (witSig (witOf sig (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N))
      (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1 cs)) = sig := by
  obtain ⟨-, -, hsch, hl29, -, hn118, hsum, hb⟩ := sched_facts N hnd hoct
  set sched := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves (leavesN N))
  set v := Ref.leavesOf N
  set vs := Ref.sortLeaves v
  set segs := sched.map segByte with hsegs_def
  have hvs : vs.length = 15 := by simp [vs, v, Ref.sortLeaves, Ref.leavesOf, Ref.porsK]
  have hsegs : segs.length = 29 := by simp [segs, hl29]
  rw [hsch] at hz ⊢
  simp only at hz ⊢
  set n := ((sched.map (·.reads)).flatten).length
  have hn : (segs.map (· % 16)).sum ≤ 117 := by rw [hsum]; exact hn118
  unfold compressList
  -- the four parts
  have p1 : dv (witSig (witOf sig v vs segs cs)).randomness = Ref.slice sig 0 16 := by
    simp only [witSig]
    rw [witRho_W sig hsig v vs segs hvs cs]
    exact dv_ofList_slice _ _ (by omega)
  have p2 : (List.ofFn fun s => dv ((witSig (witOf sig v vs segs cs)).fts.secrets s)).flatten =
      Ref.slice sig 16 (16 * 15) := by
    rw [← flatten_ofFn_slices]
    refine congrArg List.flatten ?_
    refine List.ofFn_inj.mpr (funext fun s => ?_)
    have := s.isLt
    simp only [SphincsSecurity.ftsOpenings] at this
    simp only [witSig, witFts]
    rw [witSecret_W sig hsig v vs segs hvs cs _ this]
    exact dv_ofList_slice _ _ (by omega)
  have p3 : (((authNodes (witSig (witOf sig v vs segs cs))).map dv).flatten ++
      Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM) = Ref.slice sig 256 (16 * 117) := by
    rw [authNodes_W sig hsig v vs segs hvs cs hsegs hb hn, hsum]
    have hA : ((List.range n).map (Ref.sigAuth sig)).flatten.length = 16 * n := by
      rw [map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigAuth sig hsig _ (by
        have := j.isLt; omega))]
    rw [← flatten_ofFn_slices, show (List.ofFn fun i : Fin 117 => Ref.slice sig (256 + 16 * i.val) 16) =
      (List.range 117).map (Ref.sigAuth sig) by
        rw [map_range_eq_ofFn]; exact List.ofFn_inj.mpr (funext fun i => (sigAuth_eq sig i).symm)]
    have hB : ∀ k, n + k ≤ 117 →
        ((List.range k).map fun j => Ref.sigAuth sig (n + j)).flatten = Ref.zeros (16 * k) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [hz (n + k) (by omega) (by omega)]
        simp only [Ref.zeros, ← List.replicate_add]
        congr 1
    rw [show (117 : Nat) = n + (117 - n) by omega, List.range_add, List.map_append,
      List.flatten_append, List.map_map, List.take_append, List.take_of_length_le (by rw [hA]; unfold Ref.porsM; omega)]
    refine congrArg₂ (· ++ ·) rfl ?_
    rw [hA]
    have e : (fun j => Ref.sigAuth sig (n + j)) = (Ref.sigAuth sig ∘ fun x => n + x) := rfl
    rw [← e, hB _ (by omega)]
    simp only [Ref.zeros, List.take_replicate, Ref.porsM]
    exact congrArg (List.replicate · 0) (by omega)
  have p4 : (List.ofFn (layerBytes (witSig (witOf sig v vs segs cs)))).flatten =
      Ref.slice sig 2128 3904 := by
    rw [show (3904 : Nat) = ((List.range SphincsSecurity.numLayers).map Ref.bodyBytes).sum by decide,
      ← flatten_ofFn_slices_var]
    refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun lay => ?_))
    rw [layerBytes_of sig hsig cs (witSig (witOf sig v vs segs cs)) lay
      (witLayer_W sig hsig v vs segs hvs cs lay)]
    rfl
  rw [p1, p2, p3, p4]
  conv_rhs => rw [← slice_full sig 6032 hsig]
  rw [show (6032 : Nat) = 16 + (16 * 15 + (16 * 117 + 3904)) from rfl, slice_split, slice_split,
    slice_split]
  simp only [List.append_assoc]

/-- The partial witness of a successful `expandOf`, with the counters `cs` written. -/
theorem expandOf_witOf (sig : List Byte) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf sig N = some wl) (cs : List Nat) :
    Ref.withCounters wl cs = witOf sig (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N))
      (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1 cs := by
  obtain ⟨-, -, -, hwl⟩ := expandOf_some sig N wl h
  subst hwl
  rfl

/-- **R2 on byte lists**: a successful expansion, with any counters written, decodes to a signature
whose compact form is the input. -/
theorem compressList_expandOf (sig : List Byte) (hsig : sig.length = 6032) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf sig N = some wl) (cs : List Nat) :
    compressList (witSig (Ref.withCounters wl cs)) = sig := by
  obtain ⟨hnd, hoct, hz, -⟩ := expandOf_some sig N wl h
  rw [expandOf_witOf sig N wl h cs]
  exact compressList_witOf sig hsig N hnd hoct hz cs

/-- The counter phase returns one counter per layer. -/
theorem aLayers_length (index : Index) (S0 : Signature) :
    ∀ n (M : Digest) (cs : List Nat), some cs ∈ support (aLayers index S0 n M) → cs.length = n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro M cs h
  match n with
  | 0 =>
    unfold aLayers at h
    simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
    subst h; rfl
  | 1 =>
    unfold aLayers at h
    simp only [support_bind, Set.mem_iUnion, exists_prop] at h
    obtain ⟨r, -, hr⟩ := h
    rcases r with _ | ⟨c, enc⟩
    · simp at hr
    · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr
      subst hr; rfl
  | k + 2 =>
    unfold aLayers at h
    split at h
    · simp only [support_bind, Set.mem_iUnion, exists_prop] at h
      obtain ⟨r, -, hr⟩ := h
      rcases r with _ | ⟨c, enc⟩
      · simp at hr
      · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
        obtain ⟨ends, -, leaf, -, root, -, r2, hr2, hr3⟩ := hr
        rcases r2 with _ | cs'
        · simp at hr3
        · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr3
          subst hr3
          rw [List.length_append, ih (k + 1) (by omega) root cs' hr2]; rfl
    · simp at h

/-- What a `some` output of the abstract expansion is: the partial witness of a successful
`Ref.expandOf` with counters written. -/
theorem aExpand_some (m : Message) (pk : SphincsSecurity.PublicKey) (σ : Bytes 6032)
    (w : Bytes 16384) (h : some w ∈ support (aExpand m pk σ)) :
    ∃ (N : Nat) (w0 : List Byte) (cs : List Nat),
      Ref.expandOf (Ref.toList σ) N = some w0 ∧ w = Ref.ofList 16384 (Ref.withCounters w0 cs) := by
  unfold aExpand at h
  simp only [support_bind, Set.mem_iUnion, exists_prop] at h
  obtain ⟨d, -, hd⟩ := h
  cases he : Ref.expandOf (Ref.toList σ) d.toNat with
  | none => rw [he] at hd; simp at hd
  | some w0 =>
    rw [he] at hd
    simp only [support_bind, Set.mem_iUnion, exists_prop] at hd
    obtain ⟨r, -, hr⟩ := hd
    rcases r with _ | M
    · simp at hr
    · simp only [support_bind, Set.mem_iUnion, exists_prop] at hr
      obtain ⟨r2, -, hr3⟩ := hr
      rcases r2 with _ | cs
      · simp at hr3
      · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at hr3
        exact ⟨d.toNat, w0, cs, he, hr3⟩

/-- **R2**: every successful run of the abstract expansion decodes to a signature compressing to
`σ`. -/
theorem aExpand_compress (m : Message) (pk : SphincsSecurity.PublicKey) (σ : Bytes 6032)
    (w : Bytes 16384) (h : some w ∈ support (aExpand m pk σ)) : compress (witDec w) = σ := by
  obtain ⟨N, w0, cs, he, rfl⟩ := aExpand_some m pk σ w h
  have hσ : (Ref.toList σ).length = 6032 := Ref.length_toList σ
  have hl0 : w0.length = 16384 := Ref.length_of_expandOf _ hσ _ _ he
  have hlen : (Ref.withCounters w0 cs).length = 16384 := by
    rw [length_withCounters _ _ (by omega), hl0]
  unfold witDec compress
  rw [Ref.toList_ofList 16384 _ hlen, compressList_expandOf _ hσ _ _ he, Ref.ofList_toList]

theorem mem_support_of_relabel {ι ι' R α : Type} (f : ι → ι') (oa : OracleComp (ι →ₒ R) α) (x : α)
    (hx : x ∈ support (relabel f oa)) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hx
  | query_bind t k ih =>
    rw [SigGolfCandidate.Bridge.relabel_query_bind] at hx
    rw [mem_support_bind_iff] at hx ⊢
    obtain ⟨u, -, hu⟩ := hx
    exact ⟨u, by simp, ih u hu⟩

/-- **The abstract expansion only outputs witnesses with zero W1a pads** (`padOf`, `Equiv/Verify.lean`):
`Ref.expandOf` zeroes the 48 bytes before every chain value and `Ref.withCounters` only writes the
counter bytes. -/
theorem padOf_of_mem_support_aExpand_relabel (m : Bytes 32) (pk' : SphincsSecurity.PublicKey)
    (σ : Bytes 6032) (w : Bytes 16384)
    (h : some w ∈ support (relabel fmtQ (aExpand m pk' σ))) :
    padOf (Ref.toList w) = fun _ _ => 0 := by
  obtain ⟨N, w0, cs, he, rfl⟩ := aExpand_some m pk' σ w (mem_support_of_relabel fmtQ _ _ h)
  have hσ : (Ref.toList σ).length = 6032 := Ref.length_toList σ
  have hl0 : w0.length = 16384 := Ref.length_of_expandOf _ hσ _ _ he
  have hlen : (Ref.withCounters w0 cs).length = 16384 := by
    rw [length_withCounters _ _ (by omega), hl0]
  obtain ⟨-, -, -, hwl⟩ := expandOf_some _ _ _ he
  have hvs : (Ref.sortLeaves (Ref.leavesOf N)).length = 15 := by
    simp [Ref.sortLeaves, Ref.leavesOf, Ref.porsK]
  funext lay i
  rw [Ref.toList_ofList 16384 _ hlen, hwl]
  unfold Ref.witnessList padOf
  rw [slice_W_pad _ hσ _ _ _ hvs cs lay i.val i.isLt 16 16 le_rfl (by omega),
    slice_W_pad _ hσ _ _ _ hvs cs lay i.val i.isLt 32 16 (by omega) le_rfl]
  decide

/-! ## R4: honest signatures round-trip -/

theorem ofList_dv (d : Digest) : Ref.ofList 16 (dv d) = d := by
  unfold dv; exact Ref.ofList_toList (n := 16) d

theorem map_range_getD {α β : Type} (l : List α) (f : α → β) (d : α) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h2)]
  rfl

theorem slice_flatten_dv (L : List Digest) (k : Nat) (hk : k < L.length) :
    Ref.slice (L.map dv).flatten (16 * k) 16 = dv (L.getD k 0) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x L ih =>
    cases k with
    | zero =>
      simp only [List.map_cons, List.flatten_cons, Nat.mul_zero, List.getD_cons_zero]
      rw [slice_append_left _ _ _ _ (by simp), slice_full _ _ (length_dv x)]
    | succ k =>
      simp only [List.map_cons, List.flatten_cons, List.getD_cons_succ]
      rw [slice_append_right _ _ _ (16 * k) _ (by simp; ring)]
      exact ih k (by simpa using hk)

theorem length_flatten_dv (L : List Digest) : (L.map dv).flatten.length = 16 * L.length := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih]; ring

theorem flatten_getD {α : Type} (L : List (List α)) (d : α) :
    ∀ j i, j < L.length → i < (L.getD j []).length →
      L.flatten.getD (((L.take j).map List.length).sum + i) d = (L.getD j []).getD i d := by
  induction L with
  | nil => intro j i hj; simp at hj
  | cons x L ih =>
    intro j i hj hi
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
      exact getD_append_left'' _ _ _ _ hi
    | succ j =>
      simp only [List.getD_cons_succ] at hi ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      rw [getD_append_right'' _ _ _ _ (by omega), show x.length + ((L.take j).map List.length).sum + i -
        x.length = ((L.take j).map List.length).sum + i by omega]
      exact ih j i (by simpa using hj) hi

/-! ### Slices of the compact signature -/

theorem length_secretsPart (S : Signature) :
    (List.ofFn fun s => dv (S.fts.secrets s)).flatten.length = 240 := by
  rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; rfl

theorem length_authPart (S : Signature) :
    ((((authNodes S).map dv).flatten ++ Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM)).length =
      1872 := by
  simp [Ref.porsM]

theorem slice_compress_rho (S : Signature) : Ref.slice (compressList S) 0 16 = dv S.randomness := by
  unfold compressList
  rw [List.append_assoc, List.append_assoc, slice_append_left _ _ _ _ (by simp),
    slice_full _ _ (length_dv _)]

theorem slice_compress_secret (S : Signature) (s : Nat) (hs : s < 15) :
    Ref.slice (compressList S) (16 + 16 * s) 16 = dv (S.fts.secrets ⟨s, hs⟩) := by
  unfold compressList
  rw [slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]; omega),
    slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart]; omega),
    slice_append_right _ _ _ (16 * s) _ (by simp),
    slice_flatten_ofFn (fun s => dv (S.fts.secrets s)) 16 ⟨s, hs⟩ 0 16 (16 * s)
      (fun _ _ => length_dv _) (by simp) (by ring),
    slice_full _ _ (length_dv _)]

theorem sigAuth_compress (S : Signature) (hS : (authNodes S).length ≤ 117) (k : Nat) (hk : k < 117) :
    Ref.sigAuth (compressList S) k =
      if k < (authNodes S).length then dv ((authNodes S).getD k 0) else Ref.zeros 16 := by
  rw [sigAuth_eq]
  unfold compressList
  rw [slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]; omega),
    slice_append_right _ _ _ (16 * k) _ (by
      simp only [List.length_append, length_dv, length_secretsPart]),
    slice_take _ _ _ _ (by unfold Ref.porsM; omega)]
  have hl := length_flatten_dv (authNodes S)
  split
  · next h =>
    rw [slice_append_left _ _ _ _ (by rw [hl]; omega), slice_flatten_dv _ _ h]
  · next h =>
    rw [slice_append_right _ _ _ (16 * (k - (authNodes S).length)) _ (by rw [hl]; omega)]
    unfold Ref.slice Ref.zeros
    rw [List.drop_replicate, List.take_replicate]
    congr 1
    unfold Ref.porsM; omega

theorem length_layersPart_take (S : Signature) (lay : Nat) (hlay : lay ≤ 5) :
    ((List.ofFn (layerBytes S)).take lay).flatten.length =
      ((List.range lay).map Ref.bodyBytes).sum := by
  rw [List.length_flatten, List.map_take, List.map_ofFn]
  have e : (List.length ∘ layerBytes S) = fun l : Layer => Ref.bodyBytes l.val :=
    funext fun l => length_layerBytes S l
  rw [e, ← map_range_eq_ofFn (n := SphincsSecurity.numLayers) Ref.bodyBytes, ← List.map_take,
    List.take_range, Nat.min_eq_left (by simp [SphincsSecurity.numLayers]; omega)]

theorem slice_compress_layer (S : Signature) (lay : Layer) (y len : Nat)
    (h : y + len ≤ Ref.bodyBytes lay.val) :
    Ref.slice (compressList S) (Ref.sigLayerOff lay.val + y) len = Ref.slice (layerBytes S lay) y len := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  unfold compressList
  rw [slice_append_right _ _ _ (((List.ofFn (layerBytes S)).take lay.val).flatten.length + y) _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]
      rw [length_layersPart_take S lay.val (by omega)]
      unfold Ref.sigLayerOff Ref.headBytes Ref.porsK Ref.porsM; omega),
    slice_flatten_take _ _ _ _ (by rw [List.length_ofFn]; exact lay.isLt) (by
      rw [getD_ofFn, dif_pos lay.isLt, length_layerBytes]; exact h)]
  rw [getD_ofFn, dif_pos lay.isLt]

theorem sigLayerOf_compress (S : Signature) (cs : List Nat) (lay : Layer) :
    sigLayerOf (compressList S) cs lay =
      ⟨Ref.ofList 4 (Ref.le32 (cs.getD lay.val 0)), (S.layers lay).chainValues, (S.layers lay).path⟩ := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  obtain ⟨t3, -, -⟩ := layer_table lay.val hl
  have hh := height_eq lay
  show LayerSignature.mk _ _ _ = LayerSignature.mk _ (S.layers lay).chainValues (S.layers lay).path
  rw [LayerSignature.mk.injEq]
  refine ⟨rfl, funext fun i => ?_, funext fun l => ?_⟩
  · have hi := i.isLt
    simp only [SphincsSecurity.numChains] at hi
    rw [slice_compress_layer S lay _ 16 (by omega)]
    unfold layerBytes
    rw [slice_append_left _ _ _ _ (by
        rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; simp [SphincsSecurity.numChains]; omega),
      slice_flatten_ofFn (fun i => dv ((S.layers lay).chainValues i)) 16 i 0 16 (16 * i.val)
        (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList _
  · have hlt : l.val < Ref.height lay.val := by rw [hh]; exact l.isLt
    rw [slice_compress_layer S lay _ 16 (by omega)]
    unfold layerBytes
    have hc : ((List.ofFn fun i => dv ((S.layers lay).chainValues i)).flatten).length = 672 := by
      rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; rfl
    rw [slice_append_right _ _ _ (16 * l.val) _ (by rw [hc]),
      slice_flatten_ofFn (fun j => dv ((S.layers lay).path j)) 16 l 0 16 (16 * l.val)
        (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList _

theorem expandOf_eq_some (sig : List Byte) (N : Nat) (hnd : (Ref.leavesOf N).Nodup)
    (hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 117)
    (hz : ∀ i, (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length ≤ i → i < 117 →
      Ref.sigAuth sig i = Ref.zeros 16) :
    Ref.expandOf sig N = some (Ref.witnessList sig (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N))
      (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1) := by
  unfold Ref.expandOf
  dsimp only
  split
  · next h => simp [hnd] at h
  split
  · next h => unfold Ref.porsM at h; omega
  split
  · next h =>
    exfalso
    simp only [Bool.not_eq_true', List.all_eq_false, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨i, hi, hne⟩ := h
    have hi' := List.mem_range'_1.mp hi
    exact hne (beq_iff_eq.mpr (hz i hi'.1 (by unfold Ref.porsM at hi'; omega)))
  rfl

theorem idxOf_ofFn {n : Nat} (f : Fin n → Nat) (hf : Function.Injective f) (r : Fin n) :
    (List.ofFn f).idxOf (f r) = r.val := by
  have hmem : f r ∈ List.ofFn f := List.mem_ofFn.mpr ⟨r, rfl⟩
  have hlt : (List.ofFn f).idxOf (f r) < (List.ofFn f).length := List.idxOf_lt_length_iff.mpr hmem
  have hget := List.getElem_idxOf hlt
  rw [List.getElem_ofFn] at hget
  have := hf hget
  exact congrArg Fin.val this

theorem normalized_congr {a a' : Fin 16} (h : a = a') {m m' p p' : Bool} (hm : m = m') (hp : p = p')
    (f : Fin a.val → Digest) (g : Fin a'.val → Digest)
    (hfg : ∀ i (hi : i < a.val), f ⟨i, hi⟩ = g ⟨i, h ▸ hi⟩) :
    SphincsSecurity.Segment.normalized a m p f = SphincsSecurity.Segment.normalized a' m' p' g := by
  subst h hm hp
  congr 1
  funext i
  exact hfg i.val i.isLt

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (j : Nat) (d : α) (d' : β) (hj : j < l.length) :
    (l.map f).getD j d' = f (l.getD j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

section honest
variable (leaves : IndexGroup → FtsLeaf) (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves)
  (rho : Digest) (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest)
  (layers : (lay : Layer) → LayerSignature lay)

/-- The honest signature. -/
abbrev honestSig : Signature := ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node, layers⟩

/-- The honest schedule. -/
abbrev hsched : List SphincsSecurity.Concrete.ScheduleSegment :=
  SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)

include hadm in
theorem authNodes_honestE :
    authNodes (honestSig leaves rho secret node layers) =
      ((hsched leaves).map (·.reads)).flatten.map fun p => node p.1 p.2 := by
  obtain ⟨hl, hr, -⟩ := schedule_admissible leaves hadm
  unfold authNodes
  have e : ∀ j : Fin SphincsSecurity.ftsSegments,
      List.ofFn ((honestSig leaves rho secret node layers).fts.segments j).nodes =
        ((hsched leaves).getD j.val default).reads.map fun p => node p.1 p.2 := by
    intro j
    have hj : j.val < (hsched leaves).length := by rw [hl]; exact j.isLt
    have hlen : ((hsched leaves).getD j.val default).reads.length ≤ 14 := by
      apply (hr _ _).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _
    show List.ofFn (fun i : Fin (((hsched leaves).getD j.val default).reads.length % 16) =>
      node (((hsched leaves).getD j.val default).reads.getD i.val (0, 0)).1
        (((hsched leaves).getD j.val default).reads.getD i.val (0, 0)).2) = _
    rw [← map_range_eq_ofFn (((hsched leaves).getD j.val default).reads.length % 16)
      (fun i => node (((hsched leaves).getD j.val default).reads.getD i (0, 0)).1
        (((hsched leaves).getD j.val default).reads.getD i (0, 0)).2),
      Nat.mod_eq_of_lt (by omega)]
    exact map_range_getD _ (fun p : Nat × Nat => node p.1 p.2) (0, 0)
  rw [List.ofFn_inj.mpr (funext e), List.map_flatten, List.map_map]
  have e3 : (List.ofFn fun j : Fin SphincsSecurity.ftsSegments =>
      ((hsched leaves).getD j.val default).reads.map fun p => node p.1 p.2) =
      (List.range (hsched leaves).length).map fun j =>
        ((hsched leaves).getD j default).reads.map fun p => node p.1 p.2 := by
    rw [hl, map_range_eq_ofFn]; rfl
  rw [e3, map_range_getD (hsched leaves) (fun s => s.reads.map fun p => node p.1 p.2)]
  rfl

include hadm in
theorem length_authNodes_honest :
    (authNodes (honestSig leaves rho secret node layers)).length =
      SphincsSecurity.Concrete.octopusSize (SphincsSecurity.Concrete.sortedLeaves leaves) := by
  rw [authNodes_honestE leaves hadm, List.length_map, (schedule_admissible leaves hadm).2.2]

end honest

/-- **R4**: the honest opening of admissible leaves (any randomness, secrets, node table and layers),
compressed and expanded with a digest whose leaf indices are `leaves`, gives a partial witness that
decodes to the signature with zero counters and, with any counters `cs` written, to the signature with
those counters. -/
theorem expandOf_honest (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) (N : Nat)
    (hN : ∀ r : IndexGroup, Ref.leafOf N r.val = (leaves r).val) (rho : Digest)
    (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest)
    (layers : (lay : Layer) → LayerSignature lay) :
    ∃ wl, wl.length = 16384 ∧
      Ref.expandOf (compressList ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node, layers⟩) N
        = some wl ∧
      witSig wl = ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node,
        fun lay => ⟨0, (layers lay).chainValues, (layers lay).path⟩⟩ ∧
      ∀ cs : List Nat, witSig (Ref.withCounters wl cs) = ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node,
        fun lay => ⟨Ref.ofList 4 (Ref.le32 (cs.getD lay.val 0)), (layers lay).chainValues,
          (layers lay).path⟩⟩ := by
  have hleaves : leavesN N = leaves := funext fun r => Fin.ext (hN r)
  have hv : Ref.leavesOf N = List.ofFn fun r => (leaves r).val := by rw [leavesOf_leavesN, hleaves]
  have hvs : Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves leaves := by
    rw [hv, sortLeaves_eq]
  have hnd : (Ref.leavesOf N).Nodup := by
    rw [hv, List.nodup_ofFn]; exact fun a b e => hadm.1 (Fin.ext e)
  have hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 117 := by rw [hvs]; exact hadm.2
  obtain ⟨-, -, hsch, hl29, hr, hn118, hsum, hb⟩ := sched_facts N hnd hoct
  rw [hleaves] at hsch hl29 hr hn118 hsum hb
  have hAN := authNodes_honestE leaves hadm rho secret node layers
  simp only [hsched] at hAN
  have hANl : (authNodes (honestSig leaves rho secret node layers)).length =
      ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten.length := by rw [hAN, List.length_map]
  have hcl := length_compressList (honestSig leaves rho secret node layers)
  have hauth := sigAuth_compress (honestSig leaves rho secret node layers) (by rw [hANl]; exact hn118)
  have hn2 : (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length =
      ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten.length := by rw [hsch]
  have hexp := expandOf_eq_some (compressList (honestSig leaves rho secret node layers)) N hnd hoct
    (fun i hi1 hi2 => by
      rw [hauth i hi2, if_neg (by rw [hANl]; omega)])
  have hvsl : (Ref.sortLeaves (Ref.leavesOf N)).length = 15 := by
    rw [hvs]; exact (SphincsSecurity.Completeness.sortedLeaves_facts leaves hadm.1).1
  have hs1 : (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1 = (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte := by
    rw [hsch]
  have hgen : ∀ cs : List Nat, witSig (Ref.withCounters (Ref.witnessList (compressList (honestSig leaves rho secret node layers))
      (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N))
      ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) cs) =
      ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node,
        fun lay => ⟨Ref.ofList 4 (Ref.le32 (cs.getD lay.val 0)), (layers lay).chainValues,
          (layers lay).path⟩⟩ := by
    intro cs
    unfold Ref.witnessList
    have hsegs : ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).length = 29 := by rw [List.length_map]; exact hl29
    have hn : (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).map (· % 16)).sum ≤ 117 := by rw [hsum]; exact hn118
    have hinj : Function.Injective fun r => (leaves r).val := fun a b e => hadm.1 (Fin.ext e)
    have hmod : ∀ sg ∈ hsched leaves, segByte sg % 16 = sg.reads.length := by
      intro sg hsg
      have := (hr sg hsg).1
      rw [segByte_val sg (by omega)]
      split <;> split <;> omega
    have hasum : ∀ j, asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j =
        ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).take j).map List.length).sum := by
      intro j
      unfold asum
      rw [← List.map_take, List.map_map, ← List.map_take, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun sg hsg => ?_)
      exact hmod sg (List.mem_of_mem_take hsg)
    unfold witSig
    rw [SphincsSecurity.Signature.mk.injEq]
    refine ⟨?_, ?_, funext fun lay => ?_⟩
    · rw [witRho_W _ hcl _ _ _ hvsl cs]
      unfold Ref.sigRho
      rw [slice_compress_rho]
      exact Ref.ofList_toList _
    · unfold witFts
      rw [SphincsSecurity.FtsSignature.mk.injEq]
      refine ⟨funext fun s => ?_, funext fun s => ?_, funext fun j => ?_⟩
      · -- slot codes
        rw [SphincsSecurity.Completeness.honestFts_perm]
        apply Fin.ext
        rw [Fin.val_castSucc, Fin.val_mk]
        have hs : s.val < 15 := s.isLt
        rw [witPi_W _ hcl _ _ _ hvsl cs s.val hs, hvs,
          SphincsSecurity.Completeness.sortedLeaves_getD leaves s.isLt, hv,
          idxOf_ofFn (fun r => (leaves r).val) hinj, Ref.byte_toNat]
        generalize ((SphincsSecurity.Concrete.sortedSlots leaves).getD s.val ⟨0, by decide⟩) = r
        have := r.isLt
        simp only [SphincsSecurity.ftsOpenings] at this
        omega
      · -- secrets
        rw [witSecret_W _ hcl _ _ _ hvsl cs s.val s.isLt, Ref.sigItem, slice_compress_secret _ s.val s.isLt,
          ofList_dv]
      · -- segments
        rw [SphincsSecurity.Completeness.honestFts_segments]
        unfold SphincsSecurity.Completeness.honestSegments SphincsSecurity.Concrete.ScheduleSegment.toSegment
        unfold segAt
        have hj : j.val < 29 := j.isLt
        have hjl : j.val < (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).length := by rw [hl29]; exact hj
        have hmem : (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default ∈ hsched leaves := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; exact List.getElem_mem _
        have hlen := (hr _ hmem).1
        have hw0 := wbyte_segPtr_W _ hcl (Ref.leavesOf N) _ _ hvsl cs hsegs hb hn j.val hj
        have hw : Ref.wbyte (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) (segPtr (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) j.val) =
            ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.length +
              (if ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).merge then 16 else 0) +
              32 * (if ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).parity then 1 else 0) := by
          rw [hw0, getD_map_lt _ segByte _ default 0 hjl, segByte_val _ (by omega)]
        refine normalized_congr (Fin.ext ?_) ?_ ?_ _ _ ?_
        · simp only [SphincsSecurity.Concrete.ScheduleSegment.folds, Fin.val_mk]
          rw [hw]
          generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
            j.val default) = sg at hlen ⊢
          rcases sg with ⟨mg, pr, rd⟩
          simp only at hlen ⊢
          cases mg <;> cases pr <;> simp <;> omega
        · rw [hw]
          generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
            j.val default) = sg at hlen ⊢
          rcases sg with ⟨mg, pr, rd⟩
          simp only at hlen ⊢
          cases mg <;> cases pr <;> simp <;> omega
        · rw [hw]
          generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
            j.val default) = sg at hlen ⊢
          rcases sg with ⟨mg, pr, rd⟩
          simp only at hlen ⊢
          cases mg <;> cases pr <;> simp <;> omega
        · intro i hi
          have hi' : i < ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).getD j.val 0 % 16 := by
            have h0 : i < Ref.wbyte (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) (segPtr (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) j.val) % 16 := hi
            rw [hw0] at h0; exact h0
          have hi2 : i < ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.length := by
            have h3 := hi'
            rw [getD_map_lt _ segByte _ default 0 hjl, segByte_val _ (by omega)] at h3
            generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default) = sg at h3 hlen ⊢
            rcases sg with ⟨mg, pr, rd⟩
            simp only at h3 hlen ⊢
            cases mg <;> cases pr <;> simp at h3 <;> omega
          have e1 := dv_node_W _ hcl (Ref.leavesOf N) _ _ hvsl cs hsegs hb hn j.val i hj hi'
          have ha1 := asum_succ ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val (by rw [hsegs]; exact hj)
          have ha2 : asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) (j.val + 1) ≤
              asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).length :=
            asum_mono _ (by rw [hsegs]; omega)
          rw [asum_length, hsum] at ha2
          have hk : asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i <
              (authNodes (honestSig leaves rho secret node layers)).length := by
            rw [hANl]; omega
          have e2 := hauth (asum ((SphincsSecurity.Concrete.schedule
            (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (by
              have := hk; rw [hANl] at this; omega)
          rw [if_pos hk] at e2
          have e3 : (authNodes (honestSig leaves rho secret node layers)).getD
              (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) 0 =
              node ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
                (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0)).1
                ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
                (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0)).2 := by
            rw [hAN]
            exact getD_map_lt _ (fun p : Nat × Nat => node p.1 p.2) _ (0, 0) 0 (by
              rw [hANl] at hk; exact hk)
          have hLj : ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).getD j.val [] =
              ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads :=
            by simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjl,
              Option.map_some, Option.getD_some]
          have e4 : (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
              (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0) =
              ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.getD i (0, 0) := by
            rw [hasum, flatten_getD _ (0, 0) j.val i (by rw [List.length_map]; exact hjl) (by
              rw [hLj]; exact hi2), hLj]
          calc wdig (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) (segPtr (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) j.val + 8 + 16 * i)
              = Ref.ofList 16 (dv (wdig (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) (segPtr (witOf (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) cs) j.val + 8 + 16 * i))) := (ofList_dv _).symm
            _ = Ref.ofList 16 (Ref.sigAuth (compressList (honestSig leaves rho secret node layers))
                (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i)) := by rw [e1]
            _ = _ := by rw [e2, ofList_dv, e3, e4]
    · rw [witLayer_W _ hcl _ _ _ hvsl cs, sigLayerOf_compress]
  have hz : Ref.ofList 4 (Ref.le32 0) = 0 := by decide
  refine ⟨Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N)
    (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte),
    Ref.length_witnessList _ hcl _ _ _ hvsl, by rw [hexp, hs1], ?_, hgen⟩
  rw [witnessList_withCounters_nil _ hcl _ _ _ hvsl, hgen []]
  simp only [List.getD_nil, hz]

end SigGolfCandidate.Equiv
