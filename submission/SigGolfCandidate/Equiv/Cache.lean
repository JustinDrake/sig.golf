import SigGolfCandidate.Equiv.Slices
import SigGolfCandidate.Equiv.Tree

/-!
# The cache codec

`cacheEnc : TopCache → Cache` writes `tag | region | zeros` (the bytes key generation publishes);
`cacheDec : Cache → TopCache` reads the tag (bytes `0..32`) and the masked nodes at
`Ref.cacheNodeOff l j` from *arbitrary* bytes. The reference's region slice is the abstract region's
bytes (`toB_regionBytes_cacheDec`), and its tag comparison is the abstract one (`cacheTag_iff`).
-/

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes)
open SphincsSecurity (Digest TopCache TopRegion)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- The cache bytes of an abstract cache: tag, region, zeros. -/
def cacheList (c : TopCache) : List Byte :=
  Ref.zeros Ref.cachePadBytes ++ Ref.toList (n := 32) c.tag ++ toB (SphincsSecurity.regionBytes c.region) ++
    Ref.zeros (Ref.cacheBytes - Ref.cachePadBytes - 32 - Ref.regionBytes)

/-- **The cache encoding** (what key generation publishes). -/
def cacheEnc (c : TopCache) : SigGolfCandidate.Cache := Ref.ofList SigGolfCandidate.CACHE_BYTES (cacheList c)

/-- Read an abstract cache from bytes. -/
def cacheOfList (l : List Byte) : TopCache :=
  ⟨Ref.ofList 32 (Ref.cacheTag l), fun lv j => Ref.ofList 16 (Ref.cacheNode l (lv.val + 1) j)⟩

/-- **The cache decoding** (what the signer reads from arbitrary bytes). -/
def cacheDec (b : SigGolfCandidate.Cache) : TopCache := cacheOfList (Ref.toList b)

theorem length_regionBytes (region : TopRegion) :
    (SphincsSecurity.regionBytes region).length = 32736 := by
  unfold SphincsSecurity.regionBytes
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  have : ∀ lv : Fin (SphincsSecurity.maxLayerHeight - 1),
      (List.length ∘ fun level : Fin (SphincsSecurity.maxLayerHeight - 1) =>
        (List.ofFn (region level)).flatMap (SphincsSecurity.bytesLE 16)) lv =
        16 * 2 ^ (SphincsSecurity.maxLayerHeight - (lv.val + 1)) := by
    intro lv
    simp only [Function.comp, List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    simp [SphincsSecurity.bytesLE, Nat.mul_comm]
  simp only [this]
  decide

/-- Number of internal nodes before cache rowl (actual levell+1). -/
def cacheN (l : Nat) : Nat :=
  ((List.range l).map fun k => 2 ^ (SphincsSecurity.maxLayerHeight - (k + 1))).sum

theorem cacheN_succ (l : Nat) : cacheN (l + 1) = cacheN l + 2 ^ (SphincsSecurity.maxLayerHeight - (l + 1)) := by
  simp [cacheN, List.range_succ]

theorem topN_shift (l : Nat) : Ref.topN (l + 1) = Ref.topN 1 + cacheN l := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have hs : Ref.topN (l + 1 + 1) = Ref.topN (l + 1) + 2 ^ (Ref.topH - (l + 1)) := by
      simp [Ref.topN, List.range_succ, Nat.add_assoc]
    rw [hs, ih, cacheN_succ]
    exact Nat.add_assoc _ _ _

theorem cacheN_eq (lv : Nat) :
    16 * cacheN lv = ((List.range lv).map fun k => 16 * 2 ^ (SphincsSecurity.maxLayerHeight - (k + 1))).sum := by
  unfold cacheN
  rw [← List.sum_map_mul_left]

theorem cacheNodeOff_row (lv j : Nat) :
    Ref.cacheNodeOff (lv + 1) j = Ref.cachePadBytes + 32 + 16 * (cacheN lv + j) := by
  unfold Ref.cacheNodeOff Ref.cachePadBytes
  rw [topN_shift]
  ring

theorem node_bound (lv j : Nat) (hlv : lv < SphincsSecurity.maxLayerHeight)
    (hj : j < 2 ^ (SphincsSecurity.maxLayerHeight - lv)) :
    Ref.cacheNodeOff lv j + 16 ≤ 32 + 65504 := by
  have key : ∀ lv < SphincsSecurity.maxLayerHeight,
      Ref.topN lv + 2 ^ (SphincsSecurity.maxLayerHeight - lv) ≤ 4094 := by decide
  have := key lv hlv
  unfold Ref.cacheNodeOff; omega

theorem toB_regionBytes_cacheOfList (l : List Byte) (hl : l.length = SigGolfCandidate.CACHE_BYTES) :
    toB (SphincsSecurity.regionBytes (cacheOfList l).region) = Ref.cacheRegion l := by
  unfold SphincsSecurity.regionBytes
  simp only [toB, List.map_flatten, List.map_ofFn]
  have e : ∀ lv : Fin (SphincsSecurity.maxLayerHeight - 1),
      (List.map UInt8.toBitVec ∘ fun level : Fin (SphincsSecurity.maxLayerHeight - 1) =>
        (List.ofFn ((cacheOfList l).region level)).flatMap (SphincsSecurity.bytesLE 16)) lv =
      Ref.slice l (Ref.cachePadBytes + 32 + ((List.range lv).map fun k => 16 * 2 ^ (SphincsSecurity.maxLayerHeight - (k + 1))).sum)
        (16 * 2 ^ (SphincsSecurity.maxLayerHeight - (lv.val + 1))) := by
    intro lv
    simp only [Function.comp]
    rw [show List.map UInt8.toBitVec = toB from rfl, toB_flatMap_dv, List.map_ofFn]
    have e2 : (List.ofFn (dv ∘ (cacheOfList l).region lv)) =
        List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - (lv.val + 1))) =>
          Ref.slice l ((Ref.cachePadBytes + 32 + 16 * cacheN lv) + 16 * j.val) 16 := by
      apply List.ofFn_inj.mpr
      funext j
      simp only [Function.comp, cacheOfList, Ref.cacheNode]
      have hb := node_bound (lv.val + 1) j (by have := lv.isLt; omega) j.isLt
      rw [dv_ofList_slice _ _ (by rw [hl]; unfold SigGolfCandidate.CACHE_BYTES; omega)]
      rw [cacheNodeOff_row]; congr 1; ring
    rw [e2, flatten_ofFn_slices, cacheN_eq]
  rw [List.ofFn_inj.mpr (funext e), flatten_ofFn_slices_var]
  rfl

theorem toB_regionBytes_cacheDec (b : SigGolfCandidate.Cache) :
    toB (SphincsSecurity.regionBytes (cacheDec b).region) = Ref.cacheRegion (Ref.toList b) :=
  toB_regionBytes_cacheOfList _ (Ref.length_toList b)

theorem length_cacheTag (l : List Byte) (hl : l.length = SigGolfCandidate.CACHE_BYTES) :
    (Ref.cacheTag l).length = 32 :=
  length_slice _ _ _ (by rw [hl]; decide)

/-- The reference's tag comparison is the abstract one. -/
theorem cacheTag_iff (b : SigGolfCandidate.Cache) (tag : SphincsSecurity.HashOutput) :
    Ref.toList (n := 32) tag = Ref.cacheTag (Ref.toList b) ↔ tag = (cacheDec b).tag := by
  have hl := length_cacheTag _ (Ref.length_toList b)
  constructor
  · intro h
    show tag = Ref.ofList 32 (Ref.cacheTag (Ref.toList b))
    rw [← h]; exact (Ref.ofList_toList (n := 32) tag).symm
  · intro h
    rw [h]
    exact Ref.toList_ofList 32 _ hl

/-- A cached node, as the reference reads it. -/
theorem dv_cacheDec_node (b : SigGolfCandidate.Cache) (lv j : Nat) (hpos : 0 < lv) (hlv : lv < SphincsSecurity.maxLayerHeight)
    (hj : j < 2 ^ (SphincsSecurity.maxLayerHeight - lv)) :
    dv ((cacheDec b).node lv j) = Ref.cacheNode (Ref.toList b) lv j := by
  unfold TopCache.node
  rw [dif_pos ⟨hpos, hlv⟩, dif_pos hj]
  simp only [cacheDec, cacheOfList, Nat.sub_add_cancel (by omega : 1 ≤ lv)]
  show dv (Ref.ofList 16 (Ref.cacheNode (Ref.toList b) lv j)) = _
  have hb := node_bound lv j hlv hj
  exact dv_ofList_slice _ _ (by rw [Ref.length_toList]; unfold SigGolfCandidate.CACHE_BYTES; omega)

theorem length_cacheList (c : TopCache) : (cacheList c).length = SigGolfCandidate.CACHE_BYTES := by
  simp only [cacheList, List.length_append, Ref.length_toList, length_toB, length_regionBytes,
    Ref.length_zeros]
  decide

/-! ## Decoding what key generation publishes -/

theorem toB_regionBytes_nested (region : TopRegion) :
    toB (SphincsSecurity.regionBytes region) =
      (List.ofFn fun lv : Fin (SphincsSecurity.maxLayerHeight - 1) =>
        (List.ofFn fun j => dv (region lv j)).flatten).flatten := by
  unfold SphincsSecurity.regionBytes
  rw [show toB = List.map UInt8.toBitVec from rfl, List.map_flatten, List.map_ofFn]
  refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun lv => ?_))
  simp only [Function.comp]
  rw [show List.map UInt8.toBitVec = toB from rfl, toB_flatMap_dv, List.map_ofFn]
  rfl

theorem take_region_length (region : TopRegion) (l : Nat) (hl : l ≤ SphincsSecurity.maxLayerHeight - 1) :
    ((List.ofFn fun lv : Fin (SphincsSecurity.maxLayerHeight - 1) =>
        (List.ofFn fun j => dv (region lv j)).flatten).take l).flatten.length = 16 * cacheN l := by
  induction l with
  | zero => simp [cacheN]
  | succ l ih =>
    rw [List.take_add_one, List.flatten_append, List.length_append, ih (by omega),
      List.getElem?_ofFn, dif_pos (by omega)]
    simp only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]
    simp only [cacheN, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    ring

theorem slice_region (region : TopRegion) (lv : Fin (SphincsSecurity.maxLayerHeight - 1))
    (j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - (lv.val + 1)))) :
    Ref.slice (toB (SphincsSecurity.regionBytes region)) (16 * (cacheN lv + j)) 16 =
      dv (region lv j) := by
  rw [toB_regionBytes_nested, show 16 * (cacheN lv + j) = 16 * cacheN lv + 16 * j by ring,
    ← take_region_length region lv (by have := lv.isLt; omega)]
  rw [slice_flatten_take _ _ _ _ (by simp) (by
      rw [getD_ofFn, dif_pos lv.isLt, length_flatten_ofFn _ 16 (fun _ => length_dv _)]
      exact (by have := j.isLt; omega :
        16 * j.val + 16 ≤ 16 * 2 ^ (SphincsSecurity.maxLayerHeight - (lv.val + 1)))),
    getD_ofFn, dif_pos lv.isLt,
    slice_flatten_ofFn _ 16 j 0 16 _ (fun _ _ => length_dv _) (by simp) (by ring),
    slice_full _ _ (length_dv _)]

/-- The signer decodes exactly the cache key generation encoded. -/
theorem cacheDec_cacheEnc (c : TopCache) : cacheDec (cacheEnc c) = c := by
  have hl := length_cacheList c
  unfold cacheDec cacheEnc
  rw [Ref.toList_ofList _ _ hl]
  cases c with | mk tag region =>
  unfold cacheOfList
  refine congrArg₂ TopCache.mk ?_ ?_
  · change Ref.ofList 32 (Ref.slice (cacheList ⟨tag, region⟩) Ref.cachePadBytes 32) = tag
    simp only [cacheList, List.append_assoc]
    rw [slice_append_right _ _ _ 0 _ (by simp [Ref.length_zeros]),
      slice_append_left _ _ _ _ (by rw [Ref.length_toList]),
      slice_full _ _ (Ref.length_toList _)]
    exact Ref.ofList_toList (n := 32) tag
  · funext lv j
    change Ref.ofList 16 (Ref.slice (cacheList ⟨tag, region⟩) (Ref.cacheNodeOff (lv.val + 1) j) 16) = region lv j
    have hb := node_bound (lv.val + 1) j (by have := lv.isLt; omega) j.isLt
    rw [cacheNodeOff_row] at hb ⊢
    simp only [cacheList, List.append_assoc]
    rw [slice_append_right _ _ _ (32 + 16 * (cacheN lv + j)) _ (by rw [Ref.length_zeros]; ring),
      slice_append_right _ _ _ (16 * (cacheN lv + j)) _ (by rw [Ref.length_toList]),
      slice_append_left _ _ _ _ (by
        rw [length_toB, length_regionBytes]
        have hp : Ref.cachePadBytes = 32768 := by decide
        rw [hp] at hb; omega), slice_region]
    exact Ref.ofList_toList (n := 16) _

end SigGolfCandidate.Equiv
