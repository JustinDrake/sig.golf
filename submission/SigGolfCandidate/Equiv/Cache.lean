import SigGolfCandidate.Equiv.Slices
import SigGolfCandidate.Equiv.Tree

/-!
# The cache codec

`cacheEnc : TopCache → Cache` writes `0^32 | region | tag | zeros` (the bytes key generation publishes);
`cacheDec : Cache → TopCache` reads the tag (the 48 bytes after the region) and the masked nodes at
`Ref.cacheNodeOff l j` from *arbitrary* bytes. The reference's region slice is the abstract region's
bytes (`toB_regionBytes_cacheDec`), its tag comparison is the abstract one (`cacheTag_iff`), and its
arithmetic MAC is the abstract one (`macTag_bytes`).
-/

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes)
open SphincsSecurity (Digest TopCache TopRegion MacTag MacKey)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- The 48 bytes of a tag: six little-endian 64-bit words. -/
def tagBytes (tag : MacTag) : List Byte := (List.ofFn fun j : Fin 6 => Ref.toList (n := 8) (tag j)).flatten

/-- Read a tag from 48 bytes. -/
def tagOfBytes (l : List Byte) : MacTag := fun j => Ref.ofList 8 (Ref.slice l (8 * j.val) 8)

theorem length_tagBytes (tag : MacTag) : (tagBytes tag).length = 48 :=
  length_flatten_ofFn _ 8 fun _ => Ref.length_toList _

theorem tagOfBytes_tagBytes (tag : MacTag) : tagOfBytes (tagBytes tag) = tag := by
  funext j
  unfold tagOfBytes tagBytes
  rw [slice_flatten_ofFn _ 8 j 0 8 _ (fun _ _ => Ref.length_toList _) (by rw [Ref.length_toList])
    (by ring), slice_full _ _ (Ref.length_toList _)]
  exact Ref.ofList_toList (n := 8) (tag j)

theorem tagBytes_tagOfBytes (l : List Byte) (hl : l.length = 48) : tagBytes (tagOfBytes l) = l := by
  unfold tagBytes tagOfBytes
  have e : (fun j : Fin 6 => Ref.toList (n := 8) (Ref.ofList 8 (Ref.slice l (8 * j.val) 8))) =
      fun j : Fin 6 => Ref.slice l (0 + 8 * j.val) 8 := by
    funext j
    rw [Ref.toList_ofList 8 _ (length_slice _ _ _ (by have := j.isLt; omega)), Nat.zero_add]
  rw [e, flatten_ofFn_slices]
  exact slice_full _ _ hl

theorem tagBytes_injective : Function.Injective tagBytes := fun a b h => by
  rw [← tagOfBytes_tagBytes a, h, tagOfBytes_tagBytes]

/-- The cache bytes of an abstract cache: 32 zero bytes, region, tag, zeros. -/
def cacheList (c : TopCache) : List Byte :=
  Ref.zeros 32 ++ toB (SphincsSecurity.regionBytes c.region) ++ tagBytes c.tag ++
    Ref.zeros (Ref.cacheBytes - 32 - Ref.regionBytes - 48)

/-- **The cache encoding** (what key generation publishes). -/
def cacheEnc (c : TopCache) : SigGolfCandidate.Cache := Ref.ofList SigGolfCandidate.CACHE_BYTES (cacheList c)

/-- Read an abstract cache from bytes. -/
def cacheOfList (l : List Byte) : TopCache :=
  ⟨tagOfBytes (Ref.cacheTag l), fun lv j => Ref.ofList 16 (Ref.cacheNode l lv j)⟩

/-- **The cache decoding** (what the signer reads from arbitrary bytes). -/
def cacheDec (b : SigGolfCandidate.Cache) : TopCache := cacheOfList (Ref.toList b)

theorem length_regionBytes (region : TopRegion) :
    (SphincsSecurity.regionBytes region).length = 65504 := by
  unfold SphincsSecurity.regionBytes
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  have : ∀ lv : Fin SphincsSecurity.maxLayerHeight,
      (List.length ∘ fun level : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn (region level)).flatMap (SphincsSecurity.bytesLE 16)) lv =
        16 * 2 ^ (SphincsSecurity.maxLayerHeight - lv.val) := by
    intro lv
    simp only [Function.comp, List.length_flatMap, List.map_ofFn, List.sum_ofFn]
    simp [SphincsSecurity.bytesLE, Nat.mul_comm]
  simp only [this]
  decide

theorem topN_eq (lv : Nat) :
    16 * Ref.topN lv = ((List.range lv).map fun k => 16 * 2 ^ (SphincsSecurity.maxLayerHeight - k)).sum := by
  unfold Ref.topN
  rw [← List.sum_map_mul_left]; rfl

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
  have e : ∀ lv : Fin SphincsSecurity.maxLayerHeight,
      (List.map UInt8.toBitVec ∘ fun level : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn ((cacheOfList l).region level)).flatMap (SphincsSecurity.bytesLE 16)) lv =
      Ref.slice l (32 + ((List.range lv).map fun k => 16 * 2 ^ (SphincsSecurity.maxLayerHeight - k)).sum)
        (16 * 2 ^ (SphincsSecurity.maxLayerHeight - lv.val)) := by
    intro lv
    simp only [Function.comp]
    rw [show List.map UInt8.toBitVec = toB from rfl, toB_flatMap_dv, List.map_ofFn]
    have e2 : (List.ofFn (dv ∘ (cacheOfList l).region lv)) =
        List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - lv.val)) =>
          Ref.slice l ((32 + 16 * Ref.topN lv) + 16 * j.val) 16 := by
      apply List.ofFn_inj.mpr
      funext j
      simp only [Function.comp, cacheOfList, Ref.cacheNode]
      have hb := node_bound lv j lv.isLt j.isLt
      rw [dv_ofList_slice _ _ (by rw [hl]; unfold SigGolfCandidate.CACHE_BYTES; omega)]
      unfold Ref.cacheNodeOff; congr 1; ring
    rw [e2, flatten_ofFn_slices, topN_eq]
  rw [List.ofFn_inj.mpr (funext e), flatten_ofFn_slices_var]
  rfl

theorem toB_regionBytes_cacheDec (b : SigGolfCandidate.Cache) :
    toB (SphincsSecurity.regionBytes (cacheDec b).region) = Ref.cacheRegion (Ref.toList b) :=
  toB_regionBytes_cacheOfList _ (Ref.length_toList b)

theorem length_cacheTag (l : List Byte) (hl : l.length = SigGolfCandidate.CACHE_BYTES) :
    (Ref.cacheTag l).length = 48 :=
  length_slice _ _ _ (by rw [hl, Ref.regionBytes_eq]; decide)

/-- The reference's tag comparison is the abstract one. -/
theorem cacheTag_iff (b : SigGolfCandidate.Cache) (tag : MacTag) :
    tagBytes tag = Ref.cacheTag (Ref.toList b) ↔ tag = (cacheDec b).tag := by
  have hl := length_cacheTag _ (Ref.length_toList b)
  constructor
  · intro h
    show tag = tagOfBytes (Ref.cacheTag (Ref.toList b))
    rw [← h]; exact (tagOfBytes_tagBytes tag).symm
  · intro h
    rw [h]
    exact tagBytes_tagOfBytes _ hl

/-! ## The arithmetic MAC -/

theorem chunks32_toB : ∀ data : List UInt8, Ref.chunks32 (toB data) = SphincsSecurity.chunks32 data
  | b0 :: b1 :: b2 :: b3 :: rest => by
      simp only [toB, List.map_cons, Ref.chunks32, SphincsSecurity.chunks32]
      rw [show List.map UInt8.toBitVec rest = toB rest from rfl, chunks32_toB rest]
      rfl
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl

theorem polyMac_eq (k : Nat) (chunks : List Nat) : Ref.polyMac k chunks = SphincsSecurity.polyMac k chunks :=
  rfl

/-- Tag word `j` is the reference's word `j % 2` of key answer `j / 2`. -/
theorem macTag_toNat (key : MacKey) (data : List UInt8) (j : Fin 6) :
    (SphincsSecurity.macTag key data j).toNat =
      (Ref.polyMac (Ref.answerWord (key ⟨j.val / 2, by omega⟩) (2 * (j.val % 2)) % 2 ^ 61)
          (Ref.chunks32 (toB data)) +
        Ref.answerWord (key ⟨j.val / 2, by omega⟩) (2 * (j.val % 2) + 1)) % 2 ^ 64 := by
  unfold SphincsSecurity.macTag SphincsSecurity.macKeyWord SphincsSecurity.macPadWord Ref.answerWord
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, chunks32_toB, polyMac_eq, Nat.add_mod_mod,
    Nat.mod_add_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 61 ≤ 64))]
  rw [show 64 * (2 * (j.val % 2)) = 128 * (j.val % 2) by ring,
    show 64 * (2 * (j.val % 2) + 1) = 128 * (j.val % 2) + 64 by ring]
  exact (Nat.add_mod_mod _ _ _).symm

/-- The reference's tag bytes are the abstract tag's. -/
theorem macTag_bytes (key : MacKey) (data : List UInt8) :
    Ref.macTag (key 0) (key 1) (key 2) (toB data) = tagBytes (SphincsSecurity.macTag key data) := by
  unfold Ref.macTag Ref.macWords tagBytes
  have hw : ∀ j : Fin 6, Ref.toList (n := 8) (SphincsSecurity.macTag key data j) =
      Ref.leBytes 8 ((Ref.polyMac (Ref.answerWord (key ⟨j.val / 2, by omega⟩) (2 * (j.val % 2)) % 2 ^ 61)
          (Ref.chunks32 (toB data)) +
        Ref.answerWord (key ⟨j.val / 2, by omega⟩) (2 * (j.val % 2) + 1)) % 2 ^ 64) := by
    intro j
    rw [Ref.toList_eq_map, macTag_toNat]
    rfl
  simp only [hw, List.ofFn_succ, List.ofFn_zero]
  rfl

/-- A cached node, as the reference reads it. -/
theorem dv_cacheDec_node (b : SigGolfCandidate.Cache) (lv j : Nat) (hlv : lv < SphincsSecurity.maxLayerHeight)
    (hj : j < 2 ^ (SphincsSecurity.maxLayerHeight - lv)) :
    dv ((cacheDec b).node lv j) = Ref.cacheNode (Ref.toList b) lv j := by
  unfold TopCache.node
  rw [dif_pos hlv, dif_pos hj]
  show dv (Ref.ofList 16 (Ref.cacheNode (Ref.toList b) lv j)) = _
  have hb := node_bound lv j hlv hj
  exact dv_ofList_slice _ _ (by rw [Ref.length_toList]; unfold SigGolfCandidate.CACHE_BYTES; omega)

theorem length_cacheList (c : TopCache) : (cacheList c).length = SigGolfCandidate.CACHE_BYTES := by
  simp only [cacheList, List.length_append, length_tagBytes, length_toB, length_regionBytes,
    Ref.length_zeros]
  decide

/-! ## Decoding what key generation publishes -/

theorem toB_regionBytes_nested (region : TopRegion) :
    toB (SphincsSecurity.regionBytes region) =
      (List.ofFn fun lv : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn fun j => dv (region lv j)).flatten).flatten := by
  unfold SphincsSecurity.regionBytes
  rw [show toB = List.map UInt8.toBitVec from rfl, List.map_flatten, List.map_ofFn]
  refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun lv => ?_))
  simp only [Function.comp]
  rw [show List.map UInt8.toBitVec = toB from rfl, toB_flatMap_dv, List.map_ofFn]
  rfl

theorem take_region_length (region : TopRegion) (l : Nat) (hl : l ≤ SphincsSecurity.maxLayerHeight) :
    ((List.ofFn fun lv : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn fun j => dv (region lv j)).flatten).take l).flatten.length = 16 * Ref.topN l := by
  induction l with
  | zero => simp [Ref.topN]
  | succ l ih =>
    rw [List.take_add_one, List.flatten_append, List.length_append, ih (by omega),
      List.getElem?_ofFn, dif_pos (by omega)]
    simp only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]
    simp only [Ref.topN, List.range_succ, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    rw [show Ref.topH = SphincsSecurity.maxLayerHeight from rfl]; ring

theorem slice_region (region : TopRegion) (lv : Fin SphincsSecurity.maxLayerHeight)
    (j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - lv.val))) :
    Ref.slice (toB (SphincsSecurity.regionBytes region)) (16 * (Ref.topN lv + j)) 16 =
      dv (region lv j) := by
  rw [toB_regionBytes_nested, show 16 * (Ref.topN lv + j) = 16 * Ref.topN lv + 16 * j by ring,
    ← take_region_length region lv (by have := lv.isLt; omega)]
  rw [slice_flatten_take _ _ _ _ (by simp) (by
      rw [getD_ofFn, dif_pos lv.isLt, length_flatten_ofFn _ 16 (fun _ => length_dv _)]
      exact (by have := j.isLt; omega :
        16 * j.val + 16 ≤ 16 * 2 ^ (SphincsSecurity.maxLayerHeight - lv.val))),
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
  · show tagOfBytes (Ref.slice (cacheList ⟨tag, region⟩) (32 + Ref.regionBytes) 48) = tag
    rw [cacheList, List.append_assoc, slice_append_right _ _ _ 0 _
        (by rw [List.length_append, Ref.length_zeros, length_toB, length_regionBytes, Ref.regionBytes_eq]),
      slice_append_left _ _ _ _ (by rw [length_tagBytes]), slice_full _ _ (length_tagBytes _)]
    exact tagOfBytes_tagBytes tag
  · funext lv j
    show Ref.ofList 16 (Ref.slice (cacheList ⟨tag, region⟩) (Ref.cacheNodeOff lv j) 16) = region lv j
    have hb := node_bound lv j lv.isLt j.isLt
    rw [cacheList, List.append_assoc, List.append_assoc, slice_append_right _ _ _ (16 * (Ref.topN lv + j)) _
        (by rw [Ref.length_zeros]; unfold Ref.cacheNodeOff; ring),
      slice_append_left _ _ _ _ (by rw [length_toB, length_regionBytes]; unfold Ref.cacheNodeOff at hb; omega),
      slice_region]
    exact Ref.ofList_toList (n := 16) _

end SigGolfCandidate.Equiv
