import SigGolfCandidate.Equiv.Wit
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes

/-!
# Honest hash inputs

`Honest x`: `x` starts with the protocol byte `1`, its length is the one fixed by its tag
(byte 1), a chain input (tag 1) has the zero parameter slot (bytes 16..31) and a position below
`2^27`, a node input (tags 3, 10) names a node of its tree (`NodeOk`: level `1 ≤ λ ≤ h`, index
`j < 2^(h - λ)`), and the digest input (tag 12) has zero parameter and root slots. The oracle input
format (`fmtQ`: split chain position, heap-index node tweak, one-block digest) is injective on
honest inputs, and every query of the abstract key generation, signer and verifier (with the
parameter `P = 0`) is honest, for all inputs and oracle answers.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes Query)
open SigGolfCandidate.Bridge (AllQ allQ_pure allQ_bind allQ_query allQ_map)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message Signature)
open SphincsSecurity.Concrete (porsTree ftsHeapIndex)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- The input length of each tag. -/
def tagLen : Nat → Nat
  | 0 => 64 | 1 => 48 | 2 => 704 | 3 => 64 | 4 => 52 | 7 => 64 | 8 => 64 | 9 => 48 | 10 => 64
  | 12 => 96 | 13 => 64 | 14 => 65568 | _ => 0

/-- The position field (bytes `4 .. 8`, little endian) of an input. -/
def posField (x : List UInt8) : Nat := Ref.leNat (Ref.slice (toB x) 4 4)

/-- The index field (bytes `12 .. 16`, little endian) of an input. -/
def idxField (x : List UInt8) : Nat := Ref.leNat (Ref.slice (toB x) 12 4)

/-- A hypertree node input (tag 3) names a node of its tree: level `1 ≤ λ ≤ h` and index
`j < 2^(h - λ)`, `h = Ref.nodeHeight` (the height of the layer byte's tree). PORS nodes (tag 10) are
queried in their real block form (heap index), zero padded, so they need no condition. -/
def NodeOk (x : List UInt8) : Prop :=
  1 ≤ posField x ∧ posField x ≤ Ref.nodeHeight (toB x) ∧
    idxField x < 2 ^ (Ref.nodeHeight (toB x) - posField x)

/-- An honest hash input: protocol byte `1`, the length fixed by the tag byte, and
* a chain input (tag 1): the zero parameter slot (bytes `16 .. 32`) and a position below `2^27`;
* a hypertree node input (tag 3): `NodeOk`;
* the digest input (tag 12): the zero parameter slot and the zero root slot (bytes `48 .. 64`). -/
def Honest (x : List UInt8) : Prop :=
  x.head? = some 1 ∧ x.length = tagLen (x.getD 1 0).toNat ∧
    (x.getD 1 0 = 1 → (x.drop 16).take 16 = List.replicate 16 0 ∧ posField x < 2 ^ 27) ∧
    (x.getD 1 0 = 3 → NodeOk x) ∧
    (x.getD 1 0 = 12 → (x.drop 16).take 16 = List.replicate 16 0 ∧
      (x.drop 48).take 16 = List.replicate 16 0)

theorem honest_head (x : List UInt8) (h : Honest x) : x.head? = some 1 := h.1

/-! ## The input format is injective on honest inputs -/

/-- The bytes of a query. -/
def qbytes (q : Query) : List Byte := Ref.toList q.2

theorem qbytes_pad64 (z : List Byte) : qbytes (Ref.pad64 z) = Ref.padTo64 z :=
  Ref.toList_ofList _ _ (Ref.length_padTo64 z)

theorem getD_toB (x : List UInt8) (i : Nat) : (toB x).getD i 0 = (x.getD i 0).toBitVec := by
  simp only [toB, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x[i]? <;> rfl

theorem tagLen_cases (n : Nat) : tagLen n = 0 ∨ 48 ≤ tagLen n := by
  unfold tagLen; split <;> simp

theorem honest_length (x : List UInt8) (h : Honest x) : 48 ≤ x.length := by
  rcases tagLen_cases (x.getD 1 0).toNat with h0 | h0
  · have hl : x.length = 0 := h.2.1.trans h0
    have hh := h.1
    rw [List.length_eq_zero_iff.mp hl] at hh
    simp at hh
  · rw [h.2.1]; exact h0

theorem getD_append_left' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

/-- A 4-byte list is the `LE32` of its value. -/
theorem le32_leNat (l : List Byte) (h : l.length = 4) : Ref.le32 (Ref.leNat l) = l := by
  apply List.ext_getElem (by simp [h])
  intro i h1 h2
  simp only [Ref.le32, Ref.leBytes, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_toNat_eq
  rw [Ref.byte_toNat, Ref.leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
  rfl

theorem hlength_slice (l : List Byte) (a n : Nat) (h : a + n ≤ l.length) :
    (Ref.slice l a n).length = n := by
  simp [Ref.slice]; omega

/-- `l = l[0..a) ++ l[a..a+n) ++ l[a+n..)`. -/
theorem take_add_slice (l : List Byte) (a n : Nat) :
    l.take (a + n) = l.take a ++ Ref.slice l a n := List.take_add ..

/-- The zero slots of an input. -/
theorem slice_toB_zero (x : List UInt8) (a : Nat) (h : (x.drop a).take 16 = List.replicate 16 0) :
    Ref.slice (toB x) a 16 = Ref.zeros 16 := by
  simp only [Ref.slice, toB, ← List.map_drop, ← List.map_take, h]
  rfl

theorem getD_take4 (z : List Byte) (i : Nat) (hi : i < 4) : (z.take 4).getD i 0 = z.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, hi]

theorem nodeHeight_take (z : List Byte) : Ref.nodeHeight z = Ref.nodeHeight (z.take 4) := by
  unfold Ref.nodeHeight
  rw [getD_take4 z 2 (by omega)]

theorem height_le (l : Nat) : Ref.height l ≤ 11 := by
  unfold Ref.height Ref.heights
  rcases l with _ | _ | _ | _ | _ | l <;> simp

theorem nodeHeight_le (z : List Byte) : Ref.nodeHeight z ≤ 11 := by
  unfold Ref.nodeHeight; exact height_le _

/-- The heap numbering `(λ, j) ↦ 2^(h - λ) + j` is injective on `1 ≤ λ ≤ h`, `j < 2^(h - λ)`. -/
theorem heapIndex_inj (h a j b k : Nat) (ha : a ≤ h) (hb : b ≤ h)
    (hj : j < 2 ^ (h - a)) (hk : k < 2 ^ (h - b)) (e : Ref.heapIndex h a j = Ref.heapIndex h b k) :
    a = b ∧ j = k := by
  unfold Ref.heapIndex at e
  have hab : h - a = h - b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have : 2 ^ (h - a + 1) ≤ 2 ^ (h - b) := Nat.pow_le_pow_right (by omega) hlt
      rw [Nat.pow_succ] at this; omega
    · have : 2 ^ (h - b + 1) ≤ 2 ^ (h - a) := Nat.pow_le_pow_right (by omega) hlt
      rw [Nat.pow_succ] at this; omega
  refine ⟨by omega, ?_⟩
  rw [hab] at e; omega

theorem heapIndex_lt (h a j : Nat) (hh : h ≤ 11) (hj : j < 2 ^ (h - a)) :
    Ref.heapIndex h a j < 2 ^ 32 := by
  unfold Ref.heapIndex
  have : 2 ^ (h - a) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem tag_toB (x : List UInt8) (t : UInt8) (h : x.getD 1 0 = t) : (toB x).getD 1 0 = t.toBitVec := by
  rw [getD_toB, h]

/-- An input from its pieces. -/
theorem decomp (z : List Byte) (a n₁ n₂ n₃ : Nat) :
    z = z.take a ++ Ref.slice z a n₁ ++ Ref.slice z (a + n₁) n₂ ++ Ref.slice z (a + n₁ + n₂) n₃ ++
      z.drop (a + n₁ + n₂ + n₃) := by
  rw [← take_add_slice, ← take_add_slice, ← take_add_slice, List.take_append_drop]

theorem fmtQ_injOn : Set.InjOn fmtQ Honest := by
  intro x hx y hy hxy
  have hL : Ref.fmtList (toB x) = Ref.fmtList (toB y) := by
    rw [← Ref.toList_fmt, ← Ref.toList_fmt]; exact congrArg (fun q : Query => Ref.toList q.2) hxy
  have hx2 := honest_length x hx
  have hy2 := honest_length y hy
  have ht : x.getD 1 0 = y.getD 1 0 := by
    have : (Ref.fmtList (toB x)).getD 1 0 = (Ref.fmtList (toB y)).getD 1 0 := by rw [hL]
    rw [Ref.getD_fmtList _ _ (Or.inl (by omega)), Ref.getD_fmtList _ _ (Or.inl (by omega)),
      getD_toB, getD_toB] at this
    exact UInt8.toBitVec_inj.mp this
  have hlen : x.length = y.length := by rw [hx.2.1, hy.2.1, ht]
  apply toB_injective
  have lx : (toB x).length = x.length := length_toB x
  have ly : (toB y).length = y.length := length_toB y
  set z := toB x with hz
  set w := toB y with hw
  by_cases h1 : x.getD 1 0 = 1
  · have hl48 : x.length = 48 := by rw [hx.2.1, h1]; rfl
    have hcx : Ref.IsChainFmt z := ⟨by omega, tag_toB x 1 h1⟩
    have hcy : Ref.IsChainFmt w := ⟨by omega, tag_toB y 1 (ht ▸ h1)⟩
    unfold Ref.fmtList at hL
    rw [if_pos hcx, if_pos hcy] at hL
    unfold Ref.chainBlock at hL
    obtain ⟨e1, eE⟩ := List.append_inj hL (by simp [Ref.slice]; omega)
    obtain ⟨e2, -⟩ := List.append_inj e1 (by simp [Ref.slice]; omega)
    obtain ⟨e3, eC⟩ := List.append_inj e2 (by simp [Ref.slice]; omega)
    obtain ⟨eA, eB⟩ := List.append_inj e3 (by simp; omega)
    obtain ⟨hPx, hpx⟩ := hx.2.2.1 h1
    obtain ⟨hPy, hpy⟩ := hy.2.2.1 (ht ▸ h1)
    have eB' := congrArg Ref.leNat eB
    rw [Ref.leNat_le32, Ref.leNat_le32] at eB'
    unfold posField at hpx hpy
    rw [← hz] at hpx; rw [← hw] at hpy
    have bx : Ref.splitP (Ref.leNat (Ref.slice z 4 4)) < 2 ^ 32 := by unfold Ref.splitP; omega
    have bw : Ref.splitP (Ref.leNat (Ref.slice w 4 4)) < 2 ^ 32 := by unfold Ref.splitP; omega
    rw [Nat.mod_eq_of_lt bx, Nat.mod_eq_of_lt bw] at eB'
    have ep : Ref.leNat (Ref.slice z 4 4) = Ref.leNat (Ref.slice w 4 4) := by
      unfold Ref.splitP at eB'; omega
    have e4 : Ref.slice z 4 4 = Ref.slice w 4 4 := by
      rw [← le32_leNat (Ref.slice z 4 4) (hlength_slice _ _ _ (by omega)),
        ← le32_leNat (Ref.slice w 4 4) (hlength_slice _ _ _ (by omega)), ep]
    have eP : Ref.slice z 16 16 = Ref.slice w 16 16 := by
      rw [slice_toB_zero x 16 hPx, slice_toB_zero y 16 hPy]
    have dz : z = z.take 4 ++ Ref.slice z 4 4 ++ Ref.slice z 8 8 ++ Ref.slice z 16 16 ++ z.drop 32 :=
      decomp z 4 4 8 16
    have dw : w = w.take 4 ++ Ref.slice w 4 4 ++ Ref.slice w 8 8 ++ Ref.slice w 16 16 ++ w.drop 32 :=
      decomp w 4 4 8 16
    rw [dz, dw, eA, e4, eC, eP, eE]
  by_cases h3 : x.getD 1 0 = 3
  · have hl64 : x.length = 64 := by rw [hx.2.1, h3]; rfl
    have hnx : Ref.IsNodeFmt z := ⟨by omega, tag_toB x _ h3⟩
    have hny : Ref.IsNodeFmt w := ⟨by omega, tag_toB y _ (ht ▸ h3)⟩
    have hcx : ¬ Ref.IsChainFmt z := fun h => by have := h.1; omega
    have hcy : ¬ Ref.IsChainFmt w := fun h => by have := h.1; omega
    unfold Ref.fmtList at hL
    rw [if_neg hcx, if_neg hcy, if_pos hnx, if_pos hny] at hL
    unfold Ref.nodeBlock at hL
    obtain ⟨e1, eE⟩ := List.append_inj hL (by simp [Ref.slice]; omega)
    obtain ⟨e2, eD⟩ := List.append_inj e1 (by simp [Ref.slice]; omega)
    obtain ⟨e3, eC⟩ := List.append_inj e2 (by simp [Ref.slice]; omega)
    obtain ⟨eA, -⟩ := List.append_inj e3 (by simp; omega)
    obtain ⟨ax1, ax2, ax3⟩ := hx.2.2.2.1 h3
    obtain ⟨ay1, ay2, ay3⟩ := hy.2.2.2.1 (ht ▸ h3)
    simp only [posField, idxField] at ax1 ax2 ax3 ay1 ay2 ay3
    rw [← hz] at ax1 ax2 ax3; rw [← hw] at ay1 ay2 ay3
    have hH : Ref.nodeHeight z = Ref.nodeHeight w := by
      rw [nodeHeight_take z, nodeHeight_take w, eA]
    rw [hH] at eD ax2 ax3
    have eD' := congrArg Ref.leNat eD
    rw [Ref.leNat_le32, Ref.leNat_le32, Nat.mod_eq_of_lt (heapIndex_lt _ _ _ (nodeHeight_le _) ax3),
      Nat.mod_eq_of_lt (heapIndex_lt _ _ _ (nodeHeight_le _) ay3)] at eD'
    obtain ⟨ep, ej⟩ := heapIndex_inj _ _ _ _ _ ax2 ay2 ax3 ay3 eD'
    have e4 : Ref.slice z 4 4 = Ref.slice w 4 4 := by
      rw [← le32_leNat (Ref.slice z 4 4) (hlength_slice _ _ _ (by omega)),
        ← le32_leNat (Ref.slice w 4 4) (hlength_slice _ _ _ (by omega)), ep]
    have e12 : Ref.slice z 12 4 = Ref.slice w 12 4 := by
      rw [← le32_leNat (Ref.slice z 12 4) (hlength_slice _ _ _ (by omega)),
        ← le32_leNat (Ref.slice w 12 4) (hlength_slice _ _ _ (by omega)), ej]
    have dz : z = z.take 4 ++ Ref.slice z 4 4 ++ Ref.slice z 8 4 ++ Ref.slice z 12 4 ++ z.drop 16 :=
      decomp z 4 4 4 4
    have dw : w = w.take 4 ++ Ref.slice w 4 4 ++ Ref.slice w 8 4 ++ Ref.slice w 12 4 ++ w.drop 16 :=
      decomp w 4 4 4 4
    rw [dz, dw, eA, e4, eC, e12, eE]
  by_cases h12 : x.getD 1 0 = 12
  · have hl96 : x.length = 96 := by rw [hx.2.1, h12]; rfl
    have hdx : Ref.IsDigestFmt z := ⟨by omega, tag_toB x _ h12⟩
    have hdy : Ref.IsDigestFmt w := ⟨by omega, tag_toB y _ (ht ▸ h12)⟩
    have hcx : ¬ Ref.IsChainFmt z := fun h => by have := h.1; omega
    have hcy : ¬ Ref.IsChainFmt w := fun h => by have := h.1; omega
    have hnx : ¬ Ref.IsNodeFmt z := fun h => by have := h.1; omega
    have hny : ¬ Ref.IsNodeFmt w := fun h => by have := h.1; omega
    unfold Ref.fmtList at hL
    rw [if_neg hcx, if_neg hcy, if_neg hnx, if_neg hny, if_pos hdx, if_pos hdy] at hL
    unfold Ref.digestBlock at hL
    obtain ⟨e1, eE⟩ := List.append_inj hL (by simp [Ref.slice]; omega)
    obtain ⟨eA, eC⟩ := List.append_inj e1 (by simp; omega)
    obtain ⟨hPx, hRx⟩ := hx.2.2.2.2 h12
    obtain ⟨hPy, hRy⟩ := hy.2.2.2.2 (ht ▸ h12)
    have eP : Ref.slice z 16 16 = Ref.slice w 16 16 := by
      rw [slice_toB_zero x 16 hPx, slice_toB_zero y 16 hPy]
    have eR : Ref.slice z 48 16 = Ref.slice w 48 16 := by
      rw [slice_toB_zero x 48 hRx, slice_toB_zero y 48 hRy]
    have dz : z = z.take 16 ++ Ref.slice z 16 16 ++ Ref.slice z 32 16 ++ Ref.slice z 48 16 ++ z.drop 64 :=
      decomp z 16 16 16 16
    have dw : w = w.take 16 ++ Ref.slice w 16 16 ++ Ref.slice w 32 16 ++ Ref.slice w 48 16 ++ w.drop 64 :=
      decomp w 16 16 16 16
    rw [dz, dw, eA, eP, eC, eR, eE]
  · have hnot : ∀ (u : List UInt8), u.getD 1 0 = x.getD 1 0 →
        (toB u).getD 1 0 ∉ [Ref.byte 1, Ref.byte 3, Ref.byte 12] := by
      intro u hu hm
      rw [getD_toB, hu] at hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact h1 (UInt8.toBitVec_inj.mp hm)
      · exact h3 (UInt8.toBitVec_inj.mp hm)
      · exact h12 (UInt8.toBitVec_inj.mp hm)
    have hq : Ref.padTo64 z = Ref.padTo64 w := by
      have := congrArg qbytes hxy
      simp only [fmtQ, Ref.fmt_of_tag _ (hnot x rfl), Ref.fmt_of_tag _ (hnot y ht.symm),
        qbytes_pad64] at this
      exact this
    have := congrArg (fun l => l.take x.length) hq
    simp only [Ref.padTo64] at this
    rw [List.take_append_of_le_length (by simp [lx]), List.take_append_of_le_length (by simp [ly]; omega)] at this
    rw [List.take_of_length_le (by simp [lx]), hlen, List.take_of_length_le (by simp [ly])] at this
    exact this

/-! ## Honest inputs -/

theorem length_bytesLE (n : Nat) (v : BitVec (8 * n)) : (SphincsSecurity.bytesLE n v).length = n := by
  simp [SphincsSecurity.bytesLE]

theorem length_fieldBytes (f : SphincsSecurity.TweakFields) : (SphincsSecurity.fieldBytes f).length = 16 := by
  simp [SphincsSecurity.fieldBytes, length_bytesLE]

theorem getD1_fieldBytes (f : SphincsSecurity.TweakFields) (rest : List UInt8) :
    (SphincsSecurity.fieldBytes f ++ rest).getD 1 0 = UInt8.ofBitVec f.tag := by
  simp only [SphincsSecurity.fieldBytes, SphincsSecurity.bytesLE, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

theorem hslice_append_left (l₁ l₂ : List Byte) (a n : Nat) (h : a + n ≤ l₁.length) :
    Ref.slice (l₁ ++ l₂) a n = Ref.slice l₁ a n := by
  unfold Ref.slice
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem hslice_append_right (l₁ l₂ : List Byte) (a n : Nat) (h : l₁.length ≤ a) :
    Ref.slice (l₁ ++ l₂) a n = Ref.slice l₂ (a - l₁.length) n := by
  unfold Ref.slice
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem slice_self (l : List Byte) (n : Nat) (h : l.length = n) : Ref.slice l 0 n = l := by
  unfold Ref.slice; rw [List.drop_zero, List.take_of_length_le (by omega)]

theorem slice_tweak4 (t lay tau p j : Nat) (r : List Byte) :
    Ref.slice (Ref.tweak t lay tau p j ++ r) 4 4 = Ref.le32 p := by
  rw [hslice_append_left _ _ _ _ (by simp)]
  unfold Ref.tweak
  rw [hslice_append_left _ _ _ _ (by simp), hslice_append_left _ _ _ _ (by simp),
    hslice_append_right _ _ _ _ (by simp)]
  exact slice_self _ _ (Ref.length_le32 p)

theorem slice_tweak12 (t lay tau p j : Nat) (r : List Byte) :
    Ref.slice (Ref.tweak t lay tau p j ++ r) 12 4 = Ref.le32 j := by
  rw [hslice_append_left _ _ _ _ (by simp)]
  unfold Ref.tweak
  rw [hslice_append_right _ _ _ _ (by simp)]
  exact slice_self _ _ (Ref.length_le32 j)

theorem byte_eq_iff (a b : Nat) : Ref.byte a = Ref.byte b ↔ a % 256 = b % 256 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa [Ref.byte_toNat] using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa [Ref.byte_toNat] using h

theorem nodeHeight_tweak (t lay tau p j : Nat) (r : List Byte) :
    Ref.nodeHeight (Ref.tweak t lay tau p j ++ r) = Ref.height (lay % 256) := by
  unfold Ref.nodeHeight
  have h2 : (Ref.tweak t lay tau p j ++ r).getD 2 0 = Ref.byte lay := by simp [Ref.tweak]
  rw [h2, Ref.byte_toNat]

/-- A tweak input `tw(t, lay, tau, p, j) || P || payload` is honest, given the facts of its tag. -/
theorem honest_tw (t lay tau p j : Nat) (P : SphincsSecurity.PublicParameter) (payload : List UInt8)
    (hlen : 32 + payload.length = tagLen (t % 256))
    (h1 : t % 256 = 1 → P = 0 ∧ p % 2 ^ 32 < 2 ^ 27)
    (hn : t % 256 = 3 →
      1 ≤ p % 2 ^ 32 ∧ p % 2 ^ 32 ≤ Ref.height (lay % 256) ∧
        j % 2 ^ 32 < 2 ^ (Ref.height (lay % 256) - p % 2 ^ 32))
    (h12 : t % 256 = 12 → P = 0 ∧ (payload.drop 16).take 16 = List.replicate 16 0) :
    Honest (SphincsSecurity.fieldBytes (SphincsSecurity.tweakFields t lay tau p j) ++
      SphincsSecurity.bytesLE 16 P ++ payload) := by
  set x := SphincsSecurity.fieldBytes (SphincsSecurity.tweakFields t lay tau p j) ++
      SphincsSecurity.bytesLE 16 P ++ payload with hx
  have hg : (x.getD 1 0).toNat = t % 256 := by
    rw [hx, List.append_assoc, getD1_fieldBytes]
    show (BitVec.ofNat 8 t).toNat = t % 256
    simp
  have htag : ∀ c : UInt8, x.getD 1 0 = c → t % 256 = c.toNat := fun c h => hg ▸ congrArg UInt8.toNat h
  have hB : toB x = Ref.tweak t lay tau p j ++ (Ref.toList (n := 16) P ++ toB payload) := by
    simp only [hx, toB_append, toB_tweakFields, toB_bytesLE, List.append_assoc]
  have hpos : posField x = p % 2 ^ 32 := by
    unfold posField; rw [hB, slice_tweak4, Ref.leNat_le32]
  have hidx : idxField x = j % 2 ^ 32 := by
    unfold idxField; rw [hB, slice_tweak12, Ref.leNat_le32]
  have hnh : Ref.nodeHeight (toB x) = Ref.height (lay % 256) := by
    rw [hB, nodeHeight_tweak]
  have hd16 : x.drop 16 = SphincsSecurity.bytesLE 16 P ++ payload := by
    rw [hx, List.append_assoc, List.drop_left' (length_fieldBytes _)]
  have hPs : (x.drop 16).take 16 = SphincsSecurity.bytesLE 16 P := by
    rw [hd16, List.take_left' (length_bytesLE 16 _)]
  have hRs : (x.drop 48).take 16 = (payload.drop 16).take 16 := by
    rw [show 48 = 16 + 32 from rfl, ← List.drop_drop, hd16, show 32 = 16 + 16 from rfl, ← List.drop_drop,
      List.drop_left' (length_bytesLE 16 _)]
  have hP0 : P = 0 → SphincsSecurity.bytesLE 16 P = List.replicate 16 0 := by rintro rfl; rfl
  refine ⟨by simp [hx, SphincsSecurity.fieldBytes, SphincsSecurity.protocolDomainSep], ?_, ?_, ?_, ?_⟩
  · rw [hg, hx, List.length_append, List.length_append, length_fieldBytes, length_bytesLE]; omega
  · intro h
    obtain ⟨a, b⟩ := h1 (htag 1 h)
    exact ⟨hPs ▸ hP0 a, hpos ▸ b⟩
  · intro h
    obtain ⟨a, b, c⟩ := hn (htag 3 h)
    unfold NodeOk
    rw [hpos, hidx, hnh]
    exact ⟨a, b, c⟩
  · intro h
    obtain ⟨a, b⟩ := h12 (htag 12 h)
    exact ⟨hPs ▸ hP0 a, hRs ▸ b⟩

/-- An input whose tag has no special format is honest when its length is right. -/
theorem honest_plain (f : SphincsSecurity.TweakFields) (rest : List UInt8)
    (h : 16 + rest.length = tagLen f.tag.toNat)
    (ht : f.tag.toNat ≠ 1 ∧ f.tag.toNat ≠ 3 ∧ f.tag.toNat ≠ 12) :
    Honest (SphincsSecurity.fieldBytes f ++ rest) := by
  have hg : ((SphincsSecurity.fieldBytes f ++ rest).getD 1 0).toNat = f.tag.toNat := by
    rw [getD1_fieldBytes]; rfl
  have htag : ∀ c : UInt8, (SphincsSecurity.fieldBytes f ++ rest).getD 1 0 = c → f.tag.toNat = c.toNat :=
    fun c e => hg ▸ congrArg UInt8.toNat e
  refine ⟨by simp [SphincsSecurity.fieldBytes, SphincsSecurity.protocolDomainSep], ?_,
    fun e => absurd (htag 1 e) ht.1, fun e => absurd (htag 3 e) ht.2.1,
    fun e => absurd (htag 12 e) ht.2.2⟩
  rw [List.length_append, length_fieldBytes, h, hg]

theorem tweakableHashInput_eq (P : SphincsSecurity.PublicParameter) (dom : SphincsSecurity.HashDomain)
    (payload : List UInt8) :
    SphincsSecurity.tweakableHashInput P dom payload =
      SphincsSecurity.fieldBytes (SphincsSecurity.hashDomainFields dom) ++
        SphincsSecurity.bytesLE 16 P ++ payload := rfl

theorem layerHeight_eq (lay : Layer) : SphincsSecurity.layerHeight lay = Ref.height lay.val := by
  fin_cases lay <;> rfl

/-! ## Every abstract query is honest -/

/-- Every query of an abstract computation is honest. -/
abbrev HQ {α : Type} (oa : AComp α) : Prop :=
  AllQ (ι := List UInt8) (R := SphincsSecurity.HashOutput) Honest oa

theorem hq_pure {α : Type} (a : α) : HQ (pure a : AComp α) := allQ_pure Honest a

/- `AllQ` is a structural recursion on the computation; sealing it keeps elaboration from evaluating
the big concrete trees (`2^14` PORS leaves) inside `HQ` goals. -/
attribute [local irreducible] SigGolfCandidate.Bridge.AllQ

theorem hq_bind {α β : Type} {oa : AComp α} {ob : α → AComp β} (h : HQ oa) (h' : ∀ x, HQ (ob x)) :
    HQ (oa >>= ob) := allQ_bind Honest h h'

theorem hq_oracleHash (x : List UInt8) (h : Honest x) :
    HQ (SphincsSecurity.Concrete.oracleHash (m := AComp) x) :=
  (allQ_query (R := SphincsSecurity.HashOutput) Honest x).mpr h

theorem hq_th (P : SphincsSecurity.PublicParameter) (dom : SphincsSecurity.HashDomain)
    (payload : List UInt8) (h : Honest (SphincsSecurity.tweakableHashInput P dom payload)) :
    HQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) P dom payload) :=
  hq_bind (hq_oracleHash _ h) fun _ => hq_pure _

theorem hq_sequenceFin {α : Type} {n : Nat} (c : Fin n → AComp α) (h : ∀ j, HQ (c j)) :
    HQ (sequenceFin c) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    exact hq_bind (h 0) fun _ => hq_bind (ih _ fun j => h j.succ) fun _ => hq_pure _

macro "hq" : tactic => `(tactic| repeat (first
  | exact hq_pure _
  | refine hq_bind ?_ (fun _ => ?_)
  | refine hq_sequenceFin _ (fun _ => ?_)
  | split))

/-! ### Hash calls -/

section calls

open SphincsSecurity.Concrete

variable (P : SphincsSecurity.PublicParameter)

theorem length_flatMap16 (l : List Digest) :
    (l.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [List.flatMap_cons, length_bytesLE, ih]; ring

theorem hq_chainWalk (hP : P = 0) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (start steps : Nat) (v : Digest) : HQ (chainWalk (m := AComp) P lay tree leaf c start steps v) := by
  induction steps with
  | zero => exact hq_pure _
  | succ n ih =>
    refine hq_bind ih fun prev => ?_
    split
    · rename_i hstep
      refine hq_th _ _ _ ?_
      rw [tweakableHashInput_eq]
      refine honest_tw 1 lay.val tree.val (SphincsSecurity.chainLength * c.val + (start + n)) leaf.val P _
        (by simp [tagLen, length_bytesLE]) (fun _ => ⟨hP, ?_⟩) (fun h => absurd h (by decide))
        (fun h => absurd h (by decide))
      have e : SphincsSecurity.chainLength = 8 := rfl
      have hc := c.isLt
      unfold SphincsSecurity.numChains at hc
      rw [e] at hstep ⊢
      exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
    · exact hq_pure _

theorem hq_leafHash (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (ends : ChainIndex → Digest) :
    HQ (leafHash (m := AComp) P lay tree leaf ends) := by
  refine hq_th _ _ _ ?_
  rw [tweakableHashInput_eq]
  refine honest_tw 2 lay.val tree.val 0 leaf.val P _ ?_ (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
  rw [leafPayload, length_flatMap16, List.length_ofFn]
  simp [tagLen, SphincsSecurity.numChains]

theorem lay_lt256 (lay : Layer) : lay.val < 256 := by
  have := lay.isLt; unfold SphincsSecurity.numLayers at this; omega

/-- A hypertree node query is honest when it names a node of its layer's tree. -/
theorem hq_node (lay : Layer) (tree : TreeIndex) (lam j : Nat) (l r : Digest) (h1 : 1 ≤ lam)
    (h2 : lam ≤ SphincsSecurity.layerHeight lay) (h3 : j < 2 ^ (SphincsSecurity.layerHeight lay - lam)) :
    HQ (tweakableHash (m := AComp) P (.node lay tree lam j) (nodePayload l r)) := by
  refine hq_th _ _ _ ?_
  rw [tweakableHashInput_eq]
  have hh := layerHeight_eq lay
  have hl11 : SphincsSecurity.layerHeight lay ≤ 11 := hh ▸ height_le _
  have hj : j < 2 ^ 32 := lt_of_lt_of_le h3 (Nat.pow_le_pow_right (by omega) (by omega))
  refine honest_tw 3 lay.val tree.val lam j P _ (by simp [tagLen, nodePayload, length_bytesLE])
    (fun h => absurd h (by decide)) (fun _ => ?_) (fun h => absurd h (by decide))
  rw [Nat.mod_eq_of_lt (lay_lt256 lay), Nat.mod_eq_of_lt (show lam < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt hj, ← hh]
  exact ⟨h1, h2, h3⟩

/-- A PORS node query (tag 10, any heap index, any 32-byte payload) is honest. -/
theorem hq_ftsNodeAny (index : Index) (tree : FtsTree) (heap : Nat) (payload : List UInt8)
    (hl : payload.length = 32) :
    HQ (tweakableHash (m := AComp) P (.ftsNode index tree heap) payload) := by
  refine hq_th _ _ _ ?_
  rw [tweakableHashInput_eq]
  exact honest_tw 10 tree.val index.val 0 heap P _ (by simp [tagLen, hl])
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

theorem hq_ftsNode (index : Index) (tree : FtsTree) (heap : Nat) (l r : Digest) :
    HQ (tweakableHash (m := AComp) P (.ftsNode index tree heap) (nodePayload l r)) :=
  hq_ftsNodeAny P index tree heap _ (by simp [nodePayload, length_bytesLE])

theorem hq_encode (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (c : SphincsSecurity.Counter) : HQ (encode (m := AComp) P lay tree leaf M c) := by
  refine hq_bind (hq_th _ _ _ ?_) fun _ => hq_pure _
  rw [tweakableHashInput_eq]
  exact honest_tw 4 lay.val tree.val 0 leaf.val P _ (by simp [tagLen, length_bytesLE])
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

theorem hq_ftsLeafHash (index : Index) (tree : FtsTree) (leaf : Nat) (s : Digest) :
    HQ (ftsLeafHash (m := AComp) P index tree leaf s) := by
  refine hq_th _ _ _ ?_
  rw [tweakableHashInput_eq]
  exact honest_tw 9 tree.val index.val 0 leaf P _ (by simp [tagLen, length_bytesLE])
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

/-- The message digest query is honest (zero parameter; the root slot is zero). -/
theorem hq_messageDigest (hP : P = 0) (root : Digest) (m : Message) (rho : Digest) :
    HQ (messageDigest (m := AComp) P root m rho) := by
  refine hq_bind (hq_oracleHash _ ?_) fun _ => hq_pure _
  rw [tweakableHashInput_eq]
  refine honest_tw 12 0 0 0 0 P _ (by simp [tagLen, messageDigestPayload, length_bytesLE])
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ⟨hP, ?_⟩)
  unfold messageDigestPayload
  rw [List.append_assoc, List.drop_left' (length_bytesLE 16 _), List.take_left' (length_bytesLE 16 _)]
  rfl

theorem honest_keygenInput (dom : SphincsSecurity.KeygenDomain) (seed : MasterSeed) :
    Honest (SphincsSecurity.keygenHashInput P dom seed) := by
  unfold SphincsSecurity.keygenHashInput
  rw [List.append_assoc]
  apply honest_plain <;> cases dom <;> simp [SphincsSecurity.keygenDomainFields,
    SphincsSecurity.tweakFields, tagLen, length_bytesLE]

theorem hq_deriveKey (dom : SphincsSecurity.KeygenDomain) (seed : MasterSeed) :
    HQ (SphincsSecurity.deriveKey (m := AComp) P dom seed) :=
  hq_bind (hq_oracleHash _ (honest_keygenInput P dom seed)) fun _ => hq_pure _

theorem hq_otsSecret (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (pair : SphincsSecurity.ChainPair) :
    HQ (SphincsSecurity.Seeded.otsSecret (m := AComp) P seed lay tree leaf pair) :=
  hq_bind (hq_oracleHash _ (honest_keygenInput P _ seed)) fun _ => hq_pure _

theorem hq_ftsSecret (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pair : SphincsSecurity.FtsPair) :
    HQ (SphincsSecurity.Seeded.ftsSecret (m := AComp) P seed index tree pair) :=
  hq_bind (hq_oracleHash _ (honest_keygenInput P _ seed)) fun _ => hq_pure _

theorem hq_deriveRandomizer (seed : MasterSeed) (m : Message) (trial : BitVec 32) :
    HQ (SphincsSecurity.deriveRandomizer (m := AComp) P seed m trial) := by
  refine hq_bind (hq_oracleHash _ ?_) fun _ => hq_pure _
  simp [Honest, SphincsSecurity.randomizerHashInput, tagLen, length_bytesLE]

theorem hq_deriveRandomizerPair (seed : MasterSeed) (m : Message) (trial : BitVec 32) :
    HQ (SphincsSecurity.Seeded.deriveRandomizerPair (m := AComp) P seed m trial) := by
  refine hq_bind (hq_oracleHash _ ?_) fun _ => hq_pure _
  simp [Honest, SphincsSecurity.randomizerHashInput, tagLen, length_bytesLE]

end calls

macro "hqs" : tactic => `(tactic| repeat (first
  | exact hq_pure _
  | apply hq_chainWalk | apply hq_leafHash | apply hq_node | apply hq_ftsNode | apply hq_encode
  | apply hq_ftsLeafHash | apply hq_messageDigest | apply hq_deriveKey
  | apply hq_deriveRandomizer
  | refine hq_bind ?_ (fun _ => ?_)
  | refine hq_sequenceFin _ (fun _ => ?_)
  | split))

section algs

open SphincsSecurity.Concrete

variable (P : SphincsSecurity.PublicParameter)

/-! ### Verification -/

theorem hq_otsLeaf (hP : P = 0) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (c : SphincsSecurity.Counter) (values : ChainIndex → Digest) :
    HQ (otsLeaf (m := AComp) P lay tree leaf M c values) := by
  unfold otsLeaf
  refine hq_bind (hq_encode _ _ _ _ _ _) fun r => ?_
  split
  · exact hq_bind (hq_sequenceFin _ fun c => hq_chainWalk _ hP _ _ _ _ _ _ _) fun _ =>
      hq_bind (hq_leafHash _ _ _ _ _) fun _ => hq_pure _
  · exact hq_pure _

theorem div_pow_lt (e h n : Nat) (he : e < 2 ^ h) (hn : n ≤ h) : e / 2 ^ n < 2 ^ (h - n) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hn]; exact he

theorem hq_treeFold (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (hleaf : leaf.val < 2 ^ SphincsSecurity.layerHeight lay)
    (n : Nat) (hn : n ≤ SphincsSecurity.layerHeight lay) (v : Digest) :
    HQ (treeFold (m := AComp) P lay tree leaf path n v) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    refine hq_bind (ih (by omega)) fun _ => ?_
    dsimp only
    split <;> exact hq_node _ _ _ _ _ _ _ (by omega) hn (div_pow_lt _ _ _ hleaf hn)

theorem length_foldPayload (right : Bool) (a b : Digest) : (foldPayload right a b).length = 32 := by
  unfold foldPayload; split <;> simp [nodePayload, length_bytesLE]

theorem hq_foldSegment (index : Index) (segment : SphincsSecurity.Segment) (remaining position : Nat)
    (current : Digest) (heap : Nat) :
    HQ (foldSegment (m := AComp) P index segment remaining position current heap) := by
  induction remaining generalizing position current heap with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold foldSegment
    exact hq_bind (hq_ftsNodeAny _ _ _ _ _ (length_foldPayload _ _ _)) fun _ => ih _ _ _

theorem hq_recoverSegments (index : Index) (segments : Fin SphincsSecurity.ftsSegments → SphincsSecurity.Segment)
    (fuel : Nat) (pending : PendingHash) (state : RecoverState) :
    HQ (recoverSegments (m := AComp) P index segments fuel pending state) := by
  induction fuel generalizing pending state with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold recoverSegments
    split
    swap
    · exact hq_pure _
    dsimp only
    split
    · exact hq_pure _
    split
    · exact hq_pure _
    cases pending with
    | leaf v s =>
      refine hq_bind (hq_ftsLeafHash _ _ _ _ _) fun start => ?_
      refine hq_bind (hq_foldSegment _ _ _ _ _ _ _) fun r => ?_
      split
      · split
        · exact hq_pure _
        · split
          · exact ih _ _
          · exact hq_pure _
      · exact hq_pure _
    | merge H l =>
      refine hq_bind (hq_ftsNode _ _ _ _ _ _) fun start => ?_
      refine hq_bind (hq_foldSegment _ _ _ _ _ _ _) fun r => ?_
      split
      · split
        · exact hq_pure _
        · split
          · exact ih _ _
          · exact hq_pure _
      · exact hq_pure _

theorem hq_recoverLeaves (index : Index) (values : SphincsSecurity.SlotCode → Nat)
    (fts : SphincsSecurity.FtsSignature) (remaining position previous : Nat) (state : RecoverState) :
    HQ (recoverLeaves (m := AComp) P index values fts remaining position previous state) := by
  induction remaining generalizing position previous state with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold recoverLeaves
    repeat (first
      | exact hq_pure _
      | exact ih _ _ _
      | refine hq_bind (hq_recoverSegments _ _ _ _ _ _) (fun _ => ?_)
      | split
      | dsimp only)

theorem hq_ftsRecover (index : Index) (values : SphincsSecurity.SlotCode → Nat)
    (fts : SphincsSecurity.FtsSignature) :
    HQ (ftsRecover (m := AComp) P index values fts) := by
  unfold ftsRecover
  refine hq_bind (hq_recoverLeaves _ _ _ _ _ _ _ _) fun r => ?_
  repeat (first | exact hq_pure _ | split | dsimp only)

theorem hq_verifyLayers (hP : P = 0) (index : Index) (σ : Signature) (n : Nat) (M : Digest) :
    HQ (verifyLayers (m := AComp) P index σ n M) := by
  induction n generalizing M with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold verifyLayers
    split
    · refine hq_bind (hq_otsLeaf _ hP _ _ _ _ _ _) fun r => ?_
      split
      · exact hq_bind (hq_treeFold _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) _ le_rfl _)
          fun _ => ih _
      · exact hq_pure _
    · exact hq_pure _

/-- **verify** makes only honest queries. -/
theorem hq_verify (pk : SphincsSecurity.PublicKey) (hP : pk.parameter = 0) (m : Message)
    (σ : Signature) :
    HQ (verify (m := AComp) pk m σ) := by
  unfold verify verifyCore
  split
  · refine hq_bind (hq_messageDigest _ hP _ _ _) fun d => ?_
    refine hq_bind (hq_ftsRecover _ _ _ _) fun r => ?_
    split
    · refine hq_bind (hq_verifyLayers _ hP _ _ _ _) fun r => ?_
      split <;> exact hq_pure _
    · exact hq_pure _
  · exact hq_pure _

/-! ### Tree building and signing -/

theorem hq_buildLevel (hashNode : Nat → Digest → Digest → AComp Digest) (width : Nat)
    (h : ∀ j l r, j < width → HQ (hashNode j l r)) (below : Nat → Digest) :
    HQ (buildLevel hashNode width below) :=
  hq_bind (hq_sequenceFin _ fun j => h _ _ _ j.isLt) fun _ => hq_pure _

theorem hq_buildLevels (hashNode : Nat → Nat → Digest → Digest → AComp Digest) (height : Nat)
    (h : ∀ lam j l r, 1 ≤ lam → lam ≤ height → j < 2 ^ (height - lam) → HQ (hashNode lam j l r))
    (leaves : Nat → Digest) (n : Nat) (hn : n ≤ height) :
    HQ (buildLevels hashNode height leaves n) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    exact hq_bind (ih (by omega)) fun _ => hq_bind (hq_buildLevel _ _
      (fun j l r hj => h _ j l r (by omega) hn hj) _) fun _ => hq_pure _

/-- The node hash of a layer tree is honest on the tree's nodes. -/
theorem hq_layerNode (lay : Layer) (tree : TreeIndex) :
    ∀ lam j l r, 1 ≤ lam → lam ≤ SphincsSecurity.layerHeight lay →
      j < 2 ^ (SphincsSecurity.layerHeight lay - lam) →
      HQ (tweakableHash (m := AComp) P (.node lay tree lam j) (nodePayload l r)) :=
  fun _ _ _ _ h1 h2 h3 => hq_node _ _ _ _ _ _ _ h1 h2 h3

theorem hq_ftsTreeNode (index : Index) :
    ∀ lam j l r, 1 ≤ lam → lam ≤ SphincsSecurity.ftsTreeHeight →
      j < 2 ^ (SphincsSecurity.ftsTreeHeight - lam) →
      HQ (tweakableHash (m := AComp) P (.ftsNode index porsTree (ftsHeapIndex lam j)) (nodePayload l r)) :=
  fun _ _ _ _ _ _ _ => hq_ftsNode _ _ _ _ _ _

theorem hq_buildChain (hP : P = 0) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (secret : AComp Digest) (hs : HQ secret) (d : Nat) :
    HQ (buildChain P lay tree leaf c secret d) :=
  hq_bind hs fun _ => hq_bind (hq_chainWalk _ hP _ _ _ _ _ _ _) fun _ =>
    hq_bind (hq_chainWalk _ hP _ _ _ _ _ _ _) fun _ => hq_pure _

theorem hq_buildLeaf (hP : P = 0) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → AComp Digest) (hs : ∀ c, HQ (secret c)) (digits : Encoding) :
    HQ (buildLeaf P lay tree leaf secret digits) :=
  hq_bind (hq_sequenceFin _ fun c => hq_buildChain _ hP _ _ _ _ _ (hs c) _) fun _ =>
    hq_bind (hq_leafHash _ _ _ _ _) fun _ => hq_pure _

theorem hq_buildLayerTree (hP : P = 0) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → AComp Digest) (hs : ∀ e c, HQ (secret e c))
    (leaf : LeafIndex) (digits : Encoding) :
    HQ (buildLayerTree P lay tree secret leaf digits) :=
  hq_bind (hq_sequenceFin _ fun _ => hq_buildLeaf _ hP _ _ _ _ (hs _) _) fun _ =>
    hq_bind (hq_buildLevels _ _ (hq_layerNode _ _ _) _ _ le_rfl) fun _ => hq_pure _

theorem hq_buildLayerTable (hP : P = 0) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → AComp Digest) (hs : ∀ e c, HQ (secret e c))
    (leaf : LeafIndex) (digits : Encoding) :
    HQ (buildLayerTable P lay tree secret leaf digits) :=
  hq_bind (hq_sequenceFin _ fun _ => hq_buildLeaf _ hP _ _ _ _ (hs _) _) fun _ =>
    hq_bind (hq_buildLevels _ _ (hq_layerNode _ _ _) _ _ le_rfl) fun _ => hq_pure _

theorem hq_buildFtsTree (index : Index) (secret : FtsLeaf → AComp Digest)
    (hs : ∀ j, HQ (secret j)) :
    HQ (buildFtsTree P index secret) :=
  hq_bind (hq_sequenceFin _ fun j => hq_bind (hs j) fun _ =>
      hq_bind (hq_ftsLeafHash _ _ _ _ _) fun _ => hq_pure _) fun _ =>
    hq_bind (hq_buildLevels _ _ (hq_ftsTreeNode _ _) _ _ le_rfl) fun _ => hq_pure _

theorem hq_encodingSearch (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (attempts counter : Nat) : HQ (encodingSearch (m := AComp) P lay tree leaf M attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold encodingSearch
    refine hq_bind (hq_encode _ _ _ _ _ _) fun r => ?_
    split
    · exact hq_pure _
    · exact ih _

theorem hq_signTopLayer (hP : P = 0) (index : Index) (secret : LeafIndex → ChainIndex → AComp Digest)
    (hs : ∀ e c, HQ (secret e c)) (topNode : Nat → Nat → AComp Digest) (ht : ∀ l j, HQ (topNode l j))
    (M : Digest) : HQ (signTopLayer P index secret topNode M) := by
  unfold signTopLayer
  refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
  split
  · exact hq_bind (hq_sequenceFin _ fun c => hq_bind (hs _ _) fun _ => hq_chainWalk _ hP _ _ _ _ _ _ _)
      fun _ => hq_bind (hq_sequenceFin _ fun _ => ht _ _) fun _ => hq_pure _
  · exact hq_pure _

theorem hq_signLayers (hP : P = 0) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → AComp Digest)
    (hs : ∀ a b c d, HQ (secret a b c d)) (topNode : Nat → Nat → AComp Digest)
    (ht : ∀ l j, HQ (topNode l j)) (n : Nat) (M : Digest) :
    HQ (signLayers P index secret topNode n M) := by
  induction n generalizing M with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold signLayers
    split
    · split
      · refine hq_bind (hq_signTopLayer _ hP _ _ (hs _ _) _ ht _) fun r => ?_
        split <;> exact hq_pure _
      · refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
        split
        · refine hq_bind (hq_buildLayerTree _ hP _ _ _ (hs _ _) _ _) fun _ => hq_bind (ih _) fun r' => ?_
          split <;> exact hq_pure _
        · exact hq_pure _
    · exact hq_pure _

theorem hq_signFrom (hP : P = 0) (index : Index) (ftsSecret : FtsTree → FtsLeaf → AComp Digest)
    (hf : ∀ t j, HQ (ftsSecret t j))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → AComp Digest)
    (ho : ∀ a b c d, HQ (otsSecret a b c d)) (topNode : Nat → Nat → AComp Digest)
    (ht : ∀ l j, HQ (topNode l j)) (randomness : Digest) (leaves : IndexGroup → FtsLeaf) :
    HQ (signFrom P index ftsSecret otsSecret topNode randomness leaves) := by
  unfold signFrom
  refine hq_bind (hq_buildFtsTree _ _ _ (hf _)) fun _ =>
    hq_bind (hq_signLayers _ hP _ _ ho _ ht _ _) fun r => ?_
  split <;> exact hq_pure _

/-! ### Paired builders -/

theorem hq_buildLeafPaired (hP : P = 0) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : SphincsSecurity.ChainPair → AComp (Digest × Digest)) (hs : ∀ c, HQ (secret c))
    (digits : Encoding) : HQ (buildLeafPaired P lay tree leaf secret digits) :=
  hq_bind (hq_sequenceFin _ fun c => hq_bind (hs c) fun _ =>
      hq_bind (hq_buildChain _ hP _ _ _ _ _ (hq_pure _) _) fun _ =>
        hq_bind (hq_buildChain _ hP _ _ _ _ _ (hq_pure _) _) fun _ => hq_pure _) fun _ =>
    hq_bind (hq_leafHash _ _ _ _ _) fun _ => hq_pure _

theorem hq_buildLayerTablePaired (hP : P = 0) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → SphincsSecurity.ChainPair → AComp (Digest × Digest))
    (hs : ∀ e c, HQ (secret e c)) (leaf : LeafIndex) (digits : Encoding) :
    HQ (buildLayerTablePaired P lay tree secret leaf digits) :=
  hq_bind (hq_sequenceFin _ fun _ => hq_buildLeafPaired _ hP _ _ _ _ (hs _) _) fun _ =>
    hq_bind (hq_buildLevels _ _ (hq_layerNode _ _ _) _ _ le_rfl) fun _ => hq_pure _

theorem hq_buildLayerTreePaired (hP : P = 0) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → SphincsSecurity.ChainPair → AComp (Digest × Digest))
    (hs : ∀ e c, HQ (secret e c)) (leaf : LeafIndex) (digits : Encoding) :
    HQ (buildLayerTreePaired P lay tree secret leaf digits) :=
  hq_bind (hq_buildLayerTablePaired _ hP _ _ _ hs _ _) fun _ => hq_pure _

theorem hq_buildFtsTreePaired (index : Index)
    (secret : SphincsSecurity.FtsPair → AComp (Digest × Digest)) (hs : ∀ j, HQ (secret j)) :
    HQ (buildFtsTreePaired P index secret) :=
  hq_bind (hq_sequenceFin _ fun j => hq_bind (hs j) fun _ =>
      hq_bind (hq_ftsLeafHash _ _ _ _ _) fun _ =>
        hq_bind (hq_ftsLeafHash _ _ _ _ _) fun _ => hq_pure _) fun _ =>
    hq_bind (hq_buildLevels _ _ (hq_ftsTreeNode _ _) _ _ le_rfl) fun _ => hq_pure _

theorem hq_signTopLayerPaired (hP : P = 0) (index : Index)
    (secret : LeafIndex → SphincsSecurity.ChainPair → AComp (Digest × Digest))
    (hs : ∀ e c, HQ (secret e c)) (topNode : Nat → Nat → AComp Digest) (ht : ∀ l j, HQ (topNode l j))
    (M : Digest) : HQ (signTopLayerPaired P index secret topNode M) := by
  unfold signTopLayerPaired
  refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
  split
  · exact hq_bind (hq_sequenceFin _ fun c => hq_bind (hs _ _) fun _ =>
      hq_bind (hq_chainWalk _ hP _ _ _ _ _ _ _) fun _ =>
        hq_bind (hq_chainWalk _ hP _ _ _ _ _ _ _) fun _ => hq_pure _)
      fun _ => hq_bind (hq_sequenceFin _ fun _ => ht _ _) fun _ => hq_pure _
  · exact hq_pure _

theorem hq_signLayersPaired (hP : P = 0) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → SphincsSecurity.ChainPair → AComp (Digest × Digest))
    (hs : ∀ a b c d, HQ (secret a b c d)) (topNode : Nat → Nat → AComp Digest)
    (ht : ∀ l j, HQ (topNode l j)) (n : Nat) (M : Digest) :
    HQ (signLayersPaired P index secret topNode n M) := by
  induction n generalizing M with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold signLayersPaired
    split
    · split
      · refine hq_bind (hq_signTopLayerPaired _ hP _ _ (hs _ _) _ ht _) fun r => ?_
        split <;> exact hq_pure _
      · refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
        split
        · refine hq_bind (hq_buildLayerTreePaired _ hP _ _ _ (hs _ _) _ _) fun _ =>
            hq_bind (ih _) fun r' => ?_
          split <;> exact hq_pure _
        · exact hq_pure _
    · exact hq_pure _

theorem hq_signFromPaired (hP : P = 0) (index : Index)
    (ftsSecret : FtsTree → SphincsSecurity.FtsPair → AComp (Digest × Digest))
    (hf : ∀ t j, HQ (ftsSecret t j))
    (otsSecret : Layer → TreeIndex → LeafIndex → SphincsSecurity.ChainPair → AComp (Digest × Digest))
    (ho : ∀ a b c d, HQ (otsSecret a b c d)) (topNode : Nat → Nat → AComp Digest)
    (ht : ∀ l j, HQ (topNode l j)) (randomness : Digest) (leaves : IndexGroup → FtsLeaf) :
    HQ (signFromPaired P index ftsSecret otsSecret topNode randomness leaves) := by
  unfold signFromPaired
  refine hq_bind (hq_buildFtsTreePaired _ _ _ (hf _)) fun _ =>
    hq_bind (hq_signLayersPaired _ hP _ _ ho _ ht _ _) fun r => ?_
  split <;> exact hq_pure _

end algs

theorem hq_mac (P : SphincsSecurity.PublicParameter) (seed : MasterSeed)
    (region : SphincsSecurity.TopRegion) :
    HQ (SphincsSecurity.Concrete.oracleHash (m := AComp) (SphincsSecurity.macHashInput P seed region)) := by
  apply hq_oracleHash
  unfold SphincsSecurity.macHashInput
  rw [List.append_assoc, List.append_assoc]
  apply honest_plain
  · have hr : (SphincsSecurity.regionBytes region).length = 65504 := by
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
    simp [tagLen, length_bytesLE, hr]
  · simp

theorem hq_maskSecret (P : SphincsSecurity.PublicParameter) (seed : MasterSeed) (l j : Nat) :
    HQ (SphincsSecurity.Seeded.maskSecret (m := AComp) P seed l j) := hq_deriveKey _ _ _

/-- **sign** makes only honest queries, for every cache. -/
theorem hq_sign (sk : SphincsSecurity.Seeded.SecretKey) (hP : sk.parameter = 0)
    (cache : SphincsSecurity.TopCache) (m : Message) :
    HQ (SphincsSecurity.Seeded.sign (m := AComp) sk cache m) := by
  unfold SphincsSecurity.Seeded.sign SphincsSecurity.Seeded.signChecked
  refine hq_bind (hq_mac _ _ _) fun tag => ?_
  split
  · refine hq_bind ?_ fun r => ?_
    · generalize SphincsSecurity.digestPairLimit = n
      generalize (0 : Nat) = a
      induction n generalizing a with
      | zero => exact hq_pure _
      | succ n ih =>
        unfold SphincsSecurity.Seeded.signDigestPairs SphincsSecurity.Seeded.signAttempt
        refine hq_bind (hq_deriveRandomizerPair _ _ _ _) fun _ => ?_
        refine hq_bind (hq_bind (hq_messageDigest _ hP _ _ _) fun _ => by split <;> exact hq_pure _)
          fun r => ?_
        split
        · exact hq_pure _
        · refine hq_bind (hq_bind (hq_messageDigest _ hP _ _ _) fun _ => by split <;> exact hq_pure _)
            fun r => ?_
          split
          · exact hq_pure _
          · exact ih _
    · split
      · exact hq_signFromPaired _ hP _ _ (fun _ _ => hq_ftsSecret _ _ _ _ _) _
          (fun _ _ _ _ => hq_otsSecret _ _ _ _ _ _)
          _ (fun _ _ => hq_bind (hq_maskSecret _ _ _ _) fun _ => hq_pure _) _ _
      · exact hq_pure _
  · exact hq_pure _

theorem hq_aLayers (index : Index) (S0 : Signature) (n : Nat) (M : Digest) :
    HQ (aLayers index S0 n M) := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n ih =>
  match n with
  | 0 => exact hq_pure _
  | 1 =>
    unfold aLayers
    exact hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => by split <;> exact hq_pure _
  | k + 2 =>
    unfold aLayers
    split
    · refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
      split
      · exact hq_pure _
      · exact hq_bind (hq_sequenceFin _ fun c => hq_chainWalk _ rfl _ _ _ _ _ _ _) fun _ =>
          hq_bind (hq_leafHash _ _ _ _ _) fun _ =>
          hq_bind (hq_treeFold _ _ _ _ _ (by simp only [SphincsSecurity.Concrete.leafIndexAt]; exact Nat.mod_lt _ (Nat.two_pow_pos _)) _ le_rfl _) fun _ =>
          hq_bind (ih (k + 1) (by omega) _) fun r => by split <;> exact hq_pure _
    · exact hq_pure _

/-- **expand** (abstract) makes only honest queries: the digest, the PORS stack machine, and per
layer the counter search, chains, leaf and fold, all with parameter `0`. -/
theorem hq_aExpand (m : Message) (pk : SphincsSecurity.PublicKey) (σ : Bytes 6032) :
    HQ (aExpand m pk σ) := by
  unfold aExpand
  refine hq_bind (hq_messageDigest _ rfl _ _ _) fun d => ?_
  split
  · exact hq_pure _
  · refine hq_bind (hq_ftsRecover _ _ _ _) fun r => ?_
    split
    · exact hq_pure _
    · exact hq_bind (hq_aLayers _ _ _ _) fun r => by split <;> exact hq_pure _

/-- **keygen** makes only honest queries. -/
theorem hq_keygen (seed : MasterSeed) : HQ (SphincsSecurity.Seeded.keygenFromSeed seed) := by
  unfold SphincsSecurity.Seeded.keygenFromSeed SphincsSecurity.Seeded.maskRegion
  refine hq_bind (hq_buildLayerTablePaired _ rfl _ _ _ (fun _ _ => hq_otsSecret _ _ _ _ _ _) _ _)
    fun _ => ?_
  refine hq_bind (hq_bind (hq_sequenceFin _ fun _ => hq_bind (hq_sequenceFin _ fun _ =>
    hq_bind (hq_maskSecret _ _ _ _) fun _ => hq_pure _) fun _ => hq_pure _) fun _ => hq_pure _) fun _ => ?_
  exact hq_bind (hq_mac _ _ _) fun _ => hq_pure _


/-! ## W1a padded chain inputs

The padded verifier (`SphincsSecurity.Concrete.verifyP`) also hashes 80-byte chain inputs
`tw ‖ P ‖ pad ‖ v` with a nonzero pad. `Ref.fmt` maps them to the one-block W1a chain block
`tw' ‖ pad ‖ v` (`Ref.padChainBlock`); it is injective on `HonestP = Honest ∨ PadHonest`
(`fmtQ_injOn_honestP`), the formal "common tweak offset" condition of W1a. -/

/-- A padded chain input the W1a verifier may issue: 80 bytes, tag `1`, zero parameter slot, position
below `2^27`, and a **nonzero** pad (bytes `32 .. 64`). A zero pad is the record's 48-byte input. -/
def PadHonest (x : List UInt8) : Prop :=
  x.head? = some 1 ∧ x.length = 80 ∧ x.getD 1 0 = 1 ∧
    (x.drop 16).take 16 = List.replicate 16 0 ∧ posField x < 2 ^ 27 ∧
    (x.drop 32).take 32 ≠ List.replicate 32 0

/-- The honest inputs of the padded game: the record's, and the padded chain inputs. -/
def HonestP (x : List UInt8) : Prop := Honest x ∨ PadHonest x

theorem honestP_head (x : List UInt8) (h : HonestP x) : x.head? = some 1 :=
  h.elim (fun h => h.1) (fun h => h.1)

theorem honestP_of_honest {x : List UInt8} (h : Honest x) : HonestP x := Or.inl h

theorem tag_of_toB {x : List UInt8} (h : (toB x).getD 1 0 = Ref.byte 1) : x.getD 1 0 = 1 := by
  rw [getD_toB] at h
  exact UInt8.toBitVec_inj.mp h

/-- The record's honest inputs never take the padded branch (tag 1 means 48 bytes). -/
theorem not_isPadChainFmt_of_honest {x : List UInt8} (h : Honest x) : ¬ Ref.IsPadChainFmt (toB x) := by
  rintro ⟨hl, ht⟩
  have hl' : x.length = 80 := by rwa [length_toB] at hl
  have h1 := tag_of_toB ht
  have := h.2.1
  rw [h1, hl'] at this
  exact absurd this (by decide)

theorem isPadChainFmt_of_padHonest {x : List UInt8} (h : PadHonest x) : Ref.IsPadChainFmt (toB x) :=
  ⟨by rw [length_toB]; exact h.2.1, tag_toB x 1 h.2.2.1⟩

theorem fmtQ_of_padHonest {x : List UInt8} (h : PadHonest x) :
    fmtQ x = ⟨0, Ref.ofList _ (Ref.padChainBlock (toB x))⟩ :=
  Ref.fmt_of_padChain _ (isPadChainFmt_of_padHonest h)

set_option exponentiation.threshold 600 in
theorem bytes_fmtQ_of_padHonest {x : List UInt8} (h : PadHonest x) :
    Ref.toList (fmtQ x).2 = Ref.padChainBlock (toB x) := by
  rw [fmtQ_of_padHonest h]
  exact Ref.toList_ofList _ _ (Ref.length_padChainBlock _ (by rw [length_toB]; exact h.2.1))

/-- The pad slot, as organizer bytes, is nonzero. -/
theorem slice32_ne_zeros {x : List UInt8} (h : PadHonest x) : Ref.slice (toB x) 32 32 ≠ Ref.zeros 32 := by
  intro heq
  apply h.2.2.2.2.2
  have hlen : ((x.drop 32).take 32).length = 32 := by simp [h.2.1]
  apply List.ext_getElem (by rw [hlen, List.length_replicate])
  intro i hi _
  have hi' : i < 32 := by rwa [hlen] at hi
  have e := congrArg (fun l : List Byte => l[i]?) heq
  simp only [Ref.slice, toB, ← List.map_drop, ← List.map_take, List.getElem?_map, Ref.zeros,
    List.getElem?_replicate, hi', if_true] at e
  rw [List.getElem_replicate]
  have hget : ((x.drop 32).take 32)[i]? = some ((x.drop 32).take 32)[i] := List.getElem?_eq_getElem hi
  rw [hget] at e
  simp only [Option.map_some, Option.some.injEq] at e
  exact UInt8.toBitVec_inj.mp e

theorem decomp5 (z : List Byte) :
    z = z.take 4 ++ Ref.slice z 4 4 ++ Ref.slice z 8 8 ++ Ref.slice z 16 16 ++ Ref.slice z 32 32 ++ z.drop 64 := by
  have h1 := decomp z 4 4 8 16
  have h2 : z.drop 32 = Ref.slice z 32 32 ++ z.drop 64 := by
    unfold Ref.slice
    rw [show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, List.take_append_drop]
  conv_lhs => rw [h1, h2]
  simp only [List.append_assoc]


/-- Two padded inputs with the same block are equal. -/
theorem padHonest_inj {x y : List UInt8} (hx : PadHonest x) (hy : PadHonest y) (hxy : fmtQ x = fmtQ y) :
    x = y := by
  have hL : Ref.padChainBlock (toB x) = Ref.padChainBlock (toB y) := by
    rw [← bytes_fmtQ_of_padHonest hx, ← bytes_fmtQ_of_padHonest hy, hxy]
  have lx : (toB x).length = 80 := by rw [length_toB]; exact hx.2.1
  have ly : (toB y).length = 80 := by rw [length_toB]; exact hy.2.1
  apply toB_injective
  set z := toB x with hz
  set w := toB y with hw
  unfold Ref.padChainBlock at hL
  obtain ⟨e1, eE⟩ := List.append_inj hL (by simp [Ref.slice]; omega)
  obtain ⟨e2, eD⟩ := List.append_inj e1 (by simp [Ref.slice]; omega)
  obtain ⟨e3, eC⟩ := List.append_inj e2 (by simp [Ref.slice]; omega)
  obtain ⟨eA, eB⟩ := List.append_inj e3 (by simp; omega)
  have hpx := hx.2.2.2.2.1
  have hpy := hy.2.2.2.2.1
  have eB' := congrArg Ref.leNat eB
  rw [Ref.leNat_le32, Ref.leNat_le32] at eB'
  unfold posField at hpx hpy
  rw [← hz] at hpx; rw [← hw] at hpy
  have bx : Ref.splitP (Ref.leNat (Ref.slice z 4 4)) < 2 ^ 32 := by unfold Ref.splitP; omega
  have bw : Ref.splitP (Ref.leNat (Ref.slice w 4 4)) < 2 ^ 32 := by unfold Ref.splitP; omega
  rw [Nat.mod_eq_of_lt bx, Nat.mod_eq_of_lt bw] at eB'
  have ep : Ref.leNat (Ref.slice z 4 4) = Ref.leNat (Ref.slice w 4 4) := by
    unfold Ref.splitP at eB'; omega
  have e4 : Ref.slice z 4 4 = Ref.slice w 4 4 := by
    rw [← le32_leNat (Ref.slice z 4 4) (hlength_slice _ _ _ (by omega)),
      ← le32_leNat (Ref.slice w 4 4) (hlength_slice _ _ _ (by omega)), ep]
  have eP : Ref.slice z 16 16 = Ref.slice w 16 16 := by
    rw [slice_toB_zero x 16 hx.2.2.2.1, slice_toB_zero y 16 hy.2.2.2.1]
  rw [decomp5 z, decomp5 w, eA, e4, eC, eP, eD, eE]

/-- A record input and a padded input never share a query: equal queries force tag 1, hence a record
chain block, whose bytes `16 .. 48` are zero, while the padded block carries its nonzero pad there. -/
theorem fmtQ_honest_ne_pad {x y : List UInt8} (hx : Honest x) (hy : PadHonest y) : fmtQ x ≠ fmtQ y := by
  intro hxy
  have ly : (toB y).length = 80 := by rw [length_toB]; exact hy.2.1
  have hL : Ref.fmtList (toB x) = Ref.padChainBlock (toB y) := by
    rw [← bytes_fmtQ_of_padHonest hy, ← hxy]
    exact (Ref.toList_fmt (toB x)).symm
  have hx2 := honest_length x hx
  have hb : (toB x).getD 1 0 = Ref.byte 1 := by
    have e := congrArg (fun l => l.getD 1 0) hL
    rw [Ref.getD_fmtList _ _ (Or.inl (by omega))] at e
    rw [e]
    unfold Ref.padChainBlock
    simp only [List.append_assoc, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by simp [ly])]
    rw [List.getElem?_take_of_lt (by omega)]
    rw [← List.getD_eq_getElem?_getD]
    exact tag_toB y 1 hy.2.2.1
  have h1 := tag_of_toB hb
  have hl48 : x.length = 48 := by rw [hx.2.1, h1]; rfl
  have lx : (toB x).length = 48 := by rw [length_toB]; exact hl48
  have hcx : Ref.IsChainFmt (toB x) := ⟨lx, hb⟩
  have hy80 := hy.2.1
  unfold Ref.fmtList at hL
  rw [if_pos hcx] at hL
  unfold Ref.chainBlock Ref.padChainBlock at hL
  obtain ⟨e1, _⟩ := List.append_inj hL (by simp [Ref.slice]; omega)
  obtain ⟨_, eD⟩ := List.append_inj e1 (by simp [Ref.slice]; omega)
  exact slice32_ne_zeros hy eD.symm

/-- **The formal common-offset condition for W1a**: the oracle input format is injective on the
padded game's honest inputs. -/
theorem fmtQ_injOn_honestP : Set.InjOn fmtQ HonestP := by
  intro x hx y hy hxy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact fmtQ_injOn hx hy hxy
  · exact absurd hxy (fmtQ_honest_ne_pad hx hy)
  · exact absurd hxy.symm (fmtQ_honest_ne_pad hy hx)
  · exact padHonest_inj hx hy hxy

/-! ### The abstract padded chain input is `PadHonest`, and its query is the W1a block -/

theorem length_bytesLE16 (v : Digest) : (SphincsSecurity.bytesLE 16 v).length = 16 := length_bytesLE 16 v

theorem bytesLE16_zero : SphincsSecurity.bytesLE 16 (0 : Digest) = List.replicate 16 0 := by
  unfold SphincsSecurity.bytesLE
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_replicate]
  apply UInt8.toBitVec_inj.mp
  simp [BitVec.extractLsb']

/-- The facts `PadHonest` asks of the first 32 bytes are those of any input with the same 32-byte
prefix. -/
theorem prefix32_facts {x y : List UInt8} (h : x.take 32 = y.take 32) :
    x.head? = y.head? ∧ x.getD 1 0 = y.getD 1 0 ∧ (x.drop 16).take 16 = (y.drop 16).take 16 ∧
      posField x = posField y := by
  have hhead : x.head? = y.head? := by
    have e := congrArg (fun l => l[0]?) h
    simp only [List.getElem?_take] at e
    rw [List.head?_eq_getElem?, List.head?_eq_getElem?]
    simpa using e
  refine ⟨hhead, ?_, ?_, ?_⟩
  · have := congrArg (fun l => l.getD 1 0) h
    simpa [List.getD_eq_getElem?_getD, List.getElem?_take] using this
  · have e := congrArg (fun l => (l.drop 16).take 16) h
    simp only [List.drop_take, List.take_take] at e
    simpa using e
  · unfold posField Ref.slice
    have e := congrArg (fun l => ((toB l).drop 4).take 4) h
    simp only [toB, ← List.map_take, ← List.map_drop, List.drop_take, List.take_take] at e ⊢
    simp only [show min 4 28 = 4 from rfl] at e
    rw [e]

theorem bytesLE16_ne_zero_pair {pad : Digest × Digest} (hpad : pad ≠ 0) :
    SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2 ≠ List.replicate 32 0 := by
  intro h
  have h' : SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2 =
      SphincsSecurity.bytesLE 16 (0 : Digest) ++ SphincsSecurity.bytesLE 16 (0 : Digest) := by
    rw [h, bytesLE16_zero]; rfl
  obtain ⟨e1, e2⟩ := List.append_inj h' (by rw [length_bytesLE16, length_bytesLE16])
  apply hpad
  exact Prod.ext (SphincsSecurity.bytesLE_injective e1) (SphincsSecurity.bytesLE_injective e2)

/-- **Every padded query of the abstract padded verifier is `PadHonest`** (parameter `0`). -/
theorem padHonest_chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (step : SphincsSecurity.ChainStep) (pad : SphincsSecurity.Pad) (hpad : pad ≠ 0) (v : Digest) :
    PadHonest (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step)
      (SphincsSecurity.Concrete.chainPayload pad v)) := by
  have hstep := step.isLt
  have hc := c.isLt
  have hbase : Honest (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step)
      (SphincsSecurity.bytesLE 16 v)) := by
    rw [tweakableHashInput_eq]
    refine honest_tw 1 lay.val tree.val (SphincsSecurity.chainLength * c.val + step.val) leaf.val 0 _
      (by simp [tagLen, length_bytesLE]) (fun _ => ⟨rfl, ?_⟩) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide))
    simp only [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits, SphincsSecurity.numChains] at hstep hc ⊢
    omega
  set x := SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) (SphincsSecurity.bytesLE 16 v)
  set y := SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) (SphincsSecurity.Concrete.chainPayload pad v)
  have hpre : SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) [] =
      SphincsSecurity.tweakBytes (.chain lay tree leaf c step) ++ SphincsSecurity.bytesLE 16 (0 : SphincsSecurity.PublicParameter) := by
    simp [SphincsSecurity.tweakableHashInput]
  have hlen32 : (SphincsSecurity.tweakBytes (.chain lay tree leaf c step) ++
      SphincsSecurity.bytesLE 16 (0 : SphincsSecurity.PublicParameter)).length = 32 := by
    rw [List.length_append, length_bytesLE]
    simp [SphincsSecurity.tweakBytes, length_fieldBytes]
  have htx : x.take 32 = y.take 32 := by
    simp only [x, y, SphincsSecurity.tweakableHashInput, List.append_assoc]
    rw [← List.append_assoc, List.take_left' hlen32, ← List.append_assoc, List.take_left' hlen32]
  obtain ⟨e1, e2, e3, e4⟩ := prefix32_facts htx
  have hlenY : y.length = 80 := by
    simp only [y, SphincsSecurity.tweakableHashInput, SphincsSecurity.Concrete.chainPayload, if_neg hpad, List.length_append,
      length_bytesLE]
    simp [SphincsSecurity.tweakBytes, length_fieldBytes]
  have hx1 : x.getD 1 0 = 1 := by
    simp only [x, tweakableHashInput_eq, List.append_assoc, getD1_fieldBytes]
    rfl
  obtain ⟨hh, hl, hP, hpos⟩ : x.head? = some 1 ∧ x.length = tagLen (x.getD 1 0).toNat ∧
      ((x.getD 1 0 = 1 → (x.drop 16).take 16 = List.replicate 16 0 ∧ posField x < 2 ^ 27)) ∧ True :=
    ⟨hbase.1, hbase.2.1, hbase.2.2.1, trivial⟩
  obtain ⟨hP16, hpos27⟩ := hP hx1
  refine ⟨e1 ▸ hh, hlenY, e2 ▸ hx1, e3 ▸ hP16, e4 ▸ hpos27, ?_⟩
  have hdrop : (y.drop 32).take 32 = SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2 := by
    simp only [y, SphincsSecurity.tweakableHashInput, SphincsSecurity.Concrete.chainPayload, if_neg hpad, List.append_assoc]
    rw [← List.append_assoc (SphincsSecurity.tweakBytes _), List.drop_left' hlen32, ← List.append_assoc,
      List.take_left' (by rw [List.length_append, length_bytesLE16, length_bytesLE16])]
  rw [hdrop]
  exact bytesLE16_ne_zero_pair hpad

theorem padChainBlock_append (A Pb Vb : List Byte) (hA : A.length = 32) (hP : Pb.length = 32) :
    Ref.padChainBlock (A ++ (Pb ++ Vb)) =
      (A.take 4 ++ Ref.le32 (Ref.splitP (Ref.leNat (Ref.slice A 4 4))) ++ Ref.slice A 8 8) ++ Pb ++ Vb := by
  unfold Ref.padChainBlock
  have e1 : (A ++ (Pb ++ Vb)).take 4 = A.take 4 := List.take_append_of_le_length (by omega)
  rw [e1, hslice_append_left _ _ 4 4 (by omega),
    hslice_append_left _ _ 8 8 (by omega)]
  have h32 : Ref.slice (A ++ (Pb ++ Vb)) 32 32 = Pb := by
    unfold Ref.slice
    rw [List.drop_left' hA, List.take_left' hP]
  have h64 : (A ++ (Pb ++ Vb)).drop 64 = Vb := by
    rw [show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, List.drop_left' hA, List.drop_left' hP]
  rw [h32, h64]

theorem chainBlock_append_take (A Vb : List Byte) (hA : A.length = 32) :
    (Ref.chainBlock (A ++ Vb)).take 16 =
      A.take 4 ++ Ref.le32 (Ref.splitP (Ref.leNat (Ref.slice A 4 4))) ++ Ref.slice A 8 8 := by
  unfold Ref.chainBlock
  have e1 : (A ++ Vb).take 4 = A.take 4 := List.take_append_of_le_length (by omega)
  rw [e1, hslice_append_left _ _ 4 4 (by omega), hslice_append_left _ _ 8 8 (by omega)]
  have hl : (A.take 4 ++ Ref.le32 (Ref.splitP (Ref.leNat (Ref.slice A 4 4))) ++ Ref.slice A 8 8).length = 16 := by
    simp [Ref.slice, hA]
  rw [List.append_assoc (A.take 4 ++ Ref.le32 (Ref.splitP (Ref.leNat (Ref.slice A 4 4))) ++ Ref.slice A 8 8)
    (Ref.zeros 32), List.take_left' hl]

/-- **The machine view** of a padded chain step: its oracle query is the record's chain block with
the 32 zero bytes replaced by the pad, `tw' ‖ pad ‖ v` (what `Ref.verifyRef` hashes in place in the
W1a witness block). With a zero pad the input is the record chain input (`Ref.fmt_of_chain`). -/
theorem fmtQ_padded_bytes (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex) (step : SphincsSecurity.ChainStep)
    (pad : Digest × Digest) (hpad : pad ≠ 0) (v : Digest) :
    Ref.toList (fmtQ (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) (SphincsSecurity.Concrete.chainPayload pad v))).2 =
      (Ref.chainBlock (toB (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step)
          (SphincsSecurity.bytesLE 16 v)))).take 16 ++
        toB (SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2) ++
        toB (SphincsSecurity.bytesLE 16 v) := by
  rw [bytes_fmtQ_of_padHonest (padHonest_chain lay tree leaf c step pad hpad v)]
  set T := SphincsSecurity.tweakBytes (.chain lay tree leaf c step) ++
    SphincsSecurity.bytesLE 16 (0 : SphincsSecurity.PublicParameter) with hT
  have hT32 : (toB T).length = 32 := by
    rw [length_toB, hT, List.length_append, length_bytesLE]
    simp [SphincsSecurity.tweakBytes, length_fieldBytes]
  have hx : toB (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) (SphincsSecurity.bytesLE 16 v)) =
      toB T ++ toB (SphincsSecurity.bytesLE 16 v) := by
    simp only [hT, SphincsSecurity.tweakableHashInput, toB, List.map_append]
  have hy : toB (SphincsSecurity.tweakableHashInput 0 (.chain lay tree leaf c step) (SphincsSecurity.Concrete.chainPayload pad v)) =
      toB T ++ (toB (SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2) ++
        toB (SphincsSecurity.bytesLE 16 v)) := by
    simp only [hT, SphincsSecurity.tweakableHashInput, SphincsSecurity.Concrete.chainPayload, if_neg hpad, toB, List.map_append,
      List.append_assoc]
  have hP32 : (toB (SphincsSecurity.bytesLE 16 pad.1 ++ SphincsSecurity.bytesLE 16 pad.2)).length = 32 := by
    rw [length_toB, List.length_append, length_bytesLE16, length_bytesLE16]
  rw [hx, hy, padChainBlock_append _ _ _ hT32 hP32, chainBlock_append_take _ _ hT32]


/-! ### The padded verifier makes only `HonestP` queries -/

/-- Every query of an abstract computation is honest for the padded game. -/
abbrev HQP {α : Type} (oa : AComp α) : Prop :=
  AllQ (ι := List UInt8) (R := SphincsSecurity.HashOutput) HonestP oa

theorem allQ_mono {P Q : List UInt8 → Prop} (hPQ : ∀ x, P x → Q x) {α : Type} {oa : AComp α}
    (h : AllQ (ι := List UInt8) (R := SphincsSecurity.HashOutput) P oa) :
    AllQ (ι := List UInt8) (R := SphincsSecurity.HashOutput) Q oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact allQ_pure Q x
  | query_bind t k ih =>
    rw [SigGolfCandidate.Bridge.allQ_query_bind] at h ⊢
    exact ⟨hPQ _ h.1, fun u => ih u (h.2 u)⟩

theorem hqp_of_hq {α : Type} {oa : AComp α} (h : HQ oa) : HQP oa := allQ_mono (fun _ hx => Or.inl hx) h

theorem hqp_pure {α : Type} (a : α) : HQP (pure a : AComp α) := allQ_pure HonestP a

theorem hqp_bind {α β : Type} {oa : AComp α} {ob : α → AComp β} (h : HQP oa) (h' : ∀ x, HQP (ob x)) :
    HQP (oa >>= ob) := allQ_bind HonestP h h'

theorem hqp_sequenceFin {α : Type} {n : Nat} (c : Fin n → AComp α) (h : ∀ j, HQP (c j)) :
    HQP (sequenceFin c) := by
  induction n with
  | zero => exact hqp_pure _
  | succ n ih =>
    exact hqp_bind (h 0) fun _ => hqp_bind (ih _ fun j => h j.succ) fun _ => hqp_pure _

theorem hqp_chainWalkP (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (pad : SphincsSecurity.Pad) (start steps : Nat) (v : Digest) :
    HQP (SphincsSecurity.Concrete.chainWalkP (m := AComp) 0 lay tree leaf c pad start steps v) := by
  induction steps with
  | zero => exact hqp_pure _
  | succ n ih =>
    refine hqp_bind ih fun prev => ?_
    split
    · rename_i hstep
      refine hqp_bind ((allQ_query (R := SphincsSecurity.HashOutput) HonestP _).mpr ?_) fun _ => hqp_pure _
      by_cases hpad : pad = 0
      · subst hpad
        left
        rw [show SphincsSecurity.Concrete.chainPayload 0 prev = SphincsSecurity.bytesLE 16 prev from if_pos rfl,
          tweakableHashInput_eq]
        refine honest_tw 1 lay.val tree.val (SphincsSecurity.chainLength * c.val + (start + n)) leaf.val 0 _
          (by simp [tagLen, length_bytesLE]) (fun _ => ⟨rfl, ?_⟩) (fun h => absurd h (by decide))
          (fun h => absurd h (by decide))
        have e : SphincsSecurity.chainLength = 8 := rfl
        have hc := c.isLt
        unfold SphincsSecurity.numChains at hc
        rw [e] at hstep ⊢
        exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
      · exact Or.inr (padHonest_chain lay tree leaf c _ pad hpad prev)
    · exact hqp_pure _

theorem hqp_otsLeafP (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (c : SphincsSecurity.Counter) (values : ChainIndex → Digest) (pads : ChainIndex → SphincsSecurity.Pad) :
    HQP (SphincsSecurity.Concrete.otsLeafP (m := AComp) 0 lay tree leaf M c values pads) := by
  unfold SphincsSecurity.Concrete.otsLeafP
  refine hqp_bind (hqp_of_hq (hq_encode _ _ _ _ _ _)) fun r => ?_
  split
  · exact hqp_bind (hqp_sequenceFin _ fun c => hqp_chainWalkP _ _ _ _ _ _ _ _) fun _ =>
      hqp_bind (hqp_of_hq (hq_leafHash _ _ _ _ _)) fun _ => hqp_pure _
  · exact hqp_pure _

theorem hqp_verifyLayersP (index : Index) (σ : Signature) (pads : SphincsSecurity.ChainPads) (n : Nat)
    (M : Digest) : HQP (SphincsSecurity.Concrete.verifyLayersP (m := AComp) 0 index σ pads n M) := by
  induction n generalizing M with
  | zero => exact hqp_pure _
  | succ n ih =>
    unfold SphincsSecurity.Concrete.verifyLayersP
    split
    · refine hqp_bind (hqp_otsLeafP _ _ _ _ _ _ _) fun r => ?_
      split
      · exact hqp_bind (hqp_of_hq (hq_treeFold _ _ _ _ _ (Nat.mod_lt _ (Nat.two_pow_pos _)) _ le_rfl _))
          fun _ => ih _
      · exact hqp_pure _
    · exact hqp_pure _

/-- **The padded verifier** makes only `HonestP` queries, for every pad. -/
theorem hq_verifyP (pk : SphincsSecurity.PublicKey) (hP : pk.parameter = 0) (m : Message)
    (σ : Signature) (pads : SphincsSecurity.ChainPads) :
    HQP (SphincsSecurity.Concrete.verifyP (m := AComp) pk m σ pads) := by
  unfold SphincsSecurity.Concrete.verifyP SphincsSecurity.Concrete.verifyCoreP
  split
  · refine hqp_bind (hqp_of_hq (hq_messageDigest _ hP _ _ _)) fun d => ?_
    refine hqp_bind (hqp_of_hq (hq_ftsRecover _ _ _ _)) fun r => ?_
    split
    · rw [hP]
      refine hqp_bind (hqp_verifyLayersP _ _ _ _ _) fun r => ?_
      split <;> exact hqp_pure _
    · exact hqp_pure _
  · exact hqp_pure _

end SigGolfCandidate.Equiv
