import SigGolfCandidate.Ref.Lemmas
import SigGolfCandidate.Ref.AddressFormat
import SigGolfCandidate.Rv.Hash

/-! The address-header words (formerly `Ref/AddressWords`). -/
namespace SigGolfCandidate.Ref.AddressFormat
open SigGolfCandidate.Legacy SigGolfCandidate.Rv
set_option exponentiation.threshold 1024

theorem wordsToNat_lt (ws : List Word) : wordsToNat ws < 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => decide
  | cons w ws ih =>
    have hw := w.isLt
    simp only [wordsToNat, List.length_cons]
    rw [show 64 * (ws.length + 1) = 64 + 64 * ws.length by omega, Nat.pow_add]
    omega

/-- The swapped header words (`LeafScale.swRel f`) of a block with words `w0`, `w1`. -/
def swW0 (w0 w1 : Word) : Word := BitVec.ofNat 64 (w0.toNat % 4294967296 + 4294967296 * (w1.toNat % 4294967296))
def swW1 (f : Nat → Nat) (w0 w1 : Word) : Word :=
  BitVec.ofNat 64 (w0.toNat / 4294967296 + 4294967296 * f (w1.toNat / 4294967296))

theorem swRel_words (f : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296)
    (w0 w1 : Word) (ws : List Word) :
    LeafScale.swRel f (wordsToNat (w0 :: w1 :: ws)) = wordsToNat (swW0 w0 w1 :: swW1 f w0 w1 :: ws) := by
  have h0 := w0.isLt
  have h1 := w1.isLt
  have he := hf (w1.toNat / 4294967296) (by norm_num only [Nat.reducePow] at h1; omega)
  norm_num only [Nat.reducePow] at h0 h1
  have hx0 : w0.toNat % 4294967296 + 4294967296 * (w1.toNat % 4294967296) < 18446744073709551616 := by omega
  have hx1 : w0.toNat / 4294967296 + 4294967296 * f (w1.toNat / 4294967296) < 18446744073709551616 := by
    omega
  have e1 : wordsToNat (w0 :: w1 :: ws) =
      w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws) := rfl
  have e2 : wordsToNat (swW0 w0 w1 :: swW1 f w0 w1 :: ws) =
      (w0.toNat % 4294967296 + 4294967296 * (w1.toNat % 4294967296)) + 18446744073709551616 *
        (w0.toNat / 4294967296 + 4294967296 * f (w1.toNat / 4294967296) +
          18446744073709551616 * wordsToNat ws) := by
    show (BitVec.ofNat 64 _).toNat + 18446744073709551616 * ((BitVec.ofNat 64 _).toNat +
      18446744073709551616 * wordsToNat ws) = _
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx0, Nat.mod_eq_of_lt hx1]
  rw [e1, e2, LeafScale.swRel_eq f _ _ _ h0 h1]

theorem wordsToNat_lt8 (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6) :
    wordsToNat (w0 :: w1 :: ws) < 2 ^ 512 := by
  have := wordsToNat_lt (w0 :: w1 :: ws)
  simpa [hlen] using this

theorem wordsToNat_class (w0 : Word) (ws : List Word) :
    wordsToNat (w0 :: ws) % 65536 = w0.toNat % 65536 := by
  show (w0.toNat + 18446744073709551616 * wordsToNat ws) % 65536 = _
  omega

/-- The tag-10 (PORS node) class: fields 1, 2 swap, the header field is relabelled by `Rev.efield`. -/
theorem baseQueryPerm_node (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2561) :
    baseQueryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 Rev.efield w0 w1 :: ws) := by
  have hN := wordsToNat_lt8 w0 w1 ws hlen
  have hcls : wordsToNat (w0 :: w1 :: ws) % 65536 = 2561 := (wordsToNat_class _ _).trans hc
  simp only [queryOfWords, baseQueryPerm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN,
    fullPerm_of_eq _ hcls, nodeRel, swRel_words _ efield_lt']

theorem baseQueryPerm_words (w : Word) (ws : List Word) (hlen : ws.length = 7)
    (hc : w.toNat % 65536 ≠ 2561) :
    baseQueryPerm (queryOfWords 0 (w :: ws)) =
      queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws) := by
  have h := wordsToNat_lt (w :: ws)
  have ht := wordsToNat_lt ws
  have hw := w.isLt
  have hp := wordPerm_lt w.toNat hw
  simp only [List.length_cons, hlen] at h ht
  simp only [wordsToNat] at h
  simp only [queryOfWords, baseQueryPerm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, wordsToNat]
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow] at h ht hw hp ⊢
  rw [Nat.mod_eq_of_lt h]
  have hc' : (w.toNat + 18446744073709551616 * wordsToNat ws) % 65536 ≠ 2561 := by omega
  rw [fullPerm_of_ne _ hc']
  unfold payloadPerm
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hw,
    Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hw, Nat.zero_add,
    Nat.mod_eq_of_lt hp]


/-- A one-block query retains the low two bytes of its first word. -/
theorem queryOfWords_class (w : Word) (ws : List Word) :
    (queryOfWords 0 (w :: ws)).2.toNat % 65536 = w.toNat % 65536 := by
  simp only [queryOfWords, BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 512)]
  change (w.toNat + 18446744073709551616 * wordsToNat ws) % 65536 = _
  omega

theorem wordPerm_leaf_class (w : Nat) (h : w % 65536 ≠ 2305) : wordPerm w % 65536 ≠ 2305 := by
  unfold wordPerm
  split_ifs with ho hn
  · simp only [oldValid] at ho
    unfold oldToNew
    omega
  · simp only [newValid] at hn
    dsimp only [newToOld]
    omega
  · exact h

theorem wordPerm_encoding_class (w : Nat) (h : w % 65536 ≠ 1025) : wordPerm w % 65536 ≠ 1025 := by
  unfold wordPerm
  split_ifs with ho hn
  · simp only [oldValid] at ho
    unfold oldToNew
    omega
  · simp only [newValid] at hn
    dsimp only [newToOld]
    omega
  · exact h

theorem swW0_class (w0 w1 : Word) : (swW0 w0 w1).toNat % 65536=w0.toNat % 65536 := by
  unfold swW0
  rw [BitVec.toNat_ofNat]
  norm_num only [Nat.reducePow]
  omega

theorem queryPerm_node (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2561) :
    queryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 Rev.efield w0 w1 :: ws) := by
  have hcls : (queryOfWords 0 (swW0 w0 w1 :: swW1 Rev.efield w0 w1 :: ws)).2.toNat % 65536=2561 := by
    rw [queryOfWords_class,swW0_class,hc]
  rw [queryPerm,baseQueryPerm_node w0 w1 ws hlen hc,
    LeafScale.queryRel_fixed _ (by rw [hcls];decide),
    EncodingSwap.query_fixed _ (by rw [hcls];decide),
    LeafClass.query_fixed_length _ (by change (0:Nat)≠10;decide)]

theorem queryPerm_words (w : Word) (ws : List Word) (hlen : ws.length = 7)
    (hc : w.toNat % 65536 ≠ 2561) (h9 : w.toNat % 65536 ≠ 2305)
    (h4 : w.toNat % 65536 ≠ 1025) :
    queryPerm (queryOfWords 0 (w :: ws)) =
      queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws) := by
  have hleaf : (queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws)).2.toNat%65536≠2305 := by
    rw [queryOfWords_class, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wordPerm_lt _ w.isLt)]
    exact wordPerm_leaf_class _ h9
  have henc : (queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws)).2.toNat%65536≠1025 := by
    rw [queryOfWords_class, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wordPerm_lt _ w.isLt)]
    exact wordPerm_encoding_class _ h4
  rw [queryPerm,baseQueryPerm_words w ws hlen hc,LeafScale.queryRel_fixed _ hleaf,EncodingSwap.query_fixed _ henc,LeafClass.query_fixed_length _ (by change (0:Nat)≠10;decide)]

theorem queryPerm_leaf (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2305) :
    queryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 LeafScale.left3 w0 w1 :: ws) := by
  have hN := wordsToNat_lt8 w0 w1 ws hlen
  have hclsQ : (queryOfWords 0 (w0 :: w1 :: ws)).2.toNat % 65536 = 2305 := by
    rw [queryOfWords_class, hc]
  have hbase : baseQueryPerm (queryOfWords 0 (w0 :: w1 :: ws)) = queryOfWords 0 (w0 :: w1 :: ws) := by
    apply baseQueryPerm_fixed <;> omega
  have hleaf : LeafScale.queryRel (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 LeafScale.left3 w0 w1 :: ws) := by
    have hred : LeafScale.queryRel (queryOfWords 0 (w0 :: w1 :: ws)) =
        ⟨0, BitVec.ofNat 512 (LeafScale.rel (queryOfWords 0 (w0 :: w1 :: ws)).2.toNat)⟩ := by
      simp only [queryOfWords, LeafScale.queryRel] at hclsQ ⊢
      rw [if_pos hclsQ]
    rw [hred]
    simp only [queryOfWords]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN, LeafScale.rel,
      swRel_words _ LeafScale.left3_lt']
  have hcls : (queryOfWords 0 (swW0 w0 w1 :: swW1 LeafScale.left3 w0 w1 :: ws)).2.toNat % 65536=2305 := by
    rw [queryOfWords_class,swW0_class,hc]
  rw [queryPerm,hbase,hleaf,EncodingSwap.query_fixed _ (by rw [hcls];decide),
    LeafClass.query_fixed_length _ (by change (0:Nat)≠10;decide)]

end SigGolfCandidate.Ref.AddressFormat

/-! The relabelled queries. -/

namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy SigGolfCandidate.Rv
set_option exponentiation.threshold 1024

/-- The format keeps the protocol and tag bytes. -/
theorem fmt_low_bytes (x : List Byte) :
    (fmt x).2.toNat % 256 = (x.getD 0 0).toNat ∧
    (fmt x).2.toNat / 256 % 256 = (x.getD 1 0).toNat := by
  have h0 := leNat_div_mod (toList (fmt x).2) 0
  have h1 := leNat_div_mod (toList (fmt x).2) 1
  rw [leNat_toList, getD_toList_fmt x 0 (by omega)] at h0
  rw [leNat_toList, getD_toList_fmt x 1 (by omega)] at h1
  simpa using And.intro h0 h1

/-- Non-chain tags retain their old oracle query. -/
theorem addrFmt_eq_of_prefix (x : List Byte)
    (h0 : (x.getD 0 0).toNat % 64 ≠ 0)
    (h1 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 257)
    (h2 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 2561)
    (h9 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 2305)
    (h4 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 1025)
    (hL : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 513) :
    addrFmt x = fmt x := by
  apply AddressFormat.queryPerm_fixed
  · have h := (fmt_low_bytes x).1
    omega
  · have h := fmt_low_bytes x
    omega
  · have h := fmt_low_bytes x
    omega

  · have h := fmt_low_bytes x
    omega
  · have h := fmt_low_bytes x
    omega
  · have h := fmt_low_bytes x
    omega

theorem addrFmt_eq_th (t lay tau p j : Nat) (payload : List Byte)
    (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 10 ∧ t % 256 ≠ 9 ∧ t % 256 ≠ 4 ∧ t % 256 ≠ 2) :
    addrFmt (thInput (tweak t lay tau p j) payload) =
      fmt (thInput (tweak t lay tau p j) payload) := by
  apply addrFmt_eq_of_prefix
  · simp [thInput, tweak, byte_toNat]
  · simp [thInput, tweak, byte_toNat]
    omega
  · simp [thInput, tweak, byte_toNat]
    omega

  · simp [thInput, tweak, byte_toNat]
    omega
  · simp [thInput, tweak, byte_toNat]
    omega
  · simp [thInput, tweak, byte_toNat]
    omega

theorem addrFmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 2, byte 3, byte 4, byte 9, byte 10, byte 12]) :
    addrFmt (thInput (tweak t lay tau p j) payload) =
      pad64 (thInput (tweak t lay tau p j) payload) := by
  have hb : ∀ k, k < 256 → byte t = byte k → t % 256 = k := by
    intro k hk h
    have := congrArg BitVec.toNat h
    simp only [byte_toNat] at this
    omega
  have h1 : t % 256 ≠ 1 ∧ t % 256 ≠ 10 ∧ t % 256 ≠ 9 ∧ t % 256 ≠ 4 ∧ t % 256 ≠ 2 := by
    have heq : ∀ k, t % 256 = k → byte t = byte k := by
      intro k h
      apply BitVec.eq_of_toNat_eq
      simp [byte_toNat, h, Nat.mod_eq_of_lt (show k < 256 by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h; apply ht; simp [heq 1 h]
    · intro h; apply ht; simp [heq 10 h]
    · intro h; apply ht; simp [heq 9 h]
    · intro h; apply ht; simp [heq 4 h]
    · intro h; apply ht; simp [heq 2 h]
  have ht' : byte t ∉ [byte 1, byte 3, byte 12] := by
    intro hm; apply ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto
  rw [addrFmt_eq_th _ _ _ _ _ _ h1, fmt_thInput _ _ _ _ _ _ ht']

@[simp] theorem addrFmt_prfInput (S : List Byte) (lay tau e i : Nat) :
    addrFmt (prfInput S lay tau e i) = fmt (prfInput S lay tau e i) := by
  unfold prfInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_leafInput (lay tau e : Nat) (ends : List Val) :
    addrFmt (leafInput lay tau e ends) = LeafClass.query (fmt (leafInput lay tau e ends)) := by
  unfold addrFmt AddressFormat.queryPerm
  congr 1
  have hc : (fmt (leafInput lay tau e ends)).2.toNat%65536=513 := by
    have h := fmt_low_bytes (leafInput lay tau e ends)
    simp [leafInput,thInput,tweak,byte_toNat] at h ⊢;omega
  rw [AddressFormat.baseQueryPerm_fixed _ (by omega) (by omega) (by omega),
    LeafScale.queryRel_fixed _ (by omega),EncodingSwap.query_fixed _ (by omega)]

@[simp] theorem addrFmt_nodeInput (lay tau lam j : Nat) (l r : Val) :
    addrFmt (nodeInput lay tau lam j l r) = fmt (nodeInput lay tau lam j l r) := by
  unfold nodeInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_encInput (lay tau e : Nat) (M : Val) (c : Nat) :
    addrFmt (encInput lay tau e M c) = LeafClass.query (EncodingSwap.query (fmt (encInput lay tau e M c))) := by
  unfold addrFmt AddressFormat.queryPerm
  congr 1
  congr 1
  rw [AddressFormat.baseQueryPerm_fixed _ (by
    have h := fmt_low_bytes (encInput lay tau e M c)
    simp [encInput,thInput,tweak,byte_toNat] at h ⊢;omega) (by
    have h := fmt_low_bytes (encInput lay tau e M c)
    simp [encInput,thInput,tweak,byte_toNat] at h ⊢;omega) (by
    have h := fmt_low_bytes (encInput lay tau e M c)
    simp [encInput,thInput,tweak,byte_toNat] at h ⊢;omega)]
  apply LeafScale.queryRel_fixed
  have h := fmt_low_bytes (encInput lay tau e M c)
  simp [encInput,thInput,tweak,byte_toNat] at h ⊢;omega

@[simp] theorem addrFmt_porsPrfInput (S : List Byte) (idx q : Nat) :
    addrFmt (porsPrfInput S idx q) = fmt (porsPrfInput S idx q) := by
  unfold porsPrfInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_porsLeafInput (idx j : Nat) (v : Val) :
    addrFmt (porsLeafInput idx j v) = LeafScale.queryRel (fmt (porsLeafInput idx j v)) := by
  have hbase : AddressFormat.baseQueryPerm (fmt (porsLeafInput idx j v)) = fmt (porsLeafInput idx j v) := by
    apply AddressFormat.baseQueryPerm_fixed
    all_goals
      have h := fmt_low_bytes (porsLeafInput idx j v)
      simp [porsLeafInput,thInput,tweak,byte_toNat] at h ⊢;omega
  have hc : (LeafScale.queryRel (fmt (porsLeafInput idx j v))).2.toNat%65536=2305 := by
    have h := fmt_low_bytes (porsLeafInput idx j v)
    rw [LeafScale.queryRel_class]
    simp [porsLeafInput,thInput,tweak,byte_toNat] at h ⊢;omega
  unfold addrFmt AddressFormat.queryPerm
  rw [hbase,EncodingSwap.query_fixed _ (by omega),LeafClass.query_fixed _ (by omega) (by omega)]

-- `addrFmt (porsNodeInput ..)` relabels the header field: see `Verify.Words.addrFmt_porsNodeInput`.

@[simp] theorem addrFmt_digestInput (rho m : List Byte) :
    addrFmt (digestInput rho m) = fmt (digestInput rho m) := by
  unfold digestInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_macInput (S region : List Byte) :
    addrFmt (macInput S region) = fmt (macInput S region) := by
  unfold macInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_rndInput (S m : List Byte) (a : Nat) :
    addrFmt (rndInput S m a) = fmt (rndInput S m a) := by
  apply addrFmt_eq_of_prefix <;> simp [rndInput, byte_toNat]

end SigGolfCandidate.Ref

namespace SigGolfCandidate.Ref.EncodingSwap
open SigGolfCandidate.Legacy SigGolfCandidate.Rv SigGolfCandidate.Ref.AddressFormat
set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

theorem query_words (w0 w1 w2 w3 w4 w5 w6 w7 : Word)
    (hc : w0.toNat%65536=1025) :
    query (queryOfWords 0 [w0,w1,w2,w3,w4,w5,w6,w7]) =
      queryOfWords 0 [w0,w1,w2,w3,w6,w7,w4,w5] := by
  let a := wordsToNat [w0,w1,w2,w3]
  let b := wordsToNat [w4,w5]
  let c := wordsToNat [w6,w7]
  have ha : a<2^256 := wordsToNat_lt _
  have hb : b<2^128 := wordsToNat_lt _
  have hh : c<2^128 := wordsToNat_lt _
  have hform : wordsToNat [w0,w1,w2,w3,w4,w5,w6,w7] = a+2^256*b+2^384*c := by
    dsimp [a,b,c,wordsToNat];norm_num;ring
  have hform' : wordsToNat [w0,w1,w2,w3,w6,w7,w4,w5] = a+2^256*c+2^384*b := by
    dsimp [a,b,c,wordsToNat];norm_num;ring
  have hn : wordsToNat [w0,w1,w2,w3,w4,w5,w6,w7]<2^512 := wordsToNat_lt _
  have hc' : (queryOfWords 0 [w0,w1,w2,w3,w4,w5,w6,w7]).2.toNat%65536=1025 := by
    rw [queryOfWords_class,hc]
  change (BitVec.ofNat 512 (wordsToNat [w0,w1,w2,w3,w4,w5,w6,w7])).toNat%65536=1025 at hc'
  change (if _ then _ else _) = _
  rw [if_pos hc']
  simp only [queryOfWords]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hn,hform,hform',word_eq a b c ha hb hh]
end SigGolfCandidate.Ref.EncodingSwap

namespace SigGolfCandidate.Ref.LeafClass
open SigGolfCandidate.Legacy SigGolfCandidate.Rv SigGolfCandidate.Ref.AddressFormat
set_option exponentiation.threshold 8192
set_option maxRecDepth 10000

theorem word_of_class (w : Nat) (hc : w%65536=513) : word w=w+512 := by
  unfold word header
  rw [hc]
  norm_num
  omega

theorem query_pad_tag (rest : List Byte) (hlen : rest.length=702) :
    query (pad64 (byte 1::byte 2::rest))=pad64 (byte 1::byte 4::rest) := by
  have h2 : (byte 1::byte 2::rest).length=704 := by simp [hlen]
  have h4 : (byte 1::byte 4::rest).length=704 := by simp [hlen]
  have hn : leNat (byte 1::byte 2::rest)<2^5632 := by
    have h := leNat_lt (byte 1::byte 2::rest)
    rw [h2] at h
    simpa only [show (256:Nat)^704=2^5632 by norm_num] using h
  have hc : leNat (byte 1::byte 2::rest)%65536=513 := by
    simp only [leNat,byte_toNat];omega
  rw [pad64_eq _ 10 (by omega) (by omega),pad64_eq _ 10 (by omega) (by omega)]
  simp only [h2,h4,Nat.reduceAdd,Nat.reduceMul,Nat.sub_self,zeros,List.replicate_zero,List.append_nil]
  change (⟨10,BitVec.ofNat 5632 (word (BitVec.ofNat 5632 (leNat (byte 1::byte 2::rest))).toNat)⟩ : Query)=
    ⟨10,BitVec.ofNat 5632 (leNat (byte 1::byte 4::rest))⟩
  congr 1
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,word_of_class _ hc]
  congr 1
  simp only [leNat,byte_toNat]
  omega

theorem query_words (w : Word) (ws : List Word) (hlen : ws.length=87)
    (hc : w.toNat%65536=513) :
    query (queryOfWords 10 (w::ws))=
      queryOfWords 10 (BitVec.ofNat 64 (w.toNat+512)::ws) := by
  have hn : wordsToNat (w::ws)<2^5632 := by
    have h := wordsToNat_lt (w::ws)
    simpa only [List.length_cons,hlen,Nat.reduceAdd,Nat.reduceMul] using h
  have hw := w.isLt
  have hp : w.toNat+512<2^64 := by
    norm_num only [Nat.reducePow] at hw ⊢
    omega
  have hc' : wordsToNat (w::ws)%65536=513 := by
    change (w.toNat+18446744073709551616*wordsToNat ws)%65536=513
    omega
  change (⟨10,BitVec.ofNat 5632 (word (BitVec.ofNat 5632 (wordsToNat (w::ws))).toNat)⟩ : Query)=_
  simp only [queryOfWords]
  congr 1
  rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,word_of_class _ hc']
  congr 1
  simp only [wordsToNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hp]
  omega
end SigGolfCandidate.Ref.LeafClass

namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy SigGolfCandidate.Rv
set_option exponentiation.threshold 8192

theorem addrFmt_leafInput_tag4 (lay tau e : Nat) (ends : List Val) (hl : ends.length=42)
    (hv : ∀ v∈ends, v.length=16) :
    addrFmt (leafInput lay tau e ends)=pad64 (thInput (tweak 4 lay tau 0 e) ends.flatten) := by
  have hflat : ends.flatten.length=672 := by
    rw [List.length_flatten]
    have : ends.map List.length=List.replicate 42 16 := by
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2
      simp only [List.getElem_map,List.getElem_replicate]
      exact hv _ (List.getElem_mem _)
    rw [this];decide
  rw [addrFmt_leafInput]
  unfold leafInput
  rw [fmt_thInput _ _ _ _ _ _ (by decide)]
  change LeafClass.query (pad64 (byte 1::byte 2::_))=pad64 (byte 1::byte 4::_)
  apply LeafClass.query_pad_tag
  simp [thInput,tweak,P,hflat]

theorem addrFmt_encInput_valid (lay tau e : Nat) (M : Val) (hM : M.length=16) (c : Nat) :
    addrFmt (encInput lay tau e M c)=EncodingSwap.query (fmt (encInput lay tau e M c)) := by
  rw [addrFmt_encInput]
  apply LeafClass.query_fixed_length
  have hb := EncodingSwap.query_blocks (fmt (encInput lay tau e M c))
  have hn : (fmt (encInput lay tau e M c)).1=0 := by
    unfold encInput
    rw [fmt_thInput _ _ _ _ _ _ (by decide)]
    simp [pad64,padBlocks,thInput,hM]
  change (EncodingSwap.query (fmt (encInput lay tau e M c))).1+1=(fmt (encInput lay tau e M c)).1+1 at hb
  omega
end SigGolfCandidate.Ref
