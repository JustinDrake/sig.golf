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

theorem queryPerm_node (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2561) :
    queryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 Rev.efield w0 w1 :: ws) := by
  rw [queryPerm, baseQueryPerm_node w0 w1 ws hlen hc]
  apply LeafScale.queryRel_fixed
  rw [queryOfWords_class]
  unfold swW0
  rw [BitVec.toNat_ofNat]
  have := w0.isLt
  have := w1.isLt
  norm_num only [Nat.reducePow] at *
  omega

theorem queryPerm_words (w : Word) (ws : List Word) (hlen : ws.length = 7)
    (hc : w.toNat % 65536 ≠ 2561) (h9 : w.toNat % 65536 ≠ 2305) :
    queryPerm (queryOfWords 0 (w :: ws)) =
      queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws) := by
  rw [queryPerm, baseQueryPerm_words w ws hlen hc]
  apply LeafScale.queryRel_fixed
  rw [queryOfWords_class, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wordPerm_lt _ w.isLt)]
  exact wordPerm_leaf_class _ h9

theorem queryPerm_leaf (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2305) :
    queryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (swW0 w0 w1 :: swW1 LeafScale.left3 w0 w1 :: ws) := by
  have hN := wordsToNat_lt8 w0 w1 ws hlen
  have hclsQ : (queryOfWords 0 (w0 :: w1 :: ws)).2.toNat % 65536 = 2305 := by
    rw [queryOfWords_class, hc]
  have hbase : baseQueryPerm (queryOfWords 0 (w0 :: w1 :: ws)) = queryOfWords 0 (w0 :: w1 :: ws) := by
    apply baseQueryPerm_fixed <;> omega
  rw [queryPerm, hbase]
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
    (h9 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 2305) :
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

theorem addrFmt_eq_th (t lay tau p j : Nat) (payload : List Byte)
    (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 10 ∧ t % 256 ≠ 9) :
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

theorem addrFmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 9, byte 10, byte 12]) :
    addrFmt (thInput (tweak t lay tau p j) payload) =
      pad64 (thInput (tweak t lay tau p j) payload) := by
  have hb : ∀ k, k < 256 → byte t = byte k → t % 256 = k := by
    intro k hk h
    have := congrArg BitVec.toNat h
    simp only [byte_toNat] at this
    omega
  have h1 : t % 256 ≠ 1 ∧ t % 256 ≠ 10 ∧ t % 256 ≠ 9 := by
    have heq : ∀ k, t % 256 = k → byte t = byte k := by
      intro k h
      apply BitVec.eq_of_toNat_eq
      simp [byte_toNat, h, Nat.mod_eq_of_lt (show k < 256 by omega)]
    refine ⟨?_, ?_, ?_⟩
    · intro h; apply ht; simp [heq 1 h]
    · intro h; apply ht; simp [heq 10 h]
    · intro h; apply ht; simp [heq 9 h]
  have ht' : byte t ∉ [byte 1, byte 3, byte 12] := by
    intro hm; apply ht; simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto
  rw [addrFmt_eq_th _ _ _ _ _ _ h1, fmt_thInput _ _ _ _ _ _ ht']

@[simp] theorem addrFmt_prfInput (S : List Byte) (lay tau e i : Nat) :
    addrFmt (prfInput S lay tau e i) = fmt (prfInput S lay tau e i) := by
  unfold prfInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_leafInput (lay tau e : Nat) (ends : List Val) :
    addrFmt (leafInput lay tau e ends) = fmt (leafInput lay tau e ends) := by
  unfold leafInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_nodeInput (lay tau lam j : Nat) (l r : Val) :
    addrFmt (nodeInput lay tau lam j l r) = fmt (nodeInput lay tau lam j l r) := by
  unfold nodeInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_encInput (lay tau e : Nat) (M : Val) (c : Nat) :
    addrFmt (encInput lay tau e M c) = fmt (encInput lay tau e M c) := by
  apply addrFmt_eq_of_prefix <;> simp [encInput, tweak, byte_toNat]

@[simp] theorem addrFmt_porsPrfInput (S : List Byte) (idx q : Nat) :
    addrFmt (porsPrfInput S idx q) = fmt (porsPrfInput S idx q) := by
  unfold porsPrfInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_porsLeafInput (idx j : Nat) (v : Val) :
    addrFmt (porsLeafInput idx j v) = LeafScale.queryRel (fmt (porsLeafInput idx j v)) := by
  unfold addrFmt AddressFormat.queryPerm
  congr 1
  apply AddressFormat.baseQueryPerm_fixed
  all_goals
    have h := fmt_low_bytes (porsLeafInput idx j v)
    simp [porsLeafInput, thInput, tweak, byte_toNat] at h ⊢
    omega

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
