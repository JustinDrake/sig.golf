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

/-- The tag-10 (PORS node) class: the header field (high half of word 1) is relabelled. -/
theorem nodeRel_eq (a b R : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    nodeRel (a + 18446744073709551616 * (b + 18446744073709551616 * R)) =
      a + 18446744073709551616 * (b % 4294967296 + 4294967296 * Rev.efield (b / 4294967296) +
        18446744073709551616 * R) := by
  unfold nodeRel
  have q2 : (a + 18446744073709551616 * (b + 18446744073709551616 * R)) / 79228162514264337593543950336 %
      4294967296 = b / 4294967296 := by omega
  rw [q2]
  generalize Rev.efield (b / 4294967296) = e
  omega

theorem baseQueryPerm_node (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2561) :
    baseQueryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (w0 :: BitVec.ofNat 64 (w1.toNat % 4294967296 +
        4294967296 * Rev.efield (w1.toNat / 4294967296)) :: ws) := by
  have hR := wordsToNat_lt ws
  rw [hlen] at hR
  norm_num only [Nat.reduceMul, Nat.reducePow] at hR
  have h0 := w0.isLt
  have h1 := w1.isLt
  have he := Rev.efield_lt (w1.toNat / 4294967296)
  norm_num only [Nat.reducePow] at h0 h1 he
  have hx : w1.toNat % 4294967296 + 4294967296 * Rev.efield (w1.toNat / 4294967296) <
      18446744073709551616 := by omega
  have e1 : wordsToNat (w0 :: w1 :: ws) =
      w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws) := rfl
  have e2 : wordsToNat (w0 :: BitVec.ofNat 64 (w1.toNat % 4294967296 +
        4294967296 * Rev.efield (w1.toNat / 4294967296)) :: ws) =
      w0.toNat + 18446744073709551616 * (w1.toNat % 4294967296 +
        4294967296 * Rev.efield (w1.toNat / 4294967296) + 18446744073709551616 * wordsToNat ws) := by
    show w0.toNat + 18446744073709551616 * ((BitVec.ofNat 64 _).toNat +
      18446744073709551616 * wordsToNat ws) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have hN : w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws) < 2 ^ 512 := by
    norm_num only [Nat.reducePow]; omega
  have hcls : (w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws)) % 65536
      = 2561 := by omega
  have key : fullPerm (w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws)) =
      w0.toNat + 18446744073709551616 * (w1.toNat % 4294967296 +
        4294967296 * Rev.efield (w1.toNat / 4294967296) + 18446744073709551616 * wordsToNat ws) := by
    rw [fullPerm_of_eq _ hcls, nodeRel_eq _ _ _ h0 h1]
  simp only [queryOfWords, baseQueryPerm]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, e2, Nat.mod_eq_of_lt hN, key]

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
      queryOfWords 0 (w0 :: BitVec.ofNat 64 (w1.toNat % 4294967296 +
        4294967296 * Rev.efield (w1.toNat / 4294967296)) :: ws) := by
  rw [queryPerm, baseQueryPerm_node w0 w1 ws hlen hc]
  apply LeafScale.queryRel_fixed
  rw [queryOfWords_class, hc]
  decide

theorem queryPerm_words (w : Word) (ws : List Word) (hlen : ws.length = 7)
    (hc : w.toNat % 65536 ≠ 2561) (h9 : w.toNat % 65536 ≠ 2305) :
    queryPerm (queryOfWords 0 (w :: ws)) =
      queryOfWords 0 (BitVec.ofNat 64 (wordPerm w.toNat) :: ws) := by
  rw [queryPerm, baseQueryPerm_words w ws hlen hc]
  apply LeafScale.queryRel_fixed
  rw [queryOfWords_class, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (wordPerm_lt _ w.isLt)]
  exact wordPerm_leaf_class _ h9

theorem leafRel_eq (a b R : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) :
    LeafScale.rel (a + 18446744073709551616 * (b + 18446744073709551616 * R)) =
      a + 18446744073709551616 * (b % 4294967296 + 4294967296 * LeafScale.left3 (b / 4294967296) +
        18446744073709551616 * R) := by
  unfold LeafScale.rel
  have q2 : (a + 18446744073709551616 * (b + 18446744073709551616 * R)) / 79228162514264337593543950336 %
      4294967296 = b / 4294967296 := by omega
  rw [q2]
  generalize LeafScale.left3 (b / 4294967296) = e
  omega

theorem queryPerm_leaf (w0 w1 : Word) (ws : List Word) (hlen : ws.length = 6)
    (hc : w0.toNat % 65536 = 2305) :
    queryPerm (queryOfWords 0 (w0 :: w1 :: ws)) =
      queryOfWords 0 (w0 :: BitVec.ofNat 64 (w1.toNat % 4294967296 +
        4294967296 * LeafScale.left3 (w1.toNat / 4294967296)) :: ws) := by
  have hR := wordsToNat_lt ws
  rw [hlen] at hR
  norm_num only [Nat.reduceMul, Nat.reducePow] at hR
  have h0 := w0.isLt
  have h1 := w1.isLt
  have he := LeafScale.left3_lt (w1.toNat / 4294967296)
  norm_num only [Nat.reducePow] at h0 h1 he
  have hx : w1.toNat % 4294967296 + 4294967296 * LeafScale.left3 (w1.toNat / 4294967296) <
      18446744073709551616 := by omega
  have e1 : wordsToNat (w0 :: w1 :: ws) =
      w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws) := rfl
  have e2 : wordsToNat (w0 :: BitVec.ofNat 64 (w1.toNat % 4294967296 +
        4294967296 * LeafScale.left3 (w1.toNat / 4294967296)) :: ws) =
      w0.toNat + 18446744073709551616 * (w1.toNat % 4294967296 +
        4294967296 * LeafScale.left3 (w1.toNat / 4294967296) + 18446744073709551616 * wordsToNat ws) := by
    show w0.toNat + 18446744073709551616 * ((BitVec.ofNat 64 _).toNat +
      18446744073709551616 * wordsToNat ws) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  have hN : w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws) < 2 ^ 512 := by
    norm_num only [Nat.reducePow]; omega
  have hcls : (w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws)) % 65536
      = 2305 := by omega
  have key : LeafScale.rel (w0.toNat + 18446744073709551616 * (w1.toNat + 18446744073709551616 * wordsToNat ws)) =
      w0.toNat + 18446744073709551616 * (w1.toNat % 4294967296 +
        4294967296 * LeafScale.left3 (w1.toNat / 4294967296) + 18446744073709551616 * wordsToNat ws) := by
    exact leafRel_eq _ _ _ h0 h1
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
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, e1, e2, Nat.mod_eq_of_lt hN, key]

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
  unfold encInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

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
