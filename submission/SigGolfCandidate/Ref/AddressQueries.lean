import SigGolfCandidate.Ref.Lemmas
import SigGolfCandidate.Ref.AddressWords

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
    (h1 : (x.getD 0 0).toNat + 256 * (x.getD 1 0).toNat ≠ 257) :
    addrFmt x = fmt x := by
  apply AddressFormat.queryPerm_fixed
  · have h := (fmt_low_bytes x).1
    omega
  · have h := fmt_low_bytes x
    omega

theorem addrFmt_eq_th (t lay tau p j : Nat) (payload : List Byte)
    (ht : t % 256 ≠ 1) :
    addrFmt (thInput (tweak t lay tau p j) payload) =
      fmt (thInput (tweak t lay tau p j) payload) := by
  apply addrFmt_eq_of_prefix
  · simp [thInput, tweak, byte_toNat]
  · simp [thInput, tweak, byte_toNat]
    omega

theorem addrFmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 12]) :
    addrFmt (thInput (tweak t lay tau p j) payload) =
      pad64 (thInput (tweak t lay tau p j) payload) := by
  have h1 : t % 256 ≠ 1 := by
    intro h
    apply ht
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    left
    apply BitVec.eq_of_toNat_eq
    simpa [byte_toNat] using h
  rw [addrFmt_eq_th _ _ _ _ _ _ h1, fmt_thInput _ _ _ _ _ _ ht]

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
    addrFmt (porsLeafInput idx j v) = fmt (porsLeafInput idx j v) := by
  unfold porsLeafInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

@[simp] theorem addrFmt_porsNodeInput (idx H : Nat) (l r : Val) :
    addrFmt (porsNodeInput idx H l r) = fmt (porsNodeInput idx H l r) := by
  unfold porsNodeInput
  exact addrFmt_eq_th _ _ _ _ _ _ (by decide)

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
