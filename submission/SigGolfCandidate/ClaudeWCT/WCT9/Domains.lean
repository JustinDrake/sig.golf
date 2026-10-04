import SigGolfCandidate.ClaudeWCT.WCT9.Basic
import SigGolfCandidate.T3.PackedChain

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
theorem header_byte1 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 8 % 256 = tag % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem header_byte2 (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat / 2 ^ 16 % 256 = lay % 256 := by
  rw [header_toNat]
  have := Nat.mod_lt tag (show 0 < 256 by decide)
  have := Nat.mod_lt lay (show 0 < 256 by decide)
  split <;> omega
theorem ftsChainHeaderP_firstByte (index coord selected chain step : Nat) (high : BitVec 64) :
    (ftsChainHeaderP index coord selected chain step high).toNat % 256 = 128 + 4 * (chain % 8) := by
  rw [ftsChainHeaderP_toNat, ← ftsChainLow_byte0 index coord selected chain step]
  omega
theorem ftsChainHeaderP_ne_header (index coord selected chain step : Nat) (high : BitVec 64)
    (tag lay tree position idx : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ header tag lay tree position idx := by
  intro h
  have hc := ftsChainHeaderP_firstByte index coord selected chain step high
  rw [h, header_firstByte] at hc
  omega
theorem chainHeader_low_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2 ^ 56 ≤ ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat ∧
      ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat < 194 * 2 ^ 56 := by
  rw [chainHeader_low, chainHeaderFlaggedLow_toNat]
  have hb := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega
theorem ftsChainHeaderP_low_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    (ftsChainHeaderP index coord selected chain step high).extractLsb' 0 64 ≠
      (chainHeader lay tree leaf i st).extractLsb' 0 64 := by
  intro h
  have hw := chainHeader_low_band lay tree leaf i st
  rw [← h, ftsChainHeaderP_low, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_trans (ftsChainLow_lt ..) (by decide))] at hw
  have := ftsChainLow_lt index coord selected chain step
  omega
theorem ftsChainHeaderP_ne_chainHeader (index coord selected chain step : Nat) (high : BitVec 64)
    (lay : Layer) (tree leaf i st : Nat) :
    ftsChainHeaderP index coord selected chain step high ≠ chainHeader lay tree leaf i st := fun h =>
  ftsChainHeaderP_low_ne_chainHeader index coord selected chain step high lay tree leaf i st
    (congrArg (fun x : BitVec 128 => x.extractLsb' 0 64) h)
theorem wctNodeHeader_ne_node (coord index heap : Nat) (lay : Layer) (tree heap' : Nat) (hk : coord < 252) :
    wctNodeHeader coord index heap ≠ header 3 lay.val tree 0 heap' := by
  intro h
  have h2 := header_byte2 3 (nodeLayer coord) index 0 heap
  unfold wctNodeHeader at h
  rw [h, header_byte2] at h2
  have := lay.isLt
  unfold nodeLayer at h2
  omega
theorem wctNodeHeader_ne_tag (coord index heap tag lay tree position idx : Nat) (ht : tag % 256 ≠ 3) :
    wctNodeHeader coord index heap ≠ header tag lay tree position idx := by
  intro h
  have h1 := header_byte1 3 (nodeLayer coord) index 0 heap
  unfold wctNodeHeader at h
  rw [h, header_byte1] at h1
  omega
theorem wctNodeHeader_ne_chainHeader (coord index heap : Nat) (lay : Layer) (tree leaf i st : Nat) :
    wctNodeHeader coord index heap ≠ chainHeader lay tree leaf i st := fun h =>
  chainHeader_ne_header lay tree leaf i st 3 (nodeLayer coord) index 0 heap h.symm
theorem wctNodeHeader_ne_ftsChainHeaderP (coord index heap : Nat) (i k j t s : Nat) (high : BitVec 64) :
    wctNodeHeader coord index heap ≠ ftsChainHeaderP i k j t s high := fun h =>
  ftsChainHeaderP_ne_header i k j t s high 3 (nodeLayer coord) index 0 heap h.symm
theorem pairs_bytes_length (pairs : List (Digest × Digest)) :
    (pairs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2)).length = 32 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons p ps ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring
theorem pairs_bytes_injective : ∀ {ps qs : List (Digest × Digest)}, ps.length = qs.length →
    ps.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) = qs.flatMap (fun p => bytesLE 16 p.1 ++ bytesLE 16 p.2) →
      ps = qs
  | [], [], _, _ => rfl
  | p :: ps, q :: qs, hl, h => by
      simp only [List.flatMap_cons] at h
      obtain ⟨hpq, hrest⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
      obtain ⟨h1, h2⟩ := List.append_inj hpq (by simp only [bytesLE_length])
      rw [show p = q from Prod.ext (bytesLE_injective h1) (bytesLE_injective h2),
        pairs_bytes_injective (by simpa using hl) hrest]
theorem forestInput_length (index : Nat) (pairs : List (Digest × Digest)) (h : pairs.length = 9) :
    (forestInput index pairs).length = 320 := by
  simp only [forestInput, zero16, List.length_append, List.length_replicate, bytesLE_length, pairs_bytes_length, h]
theorem forestInput_injective {index index' : Nat} {pairs pairs' : List (Digest × Digest)}
    (hi : index < 2 ^ 40) (hi' : index' < 2 ^ 40) (hl : pairs.length = pairs'.length)
    (h : forestInput index pairs = forestInput index' pairs') : index = index' ∧ pairs = pairs' := by
  unfold forestInput at h
  obtain ⟨hh, hp⟩ := List.append_inj h (by simp only [zero16, List.length_append, List.length_replicate,
    bytesLE_length])
  obtain ⟨-, hh⟩ := List.append_inj hh (by simp only [zero16, List.length_replicate])
  obtain ⟨-, -, e, -, -⟩ := header_injective (by decide) (by decide) hi (by norm_num) (by norm_num)
    (by decide) (by decide) hi' (by norm_num) (by norm_num) (bytesLE_injective hh)
  exact ⟨e, pairs_bytes_injective hl hp⟩
theorem pairEncodingInputP_length (up : Layer) (tree leaf : Nat) (left right : Digest) (counter : BitVec 32)
    (pad : BitVec 96) : (pairEncodingInputP up tree leaf left right counter pad).length = 64 := by
  simp only [pairEncodingInputP, List.length_append, bytesLE_length]
theorem pairEncodingInputP_injective {up up' : Layer} {tree leaf tree' leaf' : Nat} {l r l' r' : Digest}
    {c c' : BitVec 32} {pad pad' : BitVec 96}
    (ht : tree < 2 ^ 40) (hl : leaf < 2 ^ 32) (ht' : tree' < 2 ^ 40) (hl' : leaf' < 2 ^ 32)
    (h : pairEncodingInputP up tree leaf l r c pad = pairEncodingInputP up' tree' leaf' l' r' c' pad') :
    up = up' ∧ tree = tree' ∧ leaf = leaf' ∧ l = l' ∧ r = r' ∧ c = c' ∧ pad = pad' := by
  unfold pairEncodingInputP at h
  obtain ⟨h, hr⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hp⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h, hc⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨hL, hh⟩ := List.append_inj h (by simp only [bytesLE_length])
  have hu := up.isLt
  have hu' := up'.isLt
  obtain ⟨-, e1, e2, -, e3⟩ := header_injective (by decide) (by omega) ht (by norm_num) hl
    (by decide) (by omega) ht' (by norm_num) hl' (bytesLE_injective hh)
  exact ⟨Fin.ext e1, e2, e3, bytesLE_injective hL, bytesLE_injective hr, bytesLE_injective hc,
    bytesLE_injective hp⟩
theorem pairEncoding_separation (up : Layer) (tree leaf : Nat) :
    (∀ (lay : Layer) (tree' leaf' i st : Nat), header 4 up.val tree 0 leaf ≠ chainHeader lay tree' leaf' i st) ∧
    (∀ (i k j t s : Nat) (high : BitVec 64), header 4 up.val tree 0 leaf ≠ ftsChainHeaderP i k j t s high) ∧
    (∀ (tag lay tree' position idx : Nat), tag % 256 ≠ 4 →
      header 4 up.val tree 0 leaf ≠ header tag lay tree' position idx) ∧
    (up.val < 3 → ∀ tree' leaf' : Nat, header 4 up.val tree 0 leaf ≠ header 4 3 tree' 0 leaf') := by
  refine ⟨fun lay tree' leaf' i st h => chainHeader_ne_header lay tree' leaf' i st _ _ _ _ _ h.symm,
    fun i k j t s high h => ftsChainHeaderP_ne_header i k j t s high _ _ _ _ _ h.symm,
    fun tag lay tree' position idx ht h => ?_, fun hup tree' leaf' h => ?_⟩
  · have h1 := header_byte1 4 up.val tree 0 leaf
    rw [h, header_byte1] at h1
    omega
  · have h2 := header_byte2 4 up.val tree 0 leaf
    rw [h, header_byte2] at h2
    omega
end ClaudeWCT.WCT9
