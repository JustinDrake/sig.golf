import SigGolfCandidate.T3.Proofs

namespace SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- The source-only metadata fits eleven otherwise spare low-word bits. -/
theorem chainExtra_bound (lay : Layer) (tree leaf : Nat) :
    tree % 2^31 / 2^(32-height lay) +
      (leaf % 4096 / 2^height lay) * 2^(height lay-1) < 2048 := by
  fin_cases lay <;> norm_num [height] <;> omega

theorem chainHeaderLow_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeaderLow lay tree leaf i step).toNat =
      128 + i % 64 + step % 8 * 2^8 +
      (tree % 2^31 * 2^height lay + leaf % 4096) % 2^32 * 2^16 +
      lay.val * 2^48 + 193 * 2^56 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) % 2 * 2^6 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) / 2 % 32 * 2^11 +
      (tree % 2^31 / 2^(32-height lay) + (leaf % 4096 / 2^height lay) * 2^(height lay-1)) / 64 * 2^50 := by
  have hb := chainExtra_bound lay tree leaf
  have hl := lay.isLt
  unfold chainHeaderLow
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  omega

theorem chainHeaderSpill_bound (tree leaf i step : Nat) :
    chainHeaderSpill tree leaf i step < 2^52 := by
  unfold chainHeaderSpill
  omega

theorem chainHeaderLow_band (lay : Layer) (tree leaf i step : Nat) :
    193 * 2^56 ≤ (chainHeaderLow lay tree leaf i step).toNat ∧
      (chainHeaderLow lay tree leaf i step).toNat < 193 * 2^56 + 2^55 := by
  rw [chainHeaderLow_toNat]
  have hb := chainExtra_bound lay tree leaf
  have hl := lay.isLt
  omega

theorem chainHeaderFlaggedLow_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeaderFlaggedLow lay tree leaf i step).toNat =
      (chainHeaderLow lay tree leaf i step).toNat +
        (if chainHeaderSpill tree leaf i step = 0 then 0 else 1) * 2^55 := by
  have hb := chainHeaderLow_band lay tree leaf i step
  unfold chainHeaderFlaggedLow
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  split_ifs <;> omega

private theorem flaggedLow_base_eq (a b : BitVec 64) (f g : Nat)
    (ha : 193 * 2^56 ≤ a.toNat ∧ a.toNat < 193 * 2^56 + 2^55)
    (hb : 193 * 2^56 ≤ b.toNat ∧ b.toNat < 193 * 2^56 + 2^55)
    (hf : f ≤ 1) (hg : g ≤ 1)
    (he : a.toNat + f * 2^55 = b.toNat + g * 2^55) : a = b := by
  apply BitVec.eq_of_toNat_eq
  omega

theorem chainHeaderFlaggedLow_base {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeaderFlaggedLow lay tree leaf i step = chainHeaderFlaggedLow lay' tree' leaf' i' step') :
    chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' := by
  have he := congrArg BitVec.toNat h
  rw [chainHeaderFlaggedLow_toNat, chainHeaderFlaggedLow_toNat] at he
  exact flaggedLow_base_eq _ _ _ _ (chainHeaderLow_band lay tree leaf i step)
    (chainHeaderLow_band lay' tree' leaf' i' step')
    (by split_ifs <;> omega) (by split_ifs <;> omega) he

theorem chainHeader_toNat (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).toNat =
      chainHeaderSpill tree leaf i step * 2^64 + (chainHeaderFlaggedLow lay tree leaf i step).toNat := by
  have hb := chainHeaderSpill_bound tree leaf i step
  unfold chainHeader
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (chainHeaderFlaggedLow lay tree leaf i step).isLt,
    Nat.shiftLeft_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show chainHeaderSpill tree leaf i step < 2^64 by omega)]

theorem chainHeader_low (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 = chainHeaderFlaggedLow lay tree leaf i step := by
  exact BitVec.extractLsb'_append_eq_right

theorem chainHeaderSpill_zero (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    chainHeaderSpill tree leaf i step = 0 := by
  unfold chainHeaderSpill
  omega

theorem chainHeader_offgraph_bit (lay : Layer) (tree leaf i step : Nat) :
    ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat / 2^55 % 2 =
      if chainHeaderSpill tree leaf i step = 0 then 0 else 1 := by
  rw [chainHeader_low, chainHeaderFlaggedLow_toNat]
  have hb := chainHeaderLow_band lay tree leaf i step
  split_ifs <;> omega

theorem chainHeader_graph_bit (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    ((chainHeader lay tree leaf i step).extractLsb' 0 64).toNat / 2^55 % 2 = 0 := by
  rw [chainHeader_offgraph_bit, chainHeaderSpill_zero tree leaf i step ht hl hi hs, if_pos rfl]

theorem chainHeader_offgraph_low_ne {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hoff : chainHeaderSpill tree leaf i step ≠ 0)
    (ht : tree' < 2^31) (hl : leaf' < 4096) (hi : i' < 64) (hs : step' < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 0 64 ≠
      (chainHeader lay' tree' leaf' i' step').extractLsb' 0 64 := by
  intro he
  have hbit := chainHeader_offgraph_bit lay tree leaf i step
  rw [he, chainHeader_graph_bit lay' tree' leaf' i' step' ht hl hi hs, if_neg hoff] at hbit
  contradiction

/-- Low-word projections recover the entire original graph coordinates. -/
theorem chainHeaderLow_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step') :
    lay = lay' ∧ tree % 2^31 = tree' % 2^31 ∧ leaf % 4096 = leaf' % 4096 ∧
      i % 64 = i' % 64 ∧ step % 8 = step' % 8 := by
  have he := congrArg BitVec.toNat h
  rw [chainHeaderLow_toNat, chainHeaderLow_toNat] at he
  have hl := lay.isLt
  have hl' := lay'.isLt
  have hb := chainExtra_bound lay tree leaf
  have hb' := chainExtra_bound lay' tree' leaf'
  generalize hx : (tree % 2^31 / 2^(32-height lay) +
    (leaf % 4096 / 2^height lay) * 2^(height lay-1)) = extra at he hb
  generalize hx' : (tree' % 2^31 / 2^(32-height lay') +
    (leaf' % 4096 / 2^height lay') * 2^(height lay'-1)) = extra' at he hb'
  have hparts : lay.val = lay'.val ∧ i % 64 = i' % 64 ∧ step % 8 = step' % 8 ∧
      (tree % 2^31 * 2^height lay + leaf % 4096) % 2^32 =
        (tree' % 2^31 * 2^height lay' + leaf' % 4096) % 2^32 ∧ extra = extra' := by omega
  have heq := Fin.ext hparts.1
  subst lay'
  have hmeta := hx.trans (hparts.2.2.2.2.trans hx'.symm)
  have hquot : tree % 2^31 / 2^(32-height lay) = tree' % 2^31 / 2^(32-height lay) ∧
      leaf % 4096 / 2^height lay = leaf' % 4096 / 2^height lay := by
    fin_cases lay <;> norm_num [height] at hmeta ⊢ <;> omega
  have hrem : leaf % 4096 % 2^height lay = leaf' % 4096 % 2^height lay := by
    have hm := congrArg (fun n => n % 2^height lay) hparts.2.2.2.1
    fin_cases lay <;> norm_num [height, Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd] at hm ⊢ <;> omega
  refine ⟨rfl, ?_⟩
  clear he hx hx'
  fin_cases lay <;> norm_num [height] at hparts hquot hrem ⊢ <;> omega

theorem chainHeaderLow_congr {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^31 = tree' % 2^31)
    (hf : leaf % 4096 = leaf' % 4096) (hi : i % 64 = i' % 64)
    (hs : step % 8 = step' % 8) :
    chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' := by
  simp only [chainHeaderLow, hl, ht, hf, hi, hs]

/-- Full headers preserve the original generic modulo alias domains. -/
theorem chainHeader_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (h : chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step') :
    lay = lay' ∧ tree % 2^40 = tree' % 2^40 ∧ leaf % 2^32 = leaf' % 2^32 ∧
      i % 2^24 = i' % 2^24 ∧ step % 256 = step' % 256 := by
  have hlo := congrArg (fun b : BitVec 128 => b.extractLsb' 0 64) h
  simp only [chainHeader_low] at hlo
  obtain ⟨hlay, ht, hf, hi, hs⟩ := chainHeaderLow_fields (chainHeaderFlaggedLow_base hlo)
  have he := congrArg BitVec.toNat h
  rw [chainHeader_toNat, chainHeader_toNat, hlo] at he
  have hh : chainHeaderSpill tree leaf i step = chainHeaderSpill tree' leaf' i' step' := by omega
  unfold chainHeaderSpill at hh
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩

theorem chainHeader_congr {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^40 = tree' % 2^40)
    (hf : leaf % 2^32 = leaf' % 2^32) (hi : i % 2^24 = i' % 2^24)
    (hs : step % 256 = step' % 256) :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' := by
  have hlo : chainHeaderLow lay tree leaf i step = chainHeaderLow lay' tree' leaf' i' step' :=
    chainHeaderLow_congr hl (by omega) (by omega) (by omega) (by omega)
  simp only [chainHeader, chainHeaderFlaggedLow, chainHeaderSpill, ht, hf, hi, hs, hlo]

/-- Mixed-radix routing is injective on the full SourceLeaf superset, not
merely the smaller population visited by a routed 31-bit index. -/
theorem packedRoute_injective {lay : Layer} {tree leaf tree' leaf' : Nat}
    (hl : leaf < 2^height lay) (hl' : leaf' < 2^height lay)
    (h : tree * 2^height lay + leaf = tree' * 2^height lay + leaf') :
    tree = tree' ∧ leaf = leaf' := by
  have he : leaf + 2^height lay * tree = leaf' + 2^height lay * tree' := by
    simpa only [Nat.mul_comm, Nat.add_comm] using h
  obtain ⟨hleaf, htree⟩ := pack_nat_injective hl hl' he
  exact ⟨htree, hleaf⟩

theorem packedRoute_bound {lay : Layer} {tree leaf : Nat}
    (ht : tree < 2^31) (hl : leaf < 2^height lay) :
    tree * 2^height lay + leaf < 2^43 := by
  fin_cases lay <;> norm_num [height] at hl ⊢ <;> omega

theorem chainHeader_low_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8)
    (ht' : tree' < 2^31) (hl' : leaf' < 4096) (hi' : i' < 64) (hs' : step' < 8)
    (h : (chainHeader lay tree leaf i step).extractLsb' 0 64 =
      (chainHeader lay' tree' leaf' i' step').extractLsb' 0 64) :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' := by
  simp only [chainHeader_low] at h
  obtain ⟨hlay, htree, hleaf, hindex, hstep⟩ := chainHeaderLow_fields (chainHeaderFlaggedLow_base h)
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩

theorem chainHeader_injective {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (ht : tree < 2^40) (hl : leaf < 2^32) (hi : i < 2^24) (hs : step < 256)
    (ht' : tree' < 2^40) (hl' : leaf' < 2^32) (hi' : i' < 2^24) (hs' : step' < 256)
    (h : chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step') :
    lay = lay' ∧ tree = tree' ∧ leaf = leaf' ∧ i = i' ∧ step = step' := by
  obtain ⟨hlay, htree, hleaf, hindex, hstep⟩ := chainHeader_fields h
  exact ⟨hlay, by omega, by omega, by omega, by omega⟩

/-- Byte 23 is the chain-domain marker, independently of every coordinate. -/
theorem chainHeader_marker (lay : Layer) (tree leaf i step : Nat) :
    (chainHeader lay tree leaf i step).toNat / 2^56 % 256 = 193 := by
  have hdiv : (chainHeaderLow lay tree leaf i step).toNat / 2^56 = 193 := by
    rw [chainHeaderLow_toNat]
    have := lay.isLt
    have hb := chainExtra_bound lay tree leaf
    generalize (tree % 2^31 / 2^(32-height lay) +
      (leaf % 4096 / 2^height lay) * 2^(height lay-1)) = extra at hb ⊢
    omega
  have hb := chainHeaderLow_band lay tree leaf i step
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat]
  split_ifs <;> omega

/-- Existing role headers with bounded position and tree have a marker byte
strictly below 128, whether their node word is reversed or not. -/
theorem header_marker_lt (tag lay tree position index : Nat)
    (ht : tree < 2^31) (hp : position < 2^31) :
    (header tag lay tree position index).toNat / 2^56 % 256 < 128 := by
  have hlow : (header tag lay tree position index).toNat % 2^64 < 2^63 := by
    have htt : tree < 2^32 := by omega
    have hpp : position < 2^32 := by omega
    have hh : tree / 2^32 = 0 := Nat.div_eq_of_lt htt
    let low := 1 + tag % 256 * 2^8 + lay % 256 * 2^16
    have heq : (header tag lay tree position index).toNat =
        if packedNodeTag tag then
          (low + tree * 2^32) + nodeWord tag position index * 2^64
        else (low + position * 2^32) + (tree + index % 2^32 * 2^32) * 2^64 := by
      rw [header_toNat]
      simp only [hh, Nat.zero_mod, Nat.zero_mul, Nat.add_zero,
        Nat.mod_eq_of_lt htt, Nat.mod_eq_of_lt hpp]
      split_ifs <;> dsimp [low] <;> ring
    rw [heq]
    split_ifs <;> rw [Nat.add_mul_mod_self_right]
    all_goals
      apply lt_of_le_of_lt (Nat.mod_le _ _)
      dsimp [low]
      omega
  have he : (header tag lay tree position index).toNat / 2^56 % 256 =
      ((header tag lay tree position index).toNat % 2^64) / 2^56 := by
    rw [show (2 : Nat)^64 = 2^56 * 256 by decide, Nat.mod_mul_right_div_self]
  rw [he]
  omega

theorem chainHeader_ne_header_bounded (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat)
    (ht : roleTree < 2^31) (hp : position < 2^31) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_marker lay tree leaf i step
  have hr := header_marker_lt tag roleLay roleTree position index ht hp
  rw [h] at hc
  omega

theorem chainHeader_firstByte (lay : Layer) (tree leaf i step : Nat) :
    128 ≤ (chainHeader lay tree leaf i step).toNat % 256 := by
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat, chainHeaderLow_toNat]
  split_ifs <;> omega

theorem header_firstByte (tag lay tree position index : Nat) :
    (header tag lay tree position index).toNat % 256 = 1 := by
  rw [header_toNat]
  split_ifs <;> omega

theorem bytesLE16_first_toNat (h : BitVec 128) :
    ((bytesLE 16 h).getD 0 0).toNat = h.toNat % 256 := by
  change (h.extractLsb' 0 8).toNat = _
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- The discriminator bit separates chain inputs from every other role,
including non-reachable source helper coordinates, without bounds. -/
theorem chainHeader_ne_header (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_firstByte lay tree leaf i step
  rw [h, header_firstByte] at hc
  omega

/-- Unpacked roles use position, not tree, in the marker-bearing word. -/
theorem header_marker_lt_nonpacked (tag lay tree position index : Nat)
    (hn : packedNodeTag tag = false) (hp : position < 2^31) :
    (header tag lay tree position index).toNat / 2^56 % 256 < 128 := by
  have hpp : position < 2^32 := by omega
  let low := 1 + tag % 256 * 2^8 + lay % 256 * 2^16 + (tree / 2^32 % 256) * 2^24
  have heq : (header tag lay tree position index).toNat =
      (low + position * 2^32) + (tree % 2^32 + index % 2^32 * 2^32) * 2^64 := by
    rw [header_toNat]
    simp only [hn, Bool.false_eq_true, if_false, Nat.mod_eq_of_lt hpp]
    dsimp [low]
    ring
  have hb : (header tag lay tree position index).toNat % 2^64 < 2^63 := by
    rw [heq, Nat.add_mul_mod_self_right]
    apply lt_of_le_of_lt (Nat.mod_le _ _)
    dsimp [low]
    omega
  have he : (header tag lay tree position index).toNat / 2^56 % 256 =
      ((header tag lay tree position index).toNat % 2^64) / 2^56 := by
    rw [show (2 : Nat)^64 = 2^56 * 256 by decide, Nat.mod_mul_right_div_self]
  rw [he]
  omega

theorem chainHeader_ne_nonpacked (lay : Layer) (tree leaf i step tag roleLay roleTree position index : Nat)
    (hn : packedNodeTag tag = false) (hp : position < 2^31) :
    chainHeader lay tree leaf i step ≠ header tag roleLay roleTree position index := by
  intro h
  have hc := chainHeader_marker lay tree leaf i step
  have hr := header_marker_lt_nonpacked tag roleLay roleTree position index hn hp
  rw [h] at hc
  omega

theorem chainHeader_congr_old {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    (hl : lay = lay') (ht : tree % 2^40 = tree' % 2^40)
    (hf : leaf % 2^32 = leaf' % 2^32) (hi : i % 2^24 = i' % 2^24)
    (hs : step % 256 = step' % 256) :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' := by
  exact chainHeader_congr hl ht hf hi hs

/-- On actual routed inputs all source-only metadata vanishes. -/
theorem chainHeader_actual (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2^height lay + leaf < 2^31) (hf : leaf < 2^height lay)
    (hi : i < 64) (hs : step < 8) :
    chainHeader lay tree leaf i step = BitVec.ofNat 128
      (128 + i + step * 2^8 + (tree * 2^height lay + leaf) * 2^16 + lay.val * 2^48 + 193 * 2^56) := by
  apply BitVec.eq_of_toNat_eq
  have hz : chainHeaderSpill tree leaf i step = 0 := by
    unfold chainHeaderSpill
    fin_cases lay <;> norm_num [height] at hr hf ⊢ <;> omega
  rw [chainHeader_toNat, chainHeaderFlaggedLow_toNat, hz, if_pos rfl,
    chainHeaderLow_toNat, BitVec.toNat_ofNat]
  fin_cases lay <;> norm_num [height] at hr hf ⊢ <;> omega

/-- Every source graph header fits the low word; witness high padding remains
arbitrary until full-input equality forces it to this canonical value. -/
theorem chainHeader_high_zero (lay : Layer) (tree leaf i step : Nat)
    (ht : tree < 2^31) (hl : leaf < 4096) (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).toNat / 2^64 = 0 := by
  rw [chainHeader_toNat]
  have hb := (chainHeaderFlaggedLow lay tree leaf i step).isLt
  unfold chainHeaderSpill
  omega

theorem chainInput_padded (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    pad64 (chainInput lay tree leaf i step value) = chainInput lay tree leaf i step value := by
  simp [pad64, chainInput, bytesLE_length, zero16]

theorem chainInput_header (lay : Layer) (tree leaf i step : Nat) (value : Digest) :
    ((chainInput lay tree leaf i step value).drop 16).take 16 =
      bytesLE 16 (chainHeader lay tree leaf i step) := by
  simp [chainInput, zero16, List.append_assoc, bytesLE_length]

/-- Full-input equality keeps the entire header, including canonical high zero. -/
theorem chainInput_fields {lay lay' : Layer} {tree leaf i step tree' leaf' i' step' : Nat}
    {value value' : Digest}
    (h : chainInput lay tree leaf i step value = chainInput lay' tree' leaf' i' step' value') :
    chainHeader lay tree leaf i step = chainHeader lay' tree' leaf' i' step' ∧ value = value' := by
  unfold chainInput at h
  obtain ⟨hp, hv⟩ := List.append_inj h (by simp [List.length_append, zero16, bytesLE_length])
  have hh : bytesLE 16 (chainHeader lay tree leaf i step) =
      bytesLE 16 (chainHeader lay' tree' leaf' i' step') := by simpa using hp
  exact ⟨bytesLE_injective hh, bytesLE_injective hv⟩

end SigGolfCandidate.T3
