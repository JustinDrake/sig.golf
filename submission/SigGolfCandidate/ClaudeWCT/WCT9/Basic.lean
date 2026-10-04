import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.T3.Proofs

namespace ClaudeWCT.WCT9
open OracleComp OracleSpec SigGolfCandidate.T3
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem wctHeader_eq_header (tag lay tree position index : Nat) (h : ¬ packedNodeTag tag) :
    wctHeader tag lay tree position index = header tag lay tree position index := by
  unfold wctHeader header
  rw [if_neg h]
  simp only [Nat.add_assoc]
theorem node_header_plain (coord index heap : Nat) :
    header 11 coord index 0 heap = wctHeader 11 coord index 0 heap :=
  (wctHeader_eq_header 11 coord index 0 heap (by decide)).symm
theorem forest_header_plain (index : Nat) :
    header 15 0 index 0 0 = wctHeader 15 0 index 0 0 :=
  (wctHeader_eq_header 15 0 index 0 0 (by decide)).symm
theorem wct_tags_plain : ¬ packedNodeTag 5 ∧ ¬ packedNodeTag 6 ∧
    ¬ packedNodeTag 11 ∧ ¬ packedNodeTag 15 := by decide
theorem chain_header_eq (coord index position selected : Nat) :
    wctHeader 5 coord index position selected = header 5 coord index position selected :=
  wctHeader_eq_header 5 coord index position selected (by decide)
theorem leaf_header_eq (coord index selected : Nat) :
    wctHeader 6 coord index 0 selected = header 6 coord index 0 selected :=
  wctHeader_eq_header 6 coord index 0 selected (by decide)
theorem chainInput_eq_header (index coord selected chain step : Nat) (value : Digest) :
    chainInput index coord selected chain step value =
      zero16 ++ bytesLE 16 (header 5 coord index (step + 256 * chain) selected) ++
        zero16 ++ bytesLE 16 value := by
  rw [chainInput, chain_header_eq]
theorem radix_inj {B a a' m m' : Nat} (h : a + B * m = a' + B * m') (ha : a < B) (ha' : a' < B) :
    a = a' ∧ m = m' := by
  have hB : 0 < B := by omega
  have h1 := congrArg (· % B) h
  have h2 := congrArg (· / B) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h1
  simp only [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha, Nat.div_eq_of_lt ha',
    Nat.zero_add] at h2
  exact ⟨h1, h2⟩
def headerValue (tag lay tree position index : Nat) : Nat :=
  1 + tag % 256 * 2 ^ 8 + lay % 256 * 2 ^ 16 + (tree / 2 ^ 32 % 256) * 2 ^ 24 +
    position % 2 ^ 32 * 2 ^ 32 + tree % 2 ^ 32 * 2 ^ 64 + index % 2 ^ 32 * 2 ^ 96
theorem headerValue_nested (tag lay tree position index : Nat) :
    headerValue tag lay tree position index =
      1 + 256 * (tag % 256 + 256 * (lay % 256 + 256 * (tree / 2 ^ 32 % 256 +
        256 * (position % 2 ^ 32 + 2 ^ 32 * (tree % 2 ^ 32 + 2 ^ 32 * (index % 2 ^ 32)))))) := by
  unfold headerValue
  ring
theorem headerValue_lt (tag lay tree position index : Nat) :
    headerValue tag lay tree position index < 2 ^ 128 := by
  rw [headerValue_nested]
  have h1 := Nat.mod_lt tag (show 0 < 256 by decide)
  have h2 := Nat.mod_lt lay (show 0 < 256 by decide)
  have h3 := Nat.mod_lt (tree / 2 ^ 32) (show 0 < 256 by decide)
  have h4 := Nat.mod_lt position (show 0 < 2 ^ 32 by decide)
  have h5 := Nat.mod_lt tree (show 0 < 2 ^ 32 by decide)
  have h6 := Nat.mod_lt index (show 0 < 2 ^ 32 by decide)
  generalize tag % 256 = a1 at *
  generalize lay % 256 = a2 at *
  generalize tree / 2 ^ 32 % 256 = a3 at *
  generalize position % 2 ^ 32 = a4 at *
  generalize tree % 2 ^ 32 = a5 at *
  generalize index % 2 ^ 32 = a6 at *
  norm_num only at h1 h2 h3 h4 h5 h6 ⊢
  omega
theorem wctHeader_toNat (tag lay tree position index : Nat) :
    (wctHeader tag lay tree position index).toNat = headerValue tag lay tree position index := by
  unfold wctHeader
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (headerValue_lt _ _ _ _ _)
theorem headerValue_inj {tag lay tree position index tag' lay' tree' position' index' : Nat}
    (h : headerValue tag lay tree position index = headerValue tag' lay' tree' position' index') :
    tag % 256 = tag' % 256 ∧ lay % 256 = lay' % 256 ∧ tree / 2 ^ 32 % 256 = tree' / 2 ^ 32 % 256 ∧
      position % 2 ^ 32 = position' % 2 ^ 32 ∧ tree % 2 ^ 32 = tree' % 2 ^ 32 ∧
      index % 2 ^ 32 = index' % 2 ^ 32 := by
  rw [headerValue_nested, headerValue_nested] at h
  have h0 := Nat.add_left_cancel h
  obtain ⟨e1, h1⟩ := radix_inj (Nat.eq_of_mul_eq_mul_left (by decide) h0)
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e2, h2⟩ := radix_inj h1 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e3, h3⟩ := radix_inj h2 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e4, h4⟩ := radix_inj h3 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  obtain ⟨e5, h5⟩ := radix_inj h4 (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  exact ⟨e1, e2, e3, e4, e5, h5⟩
theorem tree_of_split {tree tree' : Nat} (ht : tree < 2 ^ 40) (ht' : tree' < 2 ^ 40)
    (hhi : tree / 2 ^ 32 % 256 = tree' / 2 ^ 32 % 256) (hlo : tree % 2 ^ 32 = tree' % 2 ^ 32) :
    tree = tree' := by
  have hq : tree / 2 ^ 32 < 256 := Nat.div_lt_of_lt_mul (by norm_num at ht ⊢; omega)
  have hq' : tree' / 2 ^ 32 < 256 := Nat.div_lt_of_lt_mul (by norm_num at ht' ⊢; omega)
  rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq'] at hhi
  rw [← Nat.div_add_mod tree (2 ^ 32), ← Nat.div_add_mod tree' (2 ^ 32), hhi, hlo]
theorem wctHeader_inj {tag lay tree position index tag' lay' tree' position' index' : Nat}
    (ht : tag < 256) (hl : lay < 256) (htr : tree < 2 ^ 40) (hp : position < 2 ^ 32)
    (hi : index < 2 ^ 32) (ht' : tag' < 256) (hl' : lay' < 256) (htr' : tree' < 2 ^ 40)
    (hp' : position' < 2 ^ 32) (hi' : index' < 2 ^ 32)
    (h : wctHeader tag lay tree position index = wctHeader tag' lay' tree' position' index') :
    tag = tag' ∧ lay = lay' ∧ tree = tree' ∧ position = position' ∧ index = index' := by
  have hn := congrArg BitVec.toNat h
  rw [wctHeader_toNat, wctHeader_toNat] at hn
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := headerValue_inj hn
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at e1
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at e2
  rw [Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hp'] at e4
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at e6
  exact ⟨e1, e2, tree_of_split htr htr' e3 e5, e4, e6⟩
theorem chainHeader_inj {coord index chain step selected coord' index' chain' step' selected' : Nat}
    (hc : coord < 256) (hi : index < 2 ^ 31) (hch : chain < 7) (hs : step < 3) (hj : selected < 128)
    (hc' : coord' < 256) (hi' : index' < 2 ^ 31) (hch' : chain' < 7) (hs' : step' < 3)
    (hj' : selected' < 128)
    (h : wctHeader 5 coord index (step + 256 * chain) selected =
      wctHeader 5 coord' index' (step' + 256 * chain') selected') :
    coord = coord' ∧ index = index' ∧ chain = chain' ∧ step = step' ∧ selected = selected' := by
  have hpow : (2 : Nat) ^ 31 < 2 ^ 40 := by decide
  obtain ⟨_, e2, e3, e4, e5⟩ := wctHeader_inj (by decide) hc (by omega)
    (by norm_num; omega) (by norm_num; omega) (by decide) hc' (by omega)
    (by norm_num; omega) (by norm_num; omega) h
  exact ⟨e2, e3, by omega, by omega, e5⟩
theorem serializeOpening_length (opened : Opening) : (serializeOpening opened).length = 224 := by
  simp only [serializeOpening, List.length_append, digest_list_bytes_length, List.length_ofFn]
theorem serialize_length (sig : Signature) : (serialize sig).length = 5456 := by
  simp only [serialize, List.length_append, bytesLE_length, List.length_flatMap,
    List.map_ofFn, Function.comp_def, List.length_flatten]
  simp_rw [serializeOpening_length, serializeLayer_length]
  decide
theorem serializeOpening_injective : Function.Injective serializeOpening := by
  rintro ⟨lv, lp⟩ ⟨rv, rp⟩ h
  simp only [serializeOpening] at h
  obtain ⟨hv, hp⟩ := List.append_inj h (by simp only [digest_list_bytes_length, List.length_ofFn])
  have hv := SphincsSecurity.flatMap_bytesLE_ofFn_injective hv
  have hp := SphincsSecurity.flatMap_bytesLE_ofFn_injective hp
  subst rv rp
  rfl
theorem serialize_injective : Function.Injective serialize := by
  rintro ⟨lr, lo, ll⟩ ⟨rr, ro, rl⟩ h
  simp only [serialize] at h
  have hopen (o : Coord → Opening) :
      ((List.ofFn o).flatMap serializeOpening).length = 2016 := by
    simp only [List.length_flatMap, List.map_ofFn, Function.comp_def, serializeOpening_length]
    decide
  obtain ⟨hhead, hlayers⟩ := List.append_inj h (by
    simp only [List.length_append, bytesLE_length, hopen])
  obtain ⟨hrho, hopenings⟩ := List.append_inj hhead (by simp only [bytesLE_length])
  have hrho := bytesLE_injective hrho
  rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn] at hopenings
  have ho := SphincsSecurity.length_flatten_ofFn_eq _ _
    (fun coord => by
      simp only [Function.comp_apply, serializeOpening_length]) hopenings
  have ho' : lo = ro := funext fun coord => serializeOpening_injective (congrFun ho coord)
  have hl := SphincsSecurity.length_flatten_ofFn_eq _ _
    (fun lay => by rw [serializeLayer_length, serializeLayer_length]) hlayers
  have hl' : ll = rl := funext fun lay => serializeLayer_injective lay (congrFun hl lay)
  subst rr ro rl
  rfl
theorem child_val (output : HashOutput) (coord : Coord) :
    (child output coord).val = output.toNat / 2 ^ coordBase coord.val % 128 := rfl
theorem field_lt (output : HashOutput) (coord : Coord) : field output coord < 2 ^ 14 :=
  Nat.mod_lt _ (by decide)
theorem rank_val (output : HashOutput) (coord : Coord) :
    (rank output coord).val = field output coord % 728 := rfl
theorem admissible_iff (output : HashOutput) :
    admissible output = true ↔
      output.toNat / 2 ^ 31 % 2 ^ 12 = 0 ∧ ∀ coord : Coord, field output coord < 16016 := by
  unfold admissible field
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun coord => hf coord.val coord.isLt⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun coord hc => hf ⟨coord, hc⟩⟩
theorem admissible_field_split (output : HashOutput) (h : admissible output = true)
    (coord : Coord) :
    field output coord = (rank output coord).val + 728 * (field output coord / 728) ∧
      field output coord / 728 < 22 := by
  have hf := ((admissible_iff output).1 h).2 coord
  rw [rank_val]
  omega
theorem rank_fiber_card (r : Fin 728) :
    ((Finset.range 16016).filter (fun f => f % 728 = r.val)).card = 22 := by
  have he : (Finset.range 16016).filter (fun f => f % 728 = r.val) =
      (Finset.range 22).image (fun q => r.val + 728 * q) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    have hr := r.isLt
    constructor
    · rintro ⟨hf, hm⟩
      exact ⟨f / 728, by omega, by omega⟩
    · rintro ⟨q, hq, rfl⟩
      constructor <;> omega
  rw [he, Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_left_cancel hab))]
  simp
def acceptedFieldEquiv : Fin 16016 ≃ Fin 728 × Fin 22 where
  toFun f := (⟨f.val % 728, Nat.mod_lt _ (by decide)⟩, ⟨f.val / 728, by omega⟩)
  invFun p := ⟨p.1.val + 728 * p.2.val, by omega⟩
  left_inv f := by apply Fin.ext; simp only; omega
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext <;> simp only <;> omega
theorem acceptedFieldEquiv_rank (f : Fin 16016) :
    (acceptedFieldEquiv f).1.val = f.val % 728 := rfl
def digestLayout : List (Nat × Nat) :=
  [(0, 31), (31, 12),
   (43, 7), (50, 14), (64, 7), (71, 14), (85, 7), (92, 14), (106, 7), (113, 14), (127, 1),
   (128, 7), (135, 14), (149, 7), (156, 14), (170, 7), (177, 14), (191, 1),
   (192, 7), (199, 14), (213, 7), (220, 14), (234, 22)]
theorem coordBase_values :
    List.ofFn (fun k : Coord => coordBase k.val) = [43, 64, 85, 106, 128, 149, 170, 192, 213] := by
  decide
theorem digestLayout_tiles :
    digestLayout.map Prod.fst = ((digestLayout.map Prod.snd).scanl (· + ·) 0).dropLast ∧
      (digestLayout.map Prod.snd).sum = 256 ∧ ∀ p ∈ digestLayout, 0 < p.2 := by
  decide
theorem digestLayout_child (k : Coord) : (coordBase k.val, 7) ∈ digestLayout := by
  revert k; decide
theorem digestLayout_field (k : Coord) : (coordBase k.val + 7, 14) ∈ digestLayout := by
  revert k; decide
theorem digestLayout_disjoint :
    digestLayout.Pairwise (fun p q => p.1 + p.2 ≤ q.1) ∧
      ∀ p ∈ digestLayout, p.1 + p.2 ≤ 256 := by
  decide
theorem coordBase_word_aligned (k : Coord) :
    coordBase k.val / 64 = (coordBase k.val + 20) / 64 ∧ 43 ≤ coordBase k.val ∧
      coordBase k.val + 21 ≤ 234 := by
  revert k; decide
theorem coordBase_disjoint (k l : Coord) (h : k.val < l.val) :
    coordBase k.val + 21 ≤ coordBase l.val := by
  revert k l; decide
theorem coordinate_verify_steps (output : HashOutput) (coord : Coord) :
    (∑ t : Fin 7, (List.range' (3 - digit (rank output coord) t)
      (digit (rank output coord) t)).length) = 6 := by
  simp only [List.length_range']
  exact step_count _
theorem verify_walk_positions (word : Rank) (t : Fin 7) :
    (∀ s ∈ List.range' (3 - digit word t) (digit word t), s < 3) ∧
      3 - digit word t + digit word t = 3 := by
  have hd := digit_le_three word t
  refine ⟨fun s hs => ?_, by omega⟩
  rw [List.mem_range'] at hs
  omega
theorem verify_steps_total (output : HashOutput) :
    (∑ coord : Coord, ∑ t : Fin 7, digit (rank output coord) t) = 54 := by
  simp only [step_count, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
end ClaudeWCT.WCT9
