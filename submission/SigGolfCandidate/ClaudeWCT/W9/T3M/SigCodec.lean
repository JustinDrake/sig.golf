import SigGolfCandidate.T3M.SigCodec
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.T3
open SigGolfCandidate.T3M (digNat digNat_lt digNat_digit digNat_eq_of_digits getD_append_left' getD_append_right'
  getD_ofFn' ofFn_four chainCount_0 chainCount_1 chainCount_2 chainCount_3 height_0 height_1 height_2 height_3)
open SphincsSecurity (bytesLE bytesLE_length)
def openingList (op : WCT9.Opening) : List Digest := List.ofFn op.values ++ List.ofFn op.path
def layerList (s : WCT9.Signature) (lay : Layer) : List Digest :=
  List.ofFn (s.layers lay).values ++ List.ofFn (s.layers lay).path
def sigDigests (s : WCT9.Signature) : List Digest :=
  [s.rho] ++ (List.ofFn s.openings).flatMap openingList ++
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3)))
theorem serializeOpening_eq (op : WCT9.Opening) :
    WCT9.serializeOpening op = (openingList op).flatMap (bytesLE 16) := by
  unfold WCT9.serializeOpening openingList
  rw [List.flatMap_append]
theorem serialize_eq (s : WCT9.Signature) : WCT9.serialize s = (sigDigests s).flatMap (bytesLE 16) := by
  unfold WCT9.serialize sigDigests
  rw [ofFn_four]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatten_cons,
    List.flatten_nil, layerList, serializeLayer, List.flatMap_assoc, ← serializeOpening_eq]
theorem length_openingList (op : WCT9.Opening) : (openingList op).length = 14 := by
  simp [openingList]
theorem length_layerList (s : WCT9.Signature) (lay : Layer) :
    (layerList s lay).length = chainCount lay + height lay := by
  simp only [layerList, List.length_append, List.length_ofFn]
theorem length_openings (s : WCT9.Signature) :
    ((List.ofFn s.openings).flatMap openingList).length = 126 := by
  rw [List.length_flatMap]
  simp only [List.map_ofFn, Function.comp_def, length_openingList]
  rfl
theorem length_sigDigests (s : WCT9.Signature) : (sigDigests s).length = 341 := by
  simp only [sigDigests, List.length_append, List.length_singleton, length_openings, length_layerList]
  rfl
def layIdx (lay : Layer) : Nat := (![127, 193, 243, 292] : Layer → Nat) lay
section getD
theorem getD_flatMap_chunks {α β : Type} (f : α → List β) (n : Nat) (d : β) (hf : ∀ a, (f a).length = n) :
    ∀ (L : List α) k i (hk : k < L.length), i < n → (L.flatMap f).getD (n * k + i) d = (f L[k]).getD i d
  | [], k, _, hk, _ => by simp at hk
  | a :: L, k, i, hk, hi => by
      have hl : (f a).length = n := hf a
      rw [List.flatMap_cons]
      rcases k with _ | k
      · simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < (f a).length by omega)]
      · simp only [List.getElem_cons_succ]
        have := getD_flatMap_chunks f n d hf L k i (by simpa using hk) hi
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_right (show (f a).length ≤ n * (k + 1) + i by rw [hl]; nlinarith),
          show n * (k + 1) + i - (f a).length = n * k + i by rw [hl]; ring_nf; omega, this]
variable (s : WCT9.Signature)
theorem sigDigests_rho : (sigDigests s).getD 0 0 = s.rho := by
  unfold sigDigests; rfl
theorem sigDigests_opening (k : WCT9.Coord) (i : Nat) (hi : i < 14) :
    (sigDigests s).getD (1 + 14 * k.val + i) 0 = (openingList (s.openings k)).getD i 0 := by
  have hk := k.isLt
  unfold sigDigests
  rw [getD_append_left' (by simp only [List.length_append, List.length_singleton, length_openings]; omega),
    getD_append_right' (by simp; omega), List.length_singleton,
    show 1 + 14 * k.val + i - 1 = 14 * k.val + i by omega,
    getD_flatMap_chunks openingList 14 0 length_openingList _ k.val i (by simp [hk]) hi, List.getElem_ofFn]
theorem sigDigests_value (k : WCT9.Coord) (t : Fin 7) :
    (sigDigests s).getD (1 + 14 * k.val + t.val) 0 = (s.openings k).values t := by
  rw [sigDigests_opening s k t.val (by omega), openingList, getD_append_left' (by simp), getD_ofFn']
theorem sigDigests_path (k : WCT9.Coord) (l : Fin 7) :
    (sigDigests s).getD (1 + 14 * k.val + 7 + l.val) 0 = (s.openings k).path l := by
  rw [show 1 + 14 * k.val + 7 + l.val = 1 + 14 * k.val + (7 + l.val) by omega,
    sigDigests_opening s k _ (by omega), openingList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']
theorem sigDigests_tail (k : Nat) (hk : 127 ≤ k) : (sigDigests s).getD k 0 =
    (layerList s 0 ++ (layerList s 1 ++ (layerList s 2 ++ layerList s 3))).getD (k - 127) 0 := by
  unfold sigDigests
  rw [getD_append_right' (by simp only [List.length_append, List.length_singleton, length_openings]; omega)]
  simp only [List.length_append, List.length_singleton, length_openings]
theorem sigDigests_layer (lay : Layer) (i : Nat) (hi : i < chainCount lay + height lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (layerList s lay).getD i 0 := by
  have l0 := length_layerList s 0
  have l1 := length_layerList s 1
  have l2 := length_layerList s 2
  rw [chainCount_0, height_0] at l0
  rw [chainCount_1, height_1] at l1
  rw [chainCount_2, height_2] at l2
  fin_cases lay
  · show (sigDigests s).getD (127 + i) 0 = (layerList s 0).getD i 0
    have hi' : i < 66 := hi
    rw [sigDigests_tail s _ (by omega), show 127 + i - 127 = i by omega, getD_append_left' (by omega)]
  · show (sigDigests s).getD (193 + i) 0 = (layerList s 1).getD i 0
    have hi' : i < 50 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_left' (by omega),
      show 193 + i - 127 - 66 = i by omega]
  · show (sigDigests s).getD (243 + i) 0 = (layerList s 2).getD i 0
    have hi' : i < 49 := hi
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_left' (by omega), show 243 + i - 127 - 66 - 50 = i by omega]
  · show (sigDigests s).getD (292 + i) 0 = (layerList s 3).getD i 0
    rw [sigDigests_tail s _ (by omega), getD_append_right' (by omega), l0, getD_append_right' (by omega), l1,
      getD_append_right' (by omega), l2, show 292 + i - 127 - 66 - 50 - 49 = i by omega]
theorem sigDigests_layValue (lay : Layer) (i : Nat) (hi : i < chainCount lay) :
    (sigDigests s).getD (layIdx lay + i) 0 = (s.layers lay).values ⟨i, hi⟩ := by
  rw [sigDigests_layer s lay i (by omega), layerList, getD_append_left' (by simpa using hi), getD_ofFn']
theorem sigDigests_layPath (lay : Layer) (j : Nat) (hj : j < height lay) :
    (sigDigests s).getD (layIdx lay + (chainCount lay + j)) 0 = (s.layers lay).path ⟨j, hj⟩ := by
  rw [sigDigests_layer s lay _ (by omega), layerList, getD_append_right' (by simp), List.length_ofFn,
    Nat.add_sub_cancel_left, getD_ofFn']
end getD
def sigDig (b : Bytes 5456) (k : Nat) : Digest := b.extractLsb' (128 * k) 128
def sigDec (b : Bytes 5456) : WCT9.Signature where
  rho := sigDig b 0
  openings := fun k => ⟨fun t => sigDig b (1 + 14 * k.val + t.val), fun l => sigDig b (1 + 14 * k.val + 7 + l.val)⟩
  layers := fun lay => ⟨fun i => sigDig b (layIdx lay + i.val), fun j => sigDig b (layIdx lay + (chainCount lay + j.val))⟩
theorem pow_5456 : (2 : Nat) ^ (8 * 5456) = 2 ^ (128 * 341) := congrArg (fun n => 2 ^ n) rfl
def sigB (s : WCT9.Signature) : Bytes 5456 := BitVec.ofNat _ (readLE (WCT9.serialize s))
set_option exponentiation.threshold 50000 in
theorem sigB_toNat (s : WCT9.Signature) : (sigB s).toNat = digNat (sigDigests s) := by
  have hlt := digNat_lt (sigDigests s)
  rw [length_sigDigests] at hlt
  rw [sigB, BitVec.toNat_ofNat, serialize_eq, ← digNat, Nat.mod_eq_of_lt (lt_of_lt_of_eq hlt pow_5456.symm)]
theorem sigDig_toNat (b : Bytes 5456) (k : Nat) : (sigDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem sigDig_sigB (s : WCT9.Signature) (k : Nat) : sigDig (sigB s) k = (sigDigests s).getD k 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [sigDig_toNat, sigB_toNat, digNat_digit]
theorem sigDec_sigB (s : WCT9.Signature) : sigDec (sigB s) = s := by
  have hd := sigDig_sigB s
  have hr := sigDigests_rho s
  have hv := sigDigests_value s
  have hp := sigDigests_path s
  have hlv := sigDigests_layValue s
  have hlp := sigDigests_layPath s
  rcases s with ⟨rho, openings, layers⟩
  generalize sigB ⟨rho, openings, layers⟩ = b at hd ⊢
  unfold sigDec
  congr 1
  · rw [hd]; exact hr
  · funext k
    have hv' := hv k
    have hp' := hp k
    simp only at hv' hp'
    rcases ho : openings k with ⟨vals, path⟩
    rw [ho] at hv' hp'
    congr 1
    · funext t; rw [hd]; exact hv' t
    · funext l; rw [hd]; exact hp' l
  · funext lay
    have hv' := hlv lay
    have hpa' := hlp lay
    simp only at hv' hpa'
    rcases hl : layers lay with ⟨vals, path⟩
    rw [hl] at hv' hpa'
    congr 1
    · funext i; rw [hd]; exact hv' i.val i.isLt
    · funext j; rw [hd]; exact hpa' j.val j.isLt
theorem sigDigests_sigDec (b : Bytes 5456) (k : Nat) (hk : k < 341) :
    (sigDigests (sigDec b)).getD k 0 = sigDig b k := by
  by_cases h0 : k = 0
  · subst h0; exact sigDigests_rho _
  by_cases h1 : k < 127
  · have hq : (k - 1) / 14 < 9 := by omega
    have e : k = 1 + 14 * (⟨(k - 1) / 14, hq⟩ : WCT9.Coord).val + (k - 1) % 14 := by simp; omega
    by_cases hr : (k - 1) % 14 < 7
    · have := sigDigests_value (sigDec b) ⟨(k - 1) / 14, hq⟩ ⟨(k - 1) % 14, hr⟩
      simp only at this
      rw [← e] at this
      rw [this]
      show sigDig b (1 + 14 * ((k - 1) / 14) + (k - 1) % 14) = sigDig b k
      rw [← e]
    · have := sigDigests_path (sigDec b) ⟨(k - 1) / 14, hq⟩ ⟨(k - 1) % 14 - 7, by omega⟩
      simp only at this
      rw [show 1 + 14 * ((k - 1) / 14) + 7 + ((k - 1) % 14 - 7) = k by omega] at this
      rw [this]
      show sigDig b (1 + 14 * ((k - 1) / 14) + 7 + ((k - 1) % 14 - 7)) = sigDig b k
      rw [show 1 + 14 * ((k - 1) / 14) + 7 + ((k - 1) % 14 - 7) = k by omega]
  have key : ∀ (lay : Layer) (i : Nat), i < chainCount lay + height lay → layIdx lay + i = k →
      (sigDigests (sigDec b)).getD k 0 = sigDig b k := by
    intro lay i hi he
    subst he
    rw [sigDigests_layer _ lay i hi]
    unfold layerList
    by_cases hc : i < chainCount lay
    · rw [getD_append_left' (by simpa using hc), getD_ofFn' _ i hc]; rfl
    · rw [getD_append_right' (by simp; omega), List.length_ofFn, getD_ofFn' _ (i - chainCount lay) (by omega)]
      show sigDig b (layIdx lay + (chainCount lay + (i - chainCount lay))) = _
      rw [show chainCount lay + (i - chainCount lay) = i by omega]
  by_cases h3 : k < 193
  · exact key 0 (k - 127) (by rw [chainCount_0, height_0]; omega) (by simp [layIdx]; omega)
  by_cases h4 : k < 243
  · exact key 1 (k - 193) (by rw [chainCount_1, height_1]; omega) (by simp [layIdx]; omega)
  by_cases h5 : k < 292
  · exact key 2 (k - 243) (by rw [chainCount_2, height_2]; omega) (by simp [layIdx]; omega)
  · exact key 3 (k - 292) (by rw [chainCount_3, height_3]; omega) (by simp [layIdx]; omega)
set_option exponentiation.threshold 50000 in
theorem sigB_sigDec (b : Bytes 5456) : sigB (sigDec b) = b := by
  apply BitVec.eq_of_toNat_eq
  rw [sigB_toNat]
  apply digNat_eq_of_digits
  · rw [length_sigDigests]; exact lt_of_lt_of_eq b.isLt pow_5456
  · intro k hk
    rw [length_sigDigests] at hk
    rw [sigDigests_sigDec b k hk, sigDig_toNat]
theorem sigB_injective : Function.Injective sigB := fun s t h => by
  rw [← sigDec_sigB s, ← sigDec_sigB t, h]
theorem sigDec_injective : Function.Injective sigDec := fun a b h => by
  rw [← sigB_sigDec a, ← sigB_sigDec b, h]
theorem sigDig_lo (b : Bytes 5456) (k : Nat) : (sigDig b k).extractLsb' 0 64 = b.extractLsb' (64 * (2 * k)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_zero, Nat.div_one]
  rw [show 64 * (2 * k) = 128 * k by ring, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem sigDig_hi (b : Bytes 5456) (k : Nat) :
    (sigDig b k).extractLsb' 64 64 = b.extractLsb' (64 * (2 * k + 1)) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [sigDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 64 * (2 * k + 1) = 128 * k + 64 by ring, pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [Nat.mod_mod_of_dvd _ (by norm_num)]
end ClaudeWCT.W9.T3M
