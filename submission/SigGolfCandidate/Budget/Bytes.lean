import SigGolfCandidate.Budget.Basic

/-!
# Budget: query bytes, padding, block counts

`qbyte q i` is byte `i` of a query. For a padded input it is byte `i` of the input
(`qbyte_pad64`), so padding is injective on inputs of equal length (`pad64_inj`), and the tweak's
type byte (`qbyte _ 1`) and layer byte (`qbyte _ 2`) can be read off the query.
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

/-- Byte `i` of a query. -/
def rawByte (q : Query) (i : Nat) : Nat := q.2.toNat / 256 ^ i % 256

def qbyte (q : Query) (i : Nat) : Nat := rawByte (AddressFormat.queryInverse q) i

theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  unfold padTo64 padBlocks
  simp only [List.length_append, length_zeros]
  omega

theorem getD_padTo64 (x : List Byte) (i : Nat) : (padTo64 x).getD i 0 = x.getD i 0 := by
  unfold padTo64 zeros
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < x.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (l := x) (by omega),
      List.getElem?_replicate]
    split <;> rfl

theorem rawByte_pad64 (x : List Byte) (i : Nat) : rawByte (pad64 x) i = (x.getD i 0).toNat := by
  unfold rawByte pad64 ofList
  simp only [BitVec.toNat_ofNat]
  have hlt := leNat_lt (padTo64 x)
  rw [length_padTo64] at hlt
  have h2 : (2 : Nat) ^ (8 * (64 * (padBlocks x.length + 1))) = 256 ^ (64 * (padBlocks x.length + 1)) := by
    rw [Nat.pow_mul]
  rw [h2, Nat.mod_eq_of_lt hlt, leNat_div_mod, getD_padTo64]

theorem getD_eq_of_pad64_eq {x y : List Byte} (e : pad64 x = pad64 y) (i : Nat) :
    x.getD i 0 = y.getD i 0 := by
  have h := congrArg (fun q => rawByte q i) e
  simp only [rawByte_pad64] at h
  exact BitVec.eq_of_toNat_eq h

theorem pad64_inj {x y : List Byte} (h : x.length = y.length) (e : pad64 x = pad64 y) : x = y := by
  apply List.ext_getElem h
  intro i h1 h2
  have := getD_eq_of_pad64_eq e i
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this

theorem blocks_pad64 (x : List Byte) : (pad64 x).blocks = padBlocks x.length + 1 := rfl

theorem blocks_pad64_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (pad64 x).blocks ≤ k := by
  rw [blocks_pad64]; unfold padBlocks; omega

/-! ## The oracle input format -/

theorem blocksFmt_le (x : List Byte) (k : Nat) (h : x.length ≤ 64 * k) (hk : 1 ≤ k) :
    (addrFmt x).blocks ≤ k :=
  by rw [addrFmt_blocks]; exact (Ref.blocks_fmt_le x).trans (blocks_pad64_le x k h hk)

/-- Bytes `0..4` (tag, layer) of a formatted query are those of the input. -/
theorem qbyte_fmt (x : List Byte) (i : Nat) (hi : i < 4) : qbyte (addrFmt x) i = (x.getD i 0).toNat := by
  unfold qbyte addrFmt
  rw [AddressFormat.queryInverse_queryPerm]
  unfold rawByte
  rw [← leNat_toList, leNat_div_mod, getD_toList_fmt x i (Or.inl hi)]

/-- Inputs of a tag other than `1, 3, 12` are zero padded. -/
theorem fmt_eq_pad64 (t lay tau p j : Nat) (pl : List Byte)
    (ht : t % 256 ≠ 1 ∧ t % 256 ≠ 3 ∧ t % 256 ≠ 12 ∧ t % 256 ≠ 10 ∧ t % 256 ≠ 9 ∧ t % 256 ≠ 4 ∧ t % 256 ≠ 2 ∧ t % 256 ≠ 5 ∧ t % 256 ≠ 6) :
    addrFmt (thInput (tweak t lay tau p j) pl) = pad64 (thInput (tweak t lay tau p j) pl) := by
  rw [addrFmt_eq_th _ _ _ _ _ _ (by tauto)]
  refine fmt_thInput _ _ _ _ _ _ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> have := congrArg BitVec.toNat h <;>
    simp [byte_toNat] at this <;> omega

/-! ## Tweak bytes -/

theorem qbyte_tag (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (addrFmt (thInput (tweak t lay tau p j) pl)) 1 = t % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]

theorem qbyte_lay (t lay tau p j : Nat) (pl : List Byte) :
    qbyte (addrFmt (thInput (tweak t lay tau p j) pl)) 2 = lay % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [thInput, tweak, byte_toNat]

/-- The encoding input carries its message right after the tweak; its tag and layer bytes are the
tweak's. -/
theorem qbyte_tag_enc (lay tau e : Nat) (M : Val) (c : Nat) :
    qbyte (addrFmt (encInput lay tau e M c)) 1 = 4 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [encInput, tweak, byte_toNat]

theorem qbyte_lay_enc (lay tau e : Nat) (M : Val) (c : Nat) :
    qbyte (addrFmt (encInput lay tau e M c)) 2 = lay % 256 := by
  rw [qbyte_fmt _ _ (by omega)]; simp [encInput, tweak, byte_toNat]

theorem leNat_leBytes (k v : Nat) : leNat (leBytes k v) = v % 256 ^ k := leNat_map_range k v

theorem le32_inj {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32) (h : le32 c = le32 c') :
    c = c' := by
  have := congrArg leNat h
  simp only [le32, leNat_leBytes] at this
  rw [Nat.mod_eq_of_lt (by simpa using hc), Nat.mod_eq_of_lt (by simpa using hc')] at this
  exact this

/-- Tweaks with the same type and layer determine their `p` fields below `2 ^ 32`. -/
theorem tweak_p_inj {t lay tau p j t' lay' tau' p' j' : Nat} (hp : p < 2 ^ 32) (hp' : p' < 2 ^ 32)
    (h : tweak t lay tau p j = tweak t' lay' tau' p' j') : p = p' := by
  unfold tweak at h
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
  obtain ⟨-, -, -, -, h⟩ := h
  have h2 := List.append_inj_left' (List.append_inj_left' h (by simp)) (by simp)
  exact le32_inj hp hp' (List.append_inj_left' h2 (by simp))

theorem getD_len_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) (i : Nat) :
    (l.getD i []).length ≤ n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hi)

theorem length_flatten_le {l : List (List Byte)} {n : Nat} (h : ∀ v ∈ l, v.length ≤ n) :
    l.flatten.length ≤ n * l.length := by
  induction l with
  | nil => simp
  | cons v l ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h v (by simp)
    have h2 := ih (fun w hw => h w (by simp [hw]))
    rw [Nat.mul_succ]; omega

end SigGolfCandidate.Budget
