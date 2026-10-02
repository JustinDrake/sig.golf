import SigGolfCandidate.Verify.Judg

/-!
# Bytes and doublewords

`w64 l` is the little-endian doubleword of (at most 8) bytes, `wordsOfN n l` the first `n`
doublewords of a byte list. The HASH query of a padded input is `queryOfWords` of its words
(`pad64_eq_words`); the word lists of all input formats are computed below.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def w64 (l : List Byte) : Word := BitVec.ofNat 64 (leNat l)

def wordsOfN : Nat → List Byte → List Word
  | 0, _ => []
  | n + 1, l => w64 (l.take 8) :: wordsOfN n (l.drop 8)

theorem leNat_append (a b : List Byte) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih => simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]; ring

theorem leNat_zeros (k : Nat) : leNat (zeros k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zeros, List.replicate_succ, leNat] at ih ⊢; rw [ih]; rfl

theorem w64_toNat (l : List Byte) (h : l.length ≤ 8) : (w64 l).toNat = leNat l := by
  unfold w64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := leNat_lt l
  calc leNat l < 256 ^ l.length := this
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
    _ = 2 ^ 64 := by norm_num

theorem wordsToNat_wordsOfN : ∀ (n : Nat) (l : List Byte), l.length ≤ 8 * n →
    wordsToNat (wordsOfN n l) = leNat l := by
  intro n
  induction n with
  | zero => intro l h; have : l = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; rfl
  | succ n ih =>
    intro l h
    simp only [wordsOfN, wordsToNat]
    rw [ih _ (by simp; omega), w64_toNat _ (by simp)]
    conv_rhs => rw [← List.take_append_drop 8 l, leNat_append]
    by_cases hl : 8 ≤ l.length
    · rw [List.length_take_of_le hl]; norm_num
    · have : l.drop 8 = [] := List.drop_eq_nil_of_le (by omega)
      rw [this]; simp [leNat]

theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  unfold padTo64 padBlocks
  simp only [List.length_append, length_zeros]
  omega

theorem pad64_eq_words (x : List Byte) :
    pad64 x = queryOfWords (padBlocks x.length)
      (wordsOfN (8 * (padBlocks x.length + 1)) (padTo64 x)) := by
  unfold pad64 queryOfWords ofList
  rw [wordsToNat_wordsOfN _ _ (by rw [length_padTo64]; omega)]

theorem wordsOfN_append : ∀ (a b : Nat) (l1 l2 : List Byte), l1.length = 8 * a →
    wordsOfN (a + b) (l1 ++ l2) = wordsOfN a l1 ++ wordsOfN b l2 := by
  intro a
  induction a with
  | zero => intro b l1 l2 h; have : l1 = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; simp [wordsOfN]
  | succ a ih =>
    intro b l1 l2 h
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [wordsOfN, List.cons_append]
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ _ _ (by simp; omega)]

theorem wordsOfN_zeros : ∀ (n : Nat), wordsOfN n (zeros (8 * n)) = List.replicate n 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordsOfN, List.replicate_succ]
    rw [show 8 * (n + 1) = 8 + 8 * n by omega]
    have h1 : (zeros (8 + 8 * n)).take 8 = zeros 8 := by simp [zeros, List.take_replicate]
    have h2 : (zeros (8 + 8 * n)).drop 8 = zeros (8 * n) := by simp [zeros, List.drop_replicate]
    rw [h1, h2, ih]
    rfl

/-! ## Tweak words -/

def twLo (t lay tau p : Nat) : Nat :=
  1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) + 2 ^ 32 * (p % 2 ^ 32)

def twHi (tau j : Nat) : Nat := tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  have := leNat_map_range 4 v
  simpa [le32, leBytes] using this

theorem wordsOfN_tweak (t lay tau p j : Nat) :
    wordsOfN 2 (tweak t lay tau p j) =
      [BitVec.ofNat 64 (twLo t lay tau p), BitVec.ofNat 64 (twHi tau j)] := by
  unfold tweak
  have e1 : [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p ++ le32 (tau % 2 ^ 32) ++
      le32 j = ([byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p) ++
        (le32 (tau % 2 ^ 32) ++ le32 j) := by simp
  rw [e1, show (2 : Nat) = 1 + 1 from rfl, wordsOfN_append 1 1 _ _ (by simp)]
  simp only [wordsOfN, List.cons_append, List.nil_append]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  simp only [w64, leNat_append, leNat, leNat_le32, byte_toNat, length_le32, twLo, twHi,
    List.length_cons, List.length_nil]
  refine congrArg₂ _ (congrArg _ ?_) (congrArg₂ _ (congrArg _ ?_) rfl) <;> omega

/-! ## Values -/

def vw0 (v : Val) : Word := w64 (v.take 8)
def vw1 (v : Val) : Word := w64 (v.drop 8)

theorem wordsOfN_val_append (v : Val) (hv : v.length = 16) (k : Nat) (l : List Byte) :
    wordsOfN (2 + k) (v ++ l) = [vw0 v, vw1 v] ++ wordsOfN k l := by
  rw [wordsOfN_append 2 k v l (by omega)]
  simp only [wordsOfN, vw0, vw1, List.drop_drop]
  rw [List.take_of_length_le (l := v.drop 8) (by simp; omega)]

theorem wordsOfN_flatten_append : ∀ (vs : List Val), (∀ v ∈ vs, v.length = 16) →
    ∀ (k : Nat) (l : List Byte),
    wordsOfN (2 * vs.length + k) (vs.flatten ++ l) =
      (vs.map fun v => [vw0 v, vw1 v]).flatten ++ wordsOfN k l := by
  intro vs
  induction vs with
  | nil => intro _ k l; simp
  | cons v vs ih =>
    intro h k l
    simp only [List.length_cons, List.flatten_cons, List.map_cons, List.append_assoc]
    rw [show 2 * (vs.length + 1) + k = 2 + (2 * vs.length + k) by omega,
      wordsOfN_val_append v (h v (List.mem_cons_self ..)),
      ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

theorem padBlocks_val (len n : Nat) (h1 : len ≤ 64 * (n + 1)) (h2 : 64 * n < len) :
    padBlocks len = n := by unfold padBlocks; omega

/-- The query of `thInput tw payload` (a 16-byte tweak) of `n + 1` blocks. -/
theorem pad64_thInput (tw payload : List Byte) (htw : tw.length = 16) (n : Nat)
    (h1 : 32 + payload.length ≤ 64 * (n + 1)) (h2 : 64 * n < 32 + payload.length) :
    pad64 (thInput tw payload) = queryOfWords n (wordsOfN 2 tw ++ [0, 0] ++
      wordsOfN (8 * n + 4) (payload ++ zeros (64 * (n + 1) - (32 + payload.length)))) := by
  have hl : (thInput tw payload).length = 32 + payload.length := by
    simp [thInput, htw]; omega
  rw [pad64_eq_words, hl, padBlocks_val _ _ h1 h2]
  unfold padTo64
  rw [hl, padBlocks_val _ _ h1 h2]
  unfold thInput
  rw [show 8 * (n + 1) = 2 + (2 + (8 * n + 4)) by omega, List.append_assoc, List.append_assoc,
    wordsOfN_append 2 _ tw _ (by omega), wordsOfN_append 2 _ P _ (by rfl)]
  rfl

theorem w64_zeros8 : w64 (zeros 8) = 0 := rfl

theorem wordsOfN_zeros' (n : Nat) : wordsOfN n (zeros (8 * n)) = List.replicate n 0 :=
  wordsOfN_zeros n

/-! ## Input formats -/

theorem pad64_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    pad64 (chainInput lay tau e i mu v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 1 lay tau (8 * i + mu - 1)), BitVec.ofNat 64 (twHi tau e), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  unfold chainInput
  rw [pad64_thInput _ _ (by simp) 0 (by omega) (by omega), wordsOfN_tweak, hv,
    show 8 * 0 + 4 = 2 + 2 by rfl, wordsOfN_val_append v hv]
  rfl

theorem pad64_porsLeafInput (idx j : Nat) (v : Val) (hv : v.length = 16) :
    pad64 (porsLeafInput idx j v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 9 0 idx 0), BitVec.ofNat 64 (twHi idx j), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  unfold porsLeafInput
  rw [pad64_thInput _ _ (by simp) 0 (by omega) (by omega), wordsOfN_tweak, hv,
    show 8 * 0 + 4 = 2 + 2 by rfl, wordsOfN_val_append v hv]
  rfl

theorem pad64_nodeInput (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (nodeInput lay tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 3 lay tau lam), BitVec.ofNat 64 (twHi tau j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold nodeInput
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

theorem pad64_porsNodeInput (idx H : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (porsNodeInput idx H l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 10 0 idx 0), BitVec.ofNat 64 (twHi idx H), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold porsNodeInput
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

/-! ### The relabelled PORS queries

The relabelling swaps the `p` field (zero in the Ref) and the low half of `tau`: the hashed tweak
is `tweak t 0 (Ref.tauH idx) idx F`, i.e. word 0 is `twLo t 0 idx idx` (tag, high byte of `tau`, low
half of `tau` in the `p` slot) and word 1 is `twHi 0 F` (zero, then the relabelled header `F`). -/

/-- The hashed form of a PORS node input (header `F`). -/
def pNode (idx F : Nat) (l r : Val) : List Byte := thInput (tweak 10 0 (Ref.tauH idx) idx F) (l ++ r)
/-- The hashed form of a PORS leaf input (header `F`). -/
def pLeaf (idx F : Nat) (v : Val) : List Byte := thInput (tweak 9 0 (Ref.tauH idx) idx F) v

theorem twLo_tauH (t idx : Nat) : twLo t 0 (Ref.tauH idx) idx = twLo t 0 idx idx := by
  unfold twLo Ref.tauH; congr 2; omega

theorem twHi_tauH (idx F : Nat) : twHi (Ref.tauH idx) F = twHi 0 F := by
  unfold twHi Ref.tauH; omega

theorem pad64_pNode (idx F : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    pad64 (pNode idx F l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 10 0 idx idx), BitVec.ofNat 64 (twHi 0 F), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold pNode
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak, twLo_tauH,
    twHi_tauH]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

theorem pad64_pLeaf (idx F : Nat) (v : Val) (hv : v.length = 16) :
    pad64 (pLeaf idx F v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 9 0 idx idx), BitVec.ofNat 64 (twHi 0 F), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  unfold pLeaf
  rw [pad64_thInput _ _ (by simp) 0 (by omega) (by omega), wordsOfN_tweak, twLo_tauH, twHi_tauH, hv,
    show 8 * 0 + 4 = 2 + 2 by rfl, wordsOfN_val_append v hv]
  rfl

/-- The swapped words of a Ref PORS block (tag `t`, `tau = idx`, `p = 0`, header `F`). -/
theorem swW_pors (t idx F : Nat) (f : Nat → Nat) (hf : ∀ v, v < 4294967296 → f v < 4294967296) :
    AddressFormat.swW0 (BitVec.ofNat 64 (twLo t 0 idx 0)) (BitVec.ofNat 64 (twHi idx F)) =
      BitVec.ofNat 64 (twLo t 0 idx idx) ∧
    AddressFormat.swW1 f (BitVec.ofNat 64 (twLo t 0 idx 0)) (BitVec.ofNat 64 (twHi idx F)) =
      BitVec.ofNat 64 (twHi 0 (f (F % 2 ^ 32))) := by
  have hl : (BitVec.ofNat 64 (twLo t 0 idx 0)).toNat = twLo t 0 idx 0 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold twLo; omega
  have hh : (BitVec.ofNat 64 (twHi idx F)).toNat = twHi idx F := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; unfold twHi; omega
  unfold AddressFormat.swW0 AddressFormat.swW1
  rw [hl, hh]
  have e1 : twHi idx F / 4294967296 = F % 2 ^ 32 := by unfold twHi; omega
  have e2 : twLo t 0 idx 0 / 4294967296 = 0 := by unfold twLo; omega
  rw [e1, e2]
  have he := hf (F % 2 ^ 32) (by omega)
  generalize f (F % 2 ^ 32) = G at he ⊢
  constructor
  · congr 1; unfold twLo twHi; omega
  · congr 1; unfold twHi; omega

/-- **The PORS node relabelling** (`AddressFormat.nodeRel`): the query of a node input under heap
index `H` has words `twLo 10 0 idx idx`, `twHi 0 (Rev.efield H)`. -/
theorem addrFmt_porsNodeWords (idx H : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    addrFmt (porsNodeInput idx H l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 10 0 idx idx), BitVec.ofNat 64 (twHi 0 (Rev.efield H)), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  have hf : fmt (porsNodeInput idx H l r) = pad64 (porsNodeInput idx H l r) :=
    fmt_thInput _ _ _ _ _ _ (by decide)
  rw [addrFmt, hf, pad64_porsNodeInput _ _ _ _ hl hr]
  have hlo : (BitVec.ofNat 64 (twLo 10 0 idx 0)).toNat % 65536 = 2561 := by
    rw [BitVec.toNat_ofNat]; unfold twLo; omega
  rw [AddressFormat.queryPerm_node _ _ _ rfl hlo]
  obtain ⟨k0, k1⟩ := swW_pors 10 idx H Rev.efield AddressFormat.efield_lt'
  rw [k0, k1, Rev.efield_mod]

/-- The relabelled node query as a padded input: header field `Rev.efield H`. -/
theorem addrFmt_porsNodeInput_pad (idx H : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    addrFmt (porsNodeInput idx H l r) = pad64 (pNode idx (Rev.efield H) l r) := by
  rw [addrFmt_porsNodeWords _ _ _ _ hl hr, pad64_pNode _ _ _ _ hl hr]

theorem addrFmt_porsLeafWords (idx j : Nat) (v : Val) (hv : v.length = 16) :
    addrFmt (porsLeafInput idx j v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 9 0 idx idx), BitVec.ofNat 64 (twHi 0 (LeafScale.left3 (j % 2^32))), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  have hf : fmt (porsLeafInput idx j v) = pad64 (porsLeafInput idx j v) :=
    fmt_thInput _ _ _ _ _ _ (by decide)
  rw [addrFmt, hf, pad64_porsLeafInput _ _ _ hv]
  have hlo : (BitVec.ofNat 64 (twLo 9 0 idx 0)).toNat % 65536 = 2305 := by
    rw [BitVec.toNat_ofNat]; unfold twLo; omega
  rw [AddressFormat.queryPerm_leaf _ _ _ rfl hlo]
  obtain ⟨k0, k1⟩ := swW_pors 9 idx j LeafScale.left3 LeafScale.left3_lt'
  rw [k0, k1]

theorem addrFmt_porsLeafInput_pad (idx j : Nat) (v : Val) (hv : v.length = 16)
    (hj : j ≤ 2^14) :
    addrFmt (porsLeafInput idx j v) = pad64 (pLeaf idx (8*j) v) := by
  rw [addrFmt_porsLeafWords _ _ _ hv, pad64_pLeaf _ _ _ hv]
  rw [Nat.mod_eq_of_lt (show j < 2^32 by omega), LeafScale.left3_small j (by omega)]

/-- The encoding input of the 32-byte message `L ++ R` (the two children of the root of the tree below,
or `P ++` the PORS root): one block, the message in the words 2 .. 5. -/
theorem pad64_encInput (lay tau e : Nat) (L R : Val) (hL : L.length = 16) (hR : R.length = 16) (c : Nat) :
    pad64 (encInput lay tau e (L ++ R) c) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 4 lay tau 0), BitVec.ofNat 64 (twHi tau e), vw0 L, vw1 L,
        vw0 R, vw1 R, BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  have hl : (encInput lay tau e (L ++ R) c).length = 52 := by
    simp [encInput, length_tweak, hL, hR]
  rw [pad64_eq_words, hl, padBlocks_val 52 0 (by omega) (by omega)]
  unfold padTo64
  rw [hl, padBlocks_val 52 0 (by omega) (by omega)]
  unfold encInput
  simp only [List.append_assoc]
  rw [show 8 * (0 + 1) = 2 + (2 + (2 + 2)) by rfl,
    wordsOfN_append 2 _ (tweak 4 lay tau 0 e) _ (by simp [length_tweak]), wordsOfN_tweak,
    wordsOfN_val_append L hL, wordsOfN_val_append R hR]
  simp only [wordsOfN]
  have h1 : (le32 c ++ zeros (64 * (0 + 1) - 52)).take 8 = le32 c ++ zeros 4 := by
    simp [zeros, List.take_append]
  have h2 : ((le32 c ++ zeros (64 * (0 + 1) - 52)).drop 8).take 8 = zeros 8 := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp : (le32 c).length ≤ 8)]
    simp [zeros, List.take_replicate]
  rw [h1, h2]
  simp only [w64, leNat_append, leNat_le32, leNat_zeros, Nat.mul_zero, Nat.add_zero]
  rfl

/-- The rotated one-block encoding query for the ordered pair of children. -/
theorem addrFmt_encInput_words (lay tau e : Nat) (L R : Val)
    (hL : L.length = 16) (hR : R.length = 16) (c : Nat) :
    addrFmt (encInput lay tau e (L ++ R) c) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 4 lay tau 0), BitVec.ofNat 64 (twHi tau e),
        BitVec.ofNat 64 (c % 2 ^ 32), 0, vw0 L, vw1 L, vw0 R, vw1 R] := by
  have hf : fmt (encInput lay tau e (L ++ R) c) = pad64 (encInput lay tau e (L ++ R) c) :=
    Ref.fmt_of_tag _ (by simp [encInput, tweak]; decide)
  rw [addrFmt_encInput_valid _ _ _ _ (by simp [hL, hR]), hf,
    pad64_encInput lay tau e L R hL hR c]
  apply EncodingRotate.query_words
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_mod_of_dvd _ (by decide : 65536 ∣ 2 ^ 64)]
  unfold twLo
  omega

theorem pad64_leafInput (lay tau e : Nat) (ends : List Val) (hl : ends.length = 42)
    (hv : ∀ v ∈ ends, v.length = 16) :
    pad64 (leafInput lay tau e ends) = queryOfWords 10
      ([BitVec.ofNat 64 (twLo 2 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
        (ends.map fun v => [vw0 v, vw1 v]).flatten) := by
  have hflat : ends.flatten.length = 672 := by
    rw [List.length_flatten]
    have : ends.map List.length = List.replicate 42 16 := by
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      exact hv _ (List.getElem_mem _)
    rw [this]; decide
  unfold leafInput
  rw [pad64_thInput _ _ (by simp) 10 (by omega) (by omega), wordsOfN_tweak, hflat,
    show 8 * 10 + 4 = 2 * ends.length + 0 by omega, wordsOfN_flatten_append ends hv]
  simp [wordsOfN]

theorem pad64_leafPayload4 (lay tau e : Nat) (ends : List Val) (hl : ends.length = 42)
    (hv : ∀ v ∈ ends, v.length = 16) :
    pad64 (thInput (tweak 4 lay tau 0 e) ends.flatten) = queryOfWords 10
      ([BitVec.ofNat 64 (twLo 4 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
        (ends.map fun v => [vw0 v, vw1 v]).flatten) := by
  have hflat : ends.flatten.length = 672 := by
    rw [List.length_flatten]
    have : ends.map List.length = List.replicate 42 16 := by
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      exact hv _ (List.getElem_mem _)
    rw [this]; decide
  rw [pad64_thInput _ _ (by simp) 10 (by omega) (by omega), wordsOfN_tweak, hflat,
    show 8 * 10 + 4 = 2 * ends.length + 0 by omega, wordsOfN_flatten_append ends hv]
  simp [wordsOfN]

/-- The eleven-block WOTS leaf class uses the cached encoding-header tag. -/
theorem addrFmt_leafInput_words (lay tau e : Nat) (ends : List Val) (hl : ends.length = 42)
    (hv : ∀ v ∈ ends, v.length = 16) :
    addrFmt (leafInput lay tau e ends) = queryOfWords 10
      ([BitVec.ofNat 64 (Ref.LeafCarry.header (BitVec.ofNat 64 (twLo 4 lay tau 0)).toNat), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
        (ends.map fun v => [vw0 v, vw1 v]).flatten) := by
  rw [addrFmt_leafInput_tag4 lay tau e ends hl hv, pad64_leafPayload4 lay tau e ends hl hv]
  have hlen : ((ends.map fun v => [vw0 v, vw1 v]).flatten).length = 84 := by
    have hf (vs : List Val) : ((vs.map fun v => [vw0 v, vw1 v]).flatten).length = 2 * vs.length := by
      induction vs with
      | nil => rfl
      | cons v vs ih => simp [List.flatten_cons] at ih ⊢; omega
    simpa only [hl] using hf ends
  exact Ref.LeafCarry.query_words _ _ (by simp [hlen])

theorem pad64_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    pad64 (digestInput rho m) = queryOfWords 1
      ([BitVec.ofNat 64 (twLo 12 0 0 0), BitVec.ofNat 64 (twHi 0 0), 0, 0, vw0 rho, vw1 rho, 0, 0] ++
        wordsOfN 4 m ++ [0, 0, 0, 0]) := by
  unfold digestInput
  rw [pad64_thInput _ _ (by simp) 1 (by simp [hr, hm]) (by simp [hr, hm]), wordsOfN_tweak]
  simp only [List.length_append, hr, hm, length_zeros]
  simp only [List.append_assoc]
  rw [show 8 * 1 + 4 = 2 + (2 + (4 + 4)) by rfl, wordsOfN_val_append rho hr,
    wordsOfN_append 2 _ (zeros 16) _ (by rfl),
    wordsOfN_append 4 4 m _ (by omega), show 64 * (1 + 1) - (32 + (16 + 16 + 32)) = 8 * 4 by rfl,
    wordsOfN_zeros, wordsOfN_zeros 4]
  simp

/-! ## Answers -/

theorem extractLsb'_byte (a : BitVec 256) (i : Nat) (hi : i < 32) :
    a.extractLsb' (8 * i) 8 = byte (a.toNat / 256 ^ i) := by
  have := extractByte_ofNat 256 a.toNat i (by omega)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem answerBytes_eq (a : BitVec 256) :
    answerBytes 16 a = (List.range 16).map fun i => byte (a.toNat / 256 ^ i) :=
  List.map_congr_left (fun i hi => extractLsb'_byte a i (by simp at hi; omega))

theorem vw0_answer (a : BitVec 256) : vw0 (answerBytes 16 a) = a.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold vw0
  rw [w64_toNat _ (by simp), BitVec.extractLsb'_toNat, Nat.shiftRight_zero, answerBytes_eq,
    ← List.map_take, List.take_range, show min 8 16 = 8 by rfl, leNat_map_range]
  rfl

theorem vw1_answer (a : BitVec 256) : vw1 (answerBytes 16 a) = a.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold vw1
  rw [w64_toNat _ (by simp), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, answerBytes_eq,
    ← List.map_drop, List.range_eq_range', List.drop_range', List.range'_eq_map_range, List.map_map]
  have : ((fun i => byte (a.toNat / 256 ^ i)) ∘ fun i => 0 + 8 + i) =
      fun i => byte (a.toNat / 2 ^ 64 / 256 ^ i) := by
    funext i; simp only [Function.comp, Nat.zero_add, Nat.pow_add, Nat.div_div_eq_div_mul]
    norm_num
  rw [show 16 - 8 = 8 by rfl, this, leNat_map_range]
  norm_num

theorem length_answerBytes16 (a : BitVec 256) : (answerBytes 16 a).length = 16 := by simp

end SigGolfCandidate.Verify
