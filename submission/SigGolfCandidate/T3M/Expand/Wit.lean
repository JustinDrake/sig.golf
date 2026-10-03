import SigGolfCandidate.T3M.Expand.LayersBlocks
import SigGolfCandidate.T3M.Witness.Encode

/-!
# `expand`: the witness doublewords (stream E)

`witList_words` : the 3,155 doublewords of `witList N w` are the header (8), the FTS leaf blocks (128), the stream
(1,275) and the four layer regions (560, 400, 392, 392); `layer_words` reads a layer region from its chain values,
path siblings and zero doublewords; `header_words` the header from its doublewords.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest HashOutput Signature Witness Layer LayerSignature chainCount height route readLE)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

/-! ## Blocks of doublewords -/

theorem readWords_blocks (t : MachineState) : ∀ (bs : List (List Word)) (A : Nat),
    (∀ b ∈ bs, b.length = 8) → (∀ k < bs.length, t.readWords (BitVec.ofNat 64 (A + 64 * k)) 8 = bs.getD k []) →
    t.readWords (BitVec.ofNat 64 A) (8 * bs.length) = bs.flatten
  | [], _, _, _ => rfl
  | b :: bs, A, hl, h => by
    rw [List.length_cons, show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, readWords_add,
      show A + 8 * 8 = A + 64 by ring, List.flatten_cons]
    congr 1
    · simpa using h 0 (by simp)
    · refine readWords_blocks t bs (A + 64) (fun x hx => hl x (by simp [hx])) (fun k hk => ?_)
      have := h (k + 1) (by simp; omega)
      rw [show A + 64 * (k + 1) = A + 64 + 64 * k by ring] at this
      simpa using this

theorem wordsOf_flatMap64 {α : Type} (f : α → List UInt8) (hf : ∀ x, (f x).length = 64) :
    ∀ (xs : List α), wordsOf (xs.flatMap f) = xs.flatMap (fun x => wordsOf (f x))
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.flatMap_cons, wordsOf_append _ _ (by rw [hf]), wordsOf_flatMap64 f hf xs]

theorem wordsOf_dig_zeros48 (d : Digest) :
    wordsOf (bytesLE 16 d ++ T3M.zeros 48) = [d.extractLsb' 0 64, d.extractLsb' 64 64, 0, 0, 0, 0, 0, 0] := by
  rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
    show T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl

theorem wordsOf_zeros48_dig (d : Digest) :
    wordsOf (T3M.zeros 48 ++ bytesLE 16 d) = [0, 0, 0, 0, 0, 0, d.extractLsb' 0 64, d.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by rfl), wordsOf_bytesLE16,
    show T3M.zeros 48 = List.replicate (8 * 6) 0 from rfl, wordsOf_replicate_zero]
  rfl

/-! ## A layer region -/

/-- The witness base of layer `lay`'s region. -/
def lBase (lay : Layer) : Nat := ![0x3148, 0x41C8, 0x4E48, 0x5A88] lay

theorem lBase_eq (lay : Layer) : lWM lay = lBase lay + 64 * (height lay - 1) ∧
    lWC lay = lBase lay + 64 * height lay + 64 * (chainCount lay - 1) := by
  fin_cases lay <;> decide

/-- The doublewords of the Merkle block of level `j`. -/
def mkWords (leaf j : Nat) (p : Digest) : List Word :=
  if leaf / 2 ^ j % 2 = 1 then [p.extractLsb' 0 64, p.extractLsb' 64 64, 0, 0, 0, 0, 0, 0]
  else [0, 0, 0, 0, 0, 0, p.extractLsb' 0 64, p.extractLsb' 64 64]

/-- The doublewords of a chain block. -/
def chWords (v : Digest) : List Word := [0, 0, 0, 0, 0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64]

/-- The blocks of a layer region. -/
def layBlocks (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List (List Word) :=
  (List.finRange (height lay)).reverse.map (fun j => mkWords leaf j.val (ls.path j)) ++
    (List.finRange (chainCount lay)).reverse.map (fun i => chWords (ls.values i))

theorem length_flatMap_const {α : Type} (f : α → List UInt8) (c : Nat) (hf : ∀ x, (f x).length = c) :
    ∀ (xs : List α), (xs.flatMap f).length = c * xs.length
  | [] => by simp
  | x :: xs => by rw [List.flatMap_cons, List.length_append, hf, length_flatMap_const f c hf xs]; simp; ring

theorem flatMap_eq_flatten {α β : Type} (f : α → List β) (g : α → List β) (h : ∀ x, f x = g x) :
    ∀ (xs : List α), xs.flatMap f = (xs.map g).flatten
  | [] => rfl
  | x :: xs => by rw [List.flatMap_cons, List.map_cons, List.flatten_cons, h, flatMap_eq_flatten f g h xs]

theorem layerBytes_words (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    wordsOf (layerBytes lay leaf ls) = (layBlocks lay leaf ls).flatten := by
  unfold layerBytes layBlocks
  have hm : ∀ j : Fin (height lay), ((if leaf / 2 ^ j.val % 2 = 1 then bytesLE 16 (ls.path j) ++ T3M.zeros 48
      else T3M.zeros 48 ++ bytesLE 16 (ls.path j))).length = 64 := by
    intro j; split_ifs <;> simp [bytesLE_length, T3M.zeros]
  have hc : ∀ i : Fin (chainCount lay), (T3M.zeros 48 ++ bytesLE 16 (ls.values i)).length = 64 := by
    intro i; simp [bytesLE_length, T3M.zeros]
  rw [wordsOf_append _ _ (by rw [length_flatMap_const _ 64 hm]; omega),
    wordsOf_flatMap64 _ hm, wordsOf_flatMap64 _ hc, List.flatten_append]
  rw [flatMap_eq_flatten _ (fun j => mkWords leaf j.val (ls.path j)) (fun j => by
      unfold mkWords
      split_ifs
      · exact wordsOf_dig_zeros48 _
      · exact wordsOf_zeros48_dig _),
    flatMap_eq_flatten _ (fun i => chWords (ls.values i)) (fun i => wordsOf_zeros48_dig _)]

theorem mk_block (t : MachineState) (B leaf j : Nat) (p : Digest) (hp : DigAt t (B + sideOff leaf j) p)
    (hz : ∀ r < 8, 8 * r ≠ sideOff leaf j → 8 * r ≠ sideOff leaf j + 8 →
      t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = mkWords leaf j p := by
  rw [readWords_eight]
  unfold mkWords
  unfold sideOff at hp hz
  split_ifs at hp hz ⊢ with hb
  · simp only [Nat.add_zero] at hp
    rw [hp.1, hp.2, show B + 16 = B + 8 * 2 by ring, hz 2 (by omega) (by omega) (by omega),
      show B + 24 = B + 8 * 3 by ring, hz 3 (by omega) (by omega) (by omega),
      show B + 32 = B + 8 * 4 by ring, hz 4 (by omega) (by omega) (by omega),
      show B + 40 = B + 8 * 5 by ring, hz 5 (by omega) (by omega) (by omega),
      show B + 48 = B + 8 * 6 by ring, hz 6 (by omega) (by omega) (by omega),
      show B + 56 = B + 8 * 7 by ring, hz 7 (by omega) (by omega) (by omega)]
  · have h0 := hz 0 (by omega) (by omega) (by omega)
    have h1 := hz 1 (by omega) (by omega) (by omega)
    have h2 := hz 2 (by omega) (by omega) (by omega)
    have h3 := hz 3 (by omega) (by omega) (by omega)
    have h4 := hz 4 (by omega) (by omega) (by omega)
    have h5 := hz 5 (by omega) (by omega) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
    rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
      show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hp.1,
      show B + 56 = B + 48 + 8 by ring, hp.2]

theorem ch_block (t : MachineState) (B : Nat) (v : Digest) (hv : DigAt t (B + 48) v)
    (hz : ∀ r < 6, t.getMem (BitVec.ofNat 64 (B + 8 * r)) = 0) :
    t.readWords (BitVec.ofNat 64 B) 8 = chWords v := by
  rw [readWords_eight]
  have h0 := hz 0 (by omega); have h1 := hz 1 (by omega); have h2 := hz 2 (by omega)
  have h3 := hz 3 (by omega); have h4 := hz 4 (by omega); have h5 := hz 5 (by omega)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at h0 h1
  rw [h0, h1, show B + 16 = B + 8 * 2 by ring, h2, show B + 24 = B + 8 * 3 by ring, h3,
    show B + 32 = B + 8 * 4 by ring, h4, show B + 40 = B + 8 * 5 by ring, h5, hv.1,
    show B + 56 = B + 48 + 8 by ring, hv.2]
  rfl

theorem getD_rev_finRange_map {β : Type} (n : Nat) (f : Fin n → β) (d : β) (k : Nat) (hk : k < n) :
    ((List.finRange n).reverse.map f).getD k d = f ⟨n - 1 - k, by omega⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp [show n - 1 - k < n by omega]

/-- **A layer region** from its chain values, path siblings and zero doublewords. -/
theorem layer_words (t : MachineState) (lay : Layer) (leaf : Nat) (ls : LayerSignature lay)
    (hv : ∀ i (h : i < chainCount lay), DigAt t (lWC lay - 64 * i + 48) (ls.values ⟨i, h⟩))
    (hp : ∀ j (h : j < height lay), DigAt t (lWM lay - 64 * j + sideOff leaf j) (ls.path ⟨j, h⟩))
    (hz : ∀ A, lBase lay ≤ A → A < lBase lay + 64 * (height lay + chainCount lay) →
      ¬ RlWit lay leaf (lWC lay) (lWM lay) A → t.getMem (BitVec.ofNat 64 A) = 0) :
    t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (layerBytes lay leaf ls) := by
  obtain ⟨hWM, hWC⟩ := lBase_eq lay
  have hH := height_le lay
  have hH1 : 1 ≤ height lay := by fin_cases lay <;> decide
  have hN1 : 1 ≤ chainCount lay := by fin_cases lay <;> decide
  have hso : ∀ j, sideOff leaf j = 0 ∨ sideOff leaf j = 48 := fun j => by unfold sideOff; split_ifs <;> simp
  rw [layerBytes_words]
  have hlen : (layBlocks lay leaf ls).length = height lay + chainCount lay := by simp [layBlocks]
  have hl8 : ∀ b ∈ layBlocks lay leaf ls, b.length = 8 := by
    intro b hb
    simp only [layBlocks, List.mem_append, List.mem_map] at hb
    rcases hb with ⟨j, _, rfl⟩ | ⟨i, _, rfl⟩
    · unfold mkWords; split_ifs <;> rfl
    · rfl
  have key := readWords_blocks t (layBlocks lay leaf ls) (lBase lay) hl8 (fun k hk => by
    rw [hlen] at hk
    by_cases hkH : k < height lay
    · rw [layBlocks, List.getD_append _ _ _ _ (by simp; omega), getD_rev_finRange_map _ _ _ _ hkH]
      obtain ⟨j, hj⟩ : ∃ j, j = height lay - 1 - k := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWM lay - 64 * j := by omega
      have e : (⟨height lay - 1 - k, by omega⟩ : Fin (height lay)) = ⟨j, by omega⟩ := Fin.ext hj.symm
      rw [hB, e]
      refine mk_block t _ leaf j _ (hp j (by omega)) (fun r hr h1 h2 => hz _ (by omega) (by omega) ?_)
      rintro (⟨i, hi, h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
      · rcases eq_or_ne j' j with rfl | hne
        · omega
        · rcases hso j' with h4 | h4 <;> rw [h4] at h <;> omega
    · rw [layBlocks, List.getD_append_right _ _ _ _ (by simp; omega), List.length_map, List.length_reverse,
        List.length_finRange, getD_rev_finRange_map _ _ _ _ (by omega)]
      obtain ⟨i, hi⟩ : ∃ i, i = chainCount lay - 1 - (k - height lay) := ⟨_, rfl⟩
      have hB : lBase lay + 64 * k = lWC lay - 64 * i := by omega
      have e : (⟨chainCount lay - 1 - (k - height lay), by omega⟩ : Fin (chainCount lay)) = ⟨i, by omega⟩ :=
        Fin.ext hi.symm
      rw [hB, e]
      refine ch_block t _ _ (hv i (by omega)) (fun r hr => hz _ (by omega) (by omega) ?_)
      rintro (⟨i', hi', h | h⟩ | ⟨j', hj', h | h⟩)
      · omega
      · omega
      · rcases hso j' with h4 | h4 <;> omega
      · rcases hso j' with h4 | h4 <;> omega)
  rw [hlen] at key
  exact key

/-! ## The header -/

theorem readLE_two4 (a b : BitVec 32) : readLE (bytesLE 4 a ++ bytesLE 4 b) = a.toNat + 2 ^ 32 * b.toNat := by
  rw [readLE_append, readLE_bytesLE, readLE_bytesLE, bytesLE_length]; norm_num

theorem headerBytes_words (w : Witness) :
    wordsOf (headerBytes w) = [w.signature.rho.extractLsb' 0 64, w.signature.rho.extractLsb' 64 64,
      BitVec.ofNat 64 (w.digestCounter.toNat + 2 ^ 32 * (w.counters 0).toNat),
      BitVec.ofNat 64 ((w.counters 1).toNat + 2 ^ 32 * (w.counters 2).toNat),
      BitVec.ofNat 64 (w.counters 3).toNat, 0, 0, 0] := by
  unfold headerBytes
  have hf : (List.finRange 4).flatMap (fun lay : Layer => bytesLE 4 (w.counters lay)) =
      bytesLE 4 (w.counters 0) ++ bytesLE 4 (w.counters 1) ++ bytesLE 4 (w.counters 2) ++ bytesLE 4 (w.counters 3) := by
    rfl
  have hz : T3M.zeros 28 = List.replicate 4 0 ++ List.replicate (8 * 3) 0 := rfl
  rw [hf, hz]
  simp only [List.append_assoc]
  rw [wordsOf_append _ _ (by rw [bytesLE_length]), wordsOf_bytesLE16,
    ← List.append_assoc (bytesLE 4 w.digestCounter),
    wordsOf_append8 _ _ (by simp [bytesLE_length]), readLE_two4,
    ← List.append_assoc (bytesLE 4 (w.counters 1)),
    wordsOf_append8 _ _ (by simp [bytesLE_length]), readLE_two4,
    ← List.append_assoc (bytesLE 4 (w.counters 3)),
    wordsOf_append8 _ _ (by simp [bytesLE_length]), wordsOf_replicate_zero,
    readLE_append, readLE_bytesLE, readLE_replicate_zero]
  simp

/-! ## The whole witness -/

theorem witList_length_parts (N : HashOutput) (w : Witness) :
    (headerBytes w).length = 64 ∧ (leafBytes w.signature).length = 1024 ∧
      (streamBytes (T3.selections N) w.signature.proof).length = 9480 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [headerBytes, bytesLE_length, T3M.zeros]
  · unfold leafBytes
    rw [List.length_append, length_flatMap_const _ 48 (fun s => by simp [bytesLE_length, T3M.zeros])]
    simp [T3M.zeros]
  · unfold streamBytes
    rw [List.length_take, List.length_append, show (T3M.zeros 9480).length = 9480 from List.length_replicate]
    omega

theorem layerBytes_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytes lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytes
  rw [List.length_append, length_flatMap_const _ 64 (fun j => by split_ifs <;> simp [bytesLE_length, T3M.zeros]),
    length_flatMap_const _ 64 (fun i => by simp [bytesLE_length, T3M.zeros])]
  simp; ring

theorem layerStorage_length' (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerStorage lay leaf ls).length = 64 * (height lay + chainCount lay) := by
  simp [layerStorage, layerBytes_length]

theorem readWords_zero (t : MachineState) (B n : Nat) (hB : B + 8 * n < 2 ^ 64)
    (hz : ∀ j < n, t.getMem (BitVec.ofNat 64 (B + 8 * j)) = 0) :
    t.readWords (BitVec.ofNat 64 B) n = List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n + 1 = n + 1 from rfl, readWords_add, ih (by omega) (fun j hj => hz j (by omega)),
      readWords_one, hz n (by omega)]
    simp [List.replicate_add]

/-- **The witness doublewords** from its parts. -/
theorem witList_words (t : MachineState) (N : HashOutput) (w : Witness)
    (hh : t.readWords (BitVec.ofNat 64 0x800) 8 = wordsOf (headerBytes w))
    (hleaf : t.readWords (BitVec.ofNat 64 0x840) 128 = wordsOf (leafBytes w.signature))
    (hstream : t.readWords (BitVec.ofNat 64 0xC40) 1185 =
      wordsOf (streamBytes (T3.selections N) w.signature.proof))
    (hlay : ∀ lay : Layer, t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
      wordsOf (layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay))) :
    t.readWords (BitVec.ofNat 64 0x800) 3033 = wordsOf (witList N w) := by
  have hstorage : ∀ lay : Layer,
      t.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
        wordsOf (layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) := by
    intro lay
    unfold layerStorage
    exact hlay lay
  obtain ⟨l1, l2, l3⟩ := witList_length_parts N w
  have l4 := fun lay : Layer => layerStorage_length' lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
  have hf : (List.finRange 4).flatMap (fun lay : Layer =>
      layerStorage lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) =
      layerStorage 0 (route (N.toNat % 2 ^ 31) 0).1 (w.signature.layers 0) ++
      layerStorage 1 (route (N.toNat % 2 ^ 31) 1).1 (w.signature.layers 1) ++
      layerStorage 2 (route (N.toNat % 2 ^ 31) 2).1 (w.signature.layers 2) ++
      layerStorage 3 (route (N.toNat % 2 ^ 31) 3).1 (w.signature.layers 3) := by
    simp only [List.finRange_succ, List.finRange_zero, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, List.append_assoc]
    rfl
  unfold witList
  rw [hf]
  simp only [List.append_assoc]
  rw [wordsOf_append _ _ (by rw [l1]), wordsOf_append _ _ (by rw [l2]), wordsOf_append _ _ (by rw [l3]),
    wordsOf_append _ _ (by rw [layerStorage_length']; decide), wordsOf_append _ _ (by rw [layerStorage_length']; decide),
    wordsOf_append _ _ (by rw [layerStorage_length']; decide), ← hh, ← hleaf, ← hstream]
  have h0 := hstorage 0; have h1 := hstorage 1; have h2 := hstorage 2; have h3 := hstorage 3
  rw [← h0, ← h1, ← h2, ← h3]
  simp only [lBase, height, chainCount]
  rw [show (3033 : Nat) = 8 + (128 + (1185 + (528 + (400 + (392 + 392))))) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_add, readWords_add, readWords_add]
  rfl

end SigGolfCandidate.T3M.Expand
