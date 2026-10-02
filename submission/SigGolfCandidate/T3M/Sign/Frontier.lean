import SigGolfCandidate.T3M.Sign.FtsBlocks
import SigGolfCandidate.T3M.Sign.FrontierPure

/-!
# Sign: the multiproof collection of one coordinate (words 278..330)

The heap arena holds node `(ℓ, i)` of the coordinate tree at heap index `hp (ℓ, i) = 2^(11-ℓ) + i`.
`memDig t A` is the digest stored at `A` (two doublewords).

* `desc_loop` : the descent (`fr_desc`, 296..309) from `LEV = l` emits `descL g l` at `PP`;
* `asc_loop` : the ascent (`fr_asc`, 311..327) from `LEV = 0` emits `ascR g e` and stops at the level `e`
  where the next leaf's ancestor is the right sibling (or at 8 for the last leaf);
* `fr_leaves` : the three leaves (`fr_leaf`, 280..330) emit `mf 8 8 [g0, g1, g2]` — Core's `frontier`.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M (lcaLevel heap_eq heap_mod_two two_pow_add_xor_one xor_one_eq div_sib_of_lca
  lca_of_div_sib)

/-! ## Stored digests and heap indices -/

/-- The digest stored at `A` (low doubleword at `A`, high at `A + 8`). -/
def memDig (t : MachineState) (A : Nat) : Digest := t.getMem (BitVec.ofNat 64 (A + 8)) ++ t.getMem (BitVec.ofNat 64 A)

theorem memDig_toNat (t : MachineState) (A : Nat) :
    (memDig t A).toNat = (t.getMem (BitVec.ofNat 64 (A + 8))).toNat * 2 ^ 64 + (t.getMem (BitVec.ofNat 64 A)).toNat := by
  rw [memDig, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (t.getMem (BitVec.ofNat 64 A)).isLt,
    Nat.shiftLeft_eq]

theorem memDig_digAt (t : MachineState) (A : Nat) : DigAt t A (memDig t A) := by
  have h1 := (t.getMem (BitVec.ofNat 64 A)).isLt
  have h2 := (t.getMem (BitVec.ofNat 64 (A + 8))).isLt
  constructor
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_zero]
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, memDig_toNat, Nat.shiftRight_eq_div_pow]
    omega

theorem memDig_eq {t : MachineState} {A : Nat} {d : Digest} (h : DigAt t A d) : memDig t A = d := by
  apply BitVec.eq_of_toNat_eq
  rw [memDig_toNat, h.1, h.2, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have := d.isLt
  omega

theorem memDig_frame {t u : MachineState} {W : Nat → Prop} (hf : Frame t u W) {A : Nat} (hA : A + 8 < 2 ^ 64)
    (h0 : ¬ W A) (h8 : ¬ W (A + 8)) : memDig u A = memDig t A :=
  memDig_eq ((memDig_digAt t A).frame hf hA h0 h8)

/-- Heap index of node `(ℓ, i)` of a coordinate tree. -/
def hp (p : Nat × Nat) : Nat := 2 ^ (11 - p.1) + p.2

/-- The digest of node `p` in the heap arena of `t`. -/
def nodeVal (t : MachineState) (p : Nat × Nat) : Digest := memDig t (FTS + 16 * hp p)

/-- The sibling of the level-`l` ancestor of leaf `g` as a heap index. -/
theorem hp_sib {g l : Nat} (hl : l ≤ 10) : hp (l, g / 2 ^ l ^^^ 1) = (2048 + g) / 2 ^ l ^^^ 1 := by
  unfold hp
  rw [heap_eq (by omega), two_pow_add_xor_one (by omega)]

/-- `PP` holds the values of `L` (nodes of the arena of `t0`). -/
def Emitted (t0 u : MachineState) (pp : Nat) (L : List (Nat × Nat)) : Prop :=
  ∀ i < L.length, DigAt u (pp + 16 * i) (nodeVal t0 (L.getD i (0, 0)))

theorem Emitted.nil (t0 u : MachineState) (pp : Nat) : Emitted t0 u pp [] := fun i hi => by simp at hi

theorem Emitted.append {t0 u : MachineState} {pp : Nat} {L M : List (Nat × Nat)}
    (h1 : Emitted t0 u pp L) (h2 : Emitted t0 u (pp + 16 * L.length) M) : Emitted t0 u pp (L ++ M) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hlt : i < L.length
  · have := h1 i hlt
    rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  · have := h2 (i - L.length) (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
    rw [show pp + 16 * L.length + 16 * (i - L.length) = pp + 16 * i by omega] at this
    exact this

theorem Emitted.frame {t0 u v : MachineState} {pp : Nat} {L : List (Nat × Nat)} {W : Nat → Prop}
    (h : Emitted t0 u pp L) (hf : Frame u v W) (hA : pp + 16 * L.length < 2 ^ 64)
    (hW : ∀ A, pp ≤ A → A < pp + 16 * L.length → ¬ W A) : Emitted t0 v pp L := fun i hi =>
  (h i hi).frame hf (by omega) (hW _ (by omega) (by omega)) (hW _ (by omega) (by omega))

theorem descL_length_le (g : Nat) : ∀ l, (descL g l).length ≤ l
  | 0 => le_rfl
  | l + 1 => by
    simp only [descL, topD, List.length_append]
    have := descL_length_le g l
    split_ifs <;> simp <;> omega

/-- **The descent** (`fr_desc`, 296..309) from `LEV = l ≤ 10` emits `descL g l` at `PP` and ends at
`fr_asc_init` (310). -/
theorem desc_loop (t0 : MachineState) (g : Nat) (hg : g < 2048) :
    ∀ (l : Nat), l ≤ 10 → ∀ (t : MachineState) (pp : Nat),
    t.pc = pcOf 296 → t.getReg .x22 = BitVec.ofNat 64 l → t.getReg .x20 = BitVec.ofNat 64 (2048 + g) →
    t.getReg .x2 = BitVec.ofNat 64 FTS → t.getReg .x16 = BitVec.ofNat 64 pp →
    pp % 8 = 0 → pp + 16 * l ≤ FTS →
    (∀ A, FTS ≤ A → A < FTS + 65536 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
    ∃ u k, Steps image t k k u ∧ k ≤ 14 * l + 1 ∧ u.pc = pcOf 310 ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * (descL g l).length) ∧
      Emitted t0 u pp (descL g l) ∧ RegsExcept t u [.x6, .x7, .x16, .x22, .x28] ∧
      Frame t u (fun A => pp ≤ A ∧ A < pp + 16 * (descL g l).length)
  | 0, _, t, pp, hpc, h22, _, _, h16, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk296_spec t hpc 0 (by norm_num) h22
    rw [if_pos rfl] at upc
    exact ⟨u, 1, st, by omega, upc, by rw [ur.get (by simp), h16]; simp [descL], Emitted.nil _ _ _,
      ur.mono (by simp), uf.mono (fun _ _ h => h.elim)⟩
  | l + 1, hl, t, pp, hpc, h22, h20, h2, h16, hpp8, hppl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk296_spec t hpc (l + 1) (by omega) h22
    rw [if_neg (by omega)] at t1pc
    obtain ⟨t2, st2, t2pc, t2x22, t2x6, t2r, t2f⟩ := blk297_spec t1 t1pc l (2048 + g) (by omega) (by omega)
      (by rw [t1r.get (by simp)]; exact h22) (by rw [t1r.get (by simp)]; exact h20)
    have hbit : (2048 + g) / 2 ^ l % 2 = g / 2 ^ l % 2 := heap_mod_two (by omega)
    have r02 : RegsExcept t t2 [.x6, .x7, .x22] := (t1r.trans t2r).mono (by simp)
    have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun _ _ h => by simp_all)
    have h2heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t2.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
      fun A h1 h2 => (f02.get (by sgo) (fun h => h)).trans (hheap A h1 h2)
    by_cases hb : (2048 + g) / 2 ^ l % 2 = 0
    · -- a left child: nothing to emit at this level
      rw [if_pos hb] at t2pc
      obtain ⟨u, k, st, hk, upc, u16, uem, ur, uf⟩ := desc_loop t0 g hg l (by omega) t2 pp t2pc t2x22
        (by rw [r02.get (by simp)]; exact h20) (by rw [r02.get (by simp)]; exact h2)
        (by rw [r02.get (by simp)]; exact h16) hpp8 (by omega) h2heap
      have hd : descL g (l + 1) = descL g l := by
        simp only [descL, topD]; rw [if_neg (by omega)]; simp
      rw [hd]
      exact ⟨u, 1 + (4 + k), st1.trans (st2.trans st), by omega, upc, u16, uem,
        (r02.trans ur).mono (by simp), (f02.trans uf).mono (fun _ _ h => by rcases h with h | h; exact h.elim; exact h)⟩
    · -- a right child: emit the left sibling
      rw [if_neg hb] at t2pc
      have hv : (2048 + g) / 2 ^ l < 4096 := by
        have := Nat.div_le_self (2048 + g) (2 ^ l); omega
      obtain ⟨t3, st3, t3pc, t3x16, m0, m8, t3r, t3f⟩ := blk301_spec t2 t2pc ((2048 + g) / 2 ^ l) pp hv
        (by sgo) hpp8 t2x6 (by rw [r02.get (by simp)]; exact h2) (by rw [r02.get (by simp)]; exact h16)
      have h3heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t3.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
        fun A h1 h2 => (t3f.get (by sgo) (by sgo)).trans (h2heap A h1 h2)
      obtain ⟨u, k, st, hk, upc, u16, uem, ur, uf⟩ := desc_loop t0 g hg l (by omega) t3 (pp + 16) t3pc
        (by rw [t3r.get (by simp)]; exact t2x22) (by rw [t3r.get (by simp), r02.get (by simp)]; exact h20)
        (by rw [t3r.get (by simp), r02.get (by simp)]; exact h2) t3x16 (by omega) (by omega) h3heap
      have hd : descL g (l + 1) = [(l, g / 2 ^ l ^^^ 1)] ++ descL g l := by
        simp only [descL, topD]; rw [if_pos (by omega)]
      have hxv : (2048 + g) / 2 ^ l ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hv (by norm_num)
      have hfirst : DigAt t3 pp (nodeVal t0 (l, g / 2 ^ l ^^^ 1)) := by
        unfold nodeVal
        rw [hp_sib (by omega)]
        refine ⟨m0.trans ?_, m8.trans ?_⟩
        · rw [h2heap _ (by sgo) (by sgo)]
          exact (memDig_digAt t0 _).1
        · rw [h2heap _ (by sgo) (by sgo)]
          exact (memDig_digAt t0 _).2
      rw [hd]
      refine ⟨u, 1 + (4 + (9 + k)), st1.trans (st2.trans (st3.trans st)), by omega, upc, ?_, ?_, ?_, ?_⟩
      · rw [u16]; simp only [List.length_append, List.length_singleton]; congr 1; omega
      · refine Emitted.append ?_ ?_
        · intro i hi
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          simpa using hfirst.frame uf (by sgo) (by omega) (by omega)
        · simpa using uem
      · exact ((r02.trans t3r).trans ur).mono (by simp)
      · refine ((f02.trans t3f).trans uf).mono (fun A _ h => ?_)
        simp only [List.length_append, List.length_singleton]
        rcases h with (h | h) | h
        · exact h.elim
        · omega
        · omega

/-- Right siblings of the path of `g` at the levels `l .. l + n - 1` (the ascent from level `l`). -/
def ascFrom (g l : Nat) : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => topA g l ++ ascFrom g (l + 1) n

theorem ascFrom_succ_right (g : Nat) : ∀ n l, ascFrom g l (n + 1) = ascFrom g l n ++ topA g (l + n)
  | 0, l => by simp [ascFrom]
  | n + 1, l => by
    rw [ascFrom, ascFrom_succ_right g n (l + 1), ascFrom, List.append_assoc, show l + 1 + n = l + (n + 1) by ring]

theorem ascR_eq_ascFrom (g : Nat) : ∀ e, ascR g e = ascFrom g 0 e
  | 0 => rfl
  | e + 1 => by rw [ascR, ascR_eq_ascFrom g e, ascFrom_succ_right, Nat.zero_add]

theorem ascFrom_length_le (g : Nat) : ∀ n l, (ascFrom g l n).length ≤ n
  | 0, _ => le_rfl
  | n + 1, l => by
    simp only [ascFrom, topA, List.length_append]
    have := ascFrom_length_le g n (l + 1)
    split_ifs <;> simp <;> omega

/-- **The ascent** (`fr_asc`, 311..327) from `LEV = l` to the stop level `e = l + n ≤ 8` (the next leaf's
ancestor is the right sibling at `e`, or `e = 8`): emits `ascFrom g l n` and ends at `fr_asc_done` (328). -/
theorem asc_loop (t0 : MachineState) (g nxt e : Nat) (hg : g < 2048) (he : e ≤ 8) (hnxt : nxt < 2 ^ 64)
    (hne : ∀ l' < e, (2048 + g) / 2 ^ l' % 2 = 0 → nxt / 2 ^ l' ≠ (2048 + g) / 2 ^ l' ^^^ 1)
    (hend : e = 8 ∨ ((2048 + g) / 2 ^ e % 2 = 0 ∧ nxt / 2 ^ e = (2048 + g) / 2 ^ e ^^^ 1)) :
    ∀ (n l : Nat), l + n = e → ∀ (t : MachineState) (pp : Nat),
    t.pc = pcOf 311 → t.getReg .x22 = BitVec.ofNat 64 l → t.getReg .x20 = BitVec.ofNat 64 (2048 + g) →
    t.getReg .x21 = BitVec.ofNat 64 nxt → t.getReg .x2 = BitVec.ofNat 64 FTS → t.getReg .x16 = BitVec.ofNat 64 pp →
    pp % 8 = 0 → pp + 16 * n ≤ FTS →
    (∀ A, FTS ≤ A → A < FTS + 65536 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
    ∃ u k, Steps image t k k u ∧ k ≤ 17 * n + 8 ∧ u.pc = pcOf 328 ∧ u.getReg .x22 = BitVec.ofNat 64 e ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * (ascFrom g l n).length) ∧
      Emitted t0 u pp (ascFrom g l n) ∧ RegsExcept t u [.x6, .x7, .x16, .x22, .x28] ∧
      Frame t u (fun A => pp ≤ A ∧ A < pp + 16 * (ascFrom g l n).length)
  | 0, l, hle, t, pp, hpc, h22, h20, h21, h2, h16, hpp8, hppl, hheap => by
    have hl : l = e := by omega
    subst hl
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk311_spec t hpc l (by omega) h22
    by_cases h8 : ¬ l < 8
    · rw [if_neg h8] at t1pc
      exact ⟨t1, 2, st1, by omega, t1pc, by rw [t1r.get (by simp)]; exact h22,
        by rw [t1r.get (by simp), h16]; simp [ascFrom], Emitted.nil _ _ _, t1r.mono (by simp),
        t1f.mono (fun _ _ h => h.elim)⟩
    · have hl8 : l < 8 := by omega
      obtain ⟨hb, hs⟩ : (2048 + l * 0 + g) / 2 ^ l % 2 = 0 ∧ nxt / 2 ^ l = (2048 + g) / 2 ^ l ^^^ 1 := by
        rcases hend with h | h
        · omega
        · simpa using h
      simp only [Nat.mul_zero, Nat.add_zero] at hb
      rw [if_pos hl8] at t1pc
      obtain ⟨t2, st2, t2pc, t2x6, t2r, t2f⟩ := blk313_spec t1 t1pc l (2048 + g) (by omega) (by omega)
        (by rw [t1r.get (by simp)]; exact h22) (by rw [t1r.get (by simp)]; exact h20)
      rw [if_neg (by omega)] at t2pc
      have hv : (2048 + g) / 2 ^ l < 2 ^ 64 := by have := Nat.div_le_self (2048 + g) (2 ^ l); omega
      obtain ⟨t3, st3, t3pc, t3x6, t3r, t3f⟩ := blk316_spec t2 t2pc l ((2048 + g) / 2 ^ l) nxt (by omega) hv hnxt
        (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h22) t2x6
        (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h21)
      rw [if_pos hs] at t3pc
      refine ⟨t3, 2 + (3 + 3), st1.trans (st2.trans st3), by omega, t3pc, ?_, ?_, Emitted.nil _ _ _, ?_, ?_⟩
      · rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp)]; exact h22
      · rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), h16]; simp [ascFrom]
      · exact ((t1r.trans t2r).trans t3r).mono (by simp)
      · exact ((t1f.trans t2f).trans t3f).mono (fun _ _ h => by simp_all)
  | n + 1, l, hle, t, pp, hpc, h22, h20, h21, h2, h16, hpp8, hppl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk311_spec t hpc l (by omega) h22
    rw [if_pos (by omega)] at t1pc
    obtain ⟨t2, st2, t2pc, t2x6, t2r, t2f⟩ := blk313_spec t1 t1pc l (2048 + g) (by omega) (by omega)
      (by rw [t1r.get (by simp)]; exact h22) (by rw [t1r.get (by simp)]; exact h20)
    have hbit : (2048 + g) / 2 ^ l % 2 = g / 2 ^ l % 2 := heap_mod_two (by omega)
    have r02 : RegsExcept t t2 [.x6, .x7] := (t1r.trans t2r).mono (by simp)
    have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun _ _ h => by simp_all)
    by_cases hb : (2048 + g) / 2 ^ l % 2 = 1
    · -- a right child: nothing to emit, LEV += 1
      rw [if_pos hb] at t2pc
      obtain ⟨t3, st3, t3pc, t3x22, t3r, t3f⟩ := blk326_spec t2 t2pc l
        (by rw [r02.get (by simp)]; exact h22)
      have h3heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t3.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
        fun A h1 h2 => ((f02.trans t3f).get (by sgo) (fun h => by simp_all)).trans (hheap A h1 h2)
      obtain ⟨u, k, st, hk, upc, u22, u16, uem, ur, uf⟩ := asc_loop t0 g nxt e hg he hnxt hne hend n (l + 1)
        (by omega) t3 pp t3pc t3x22 (by rw [t3r.get (by simp), r02.get (by simp)]; exact h20)
        (by rw [t3r.get (by simp), r02.get (by simp)]; exact h21) (by rw [t3r.get (by simp), r02.get (by simp)]; exact h2)
        (by rw [t3r.get (by simp), r02.get (by simp)]; exact h16) hpp8 (by omega) h3heap
      have hd : ascFrom g l (n + 1) = ascFrom g (l + 1) n := by
        simp only [ascFrom, topA]; rw [if_neg (by omega)]; simp
      rw [hd]
      exact ⟨u, 2 + (3 + (2 + k)), st1.trans (st2.trans (st3.trans st)), by omega, upc, u22, u16, uem,
        ((r02.trans t3r).trans ur).mono (by simp),
        ((f02.trans t3f).trans uf).mono (fun _ _ h => by rcases h with (h | h) | h <;> simp_all)⟩
    · -- a left child below the stop level: emit the right sibling
      rw [if_neg hb] at t2pc
      have hb0 : (2048 + g) / 2 ^ l % 2 = 0 := by omega
      have hv : (2048 + g) / 2 ^ l < 4096 := by have := Nat.div_le_self (2048 + g) (2 ^ l); omega
      obtain ⟨t3, st3, t3pc, t3x6, t3r, t3f⟩ := blk316_spec t2 t2pc l ((2048 + g) / 2 ^ l) nxt (by omega)
        (by omega) hnxt (by rw [r02.get (by simp)]; exact h22) t2x6 (by rw [r02.get (by simp)]; exact h21)
      rw [if_neg (hne l (by omega) hb0)] at t3pc
      have hxv : (2048 + g) / 2 ^ l ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hv (by norm_num)
      obtain ⟨t4, st4, t4pc, t4x16, m0, m8, t4r, t4f⟩ := blk319_spec t3 t3pc ((2048 + g) / 2 ^ l ^^^ 1) pp hxv
        (by sgo) hpp8 t3x6 (by rw [t3r.get (by simp), r02.get (by simp)]; exact h2)
        (by rw [t3r.get (by simp), r02.get (by simp)]; exact h16)
      obtain ⟨t5, st5, t5pc, t5x22, t5r, t5f⟩ := blk326_spec t4 t4pc l
        (by rw [t4r.get (by simp), t3r.get (by simp), r02.get (by simp)]; exact h22)
      have f03 : Frame t t3 (fun _ => False) := (f02.trans t3f).mono (fun _ _ h => by simp_all)
      have h3heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t3.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
        fun A h1 h2 => (f03.get (by sgo) (fun h => h)).trans (hheap A h1 h2)
      have f35 : Frame t3 t5 (fun A => A = pp ∨ A = pp + 8) := (t4f.trans t5f).mono (fun _ _ h => by
        rcases h with h | h; exact h; exact h.elim)
      have h5heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t5.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
        fun A h1 h2 => (f35.get (by sgo) (by sgo)).trans (h3heap A h1 h2)
      have r35 : RegsExcept t3 t5 [.x6, .x7, .x16, .x28, .x22] := (t4r.trans t5r).mono (by simp)
      obtain ⟨u, k, st, hk, upc, u22, u16, uem, ur, uf⟩ := asc_loop t0 g nxt e hg he hnxt hne hend n (l + 1)
        (by omega) t5 (pp + 16) t5pc t5x22
        (by rw [r35.get (by simp), t3r.get (by simp), r02.get (by simp)]; exact h20)
        (by rw [r35.get (by simp), t3r.get (by simp), r02.get (by simp)]; exact h21)
        (by rw [r35.get (by simp), t3r.get (by simp), r02.get (by simp)]; exact h2)
        (by rw [t5r.get (by simp)]; exact t4x16) (by omega) (by omega) h5heap
      have hd : ascFrom g l (n + 1) = [(l, g / 2 ^ l ^^^ 1)] ++ ascFrom g (l + 1) n := by
        simp only [ascFrom, topA]; rw [if_pos (by omega)]
      have hfirst : DigAt t5 pp (nodeVal t0 (l, g / 2 ^ l ^^^ 1)) := by
        unfold nodeVal
        rw [hp_sib (by omega)]
        refine ⟨?_, ?_⟩
        · rw [t5f.get (by sgo) (fun h => h.elim), m0, h3heap _ (by sgo) (by sgo)]
          exact (memDig_digAt t0 _).1
        · rw [t5f.get (by sgo) (fun h => h.elim), m8, h3heap _ (by sgo) (by sgo)]
          exact (memDig_digAt t0 _).2
      rw [hd]
      refine ⟨u, 2 + (3 + (3 + (7 + (2 + k)))), st1.trans (st2.trans (st3.trans (st4.trans (st5.trans st)))),
        by omega, upc, u22, ?_, ?_, ?_, ?_⟩
      · rw [u16]; simp only [List.length_append, List.length_singleton]; congr 1; omega
      · refine Emitted.append ?_ ?_
        · intro i hi
          simp only [List.length_singleton] at hi
          have hi0 : i = 0 := by omega
          subst hi0
          simpa using hfirst.frame uf (by sgo) (by omega) (by omega)
        · simpa using uem
      · exact (((r02.trans t3r).trans r35).trans ur).mono (by simp)
      · refine (((f02.trans t3f).trans f35).trans uf).mono (fun A _ h => ?_)
        simp only [List.length_append, List.length_singleton]
        rcases h with ((h | h) | h) | h
        · exact h.elim
        · exact h.elim
        · omega
        · omega

/-- **One leaf of the walk** (`fr_leaf`, 280..330): leaf `g` (row entry `j`), next leaf ancestor test value
`nxt`, descent from `DSTART = s`, ascent stopping at `e`; emits `descL g s ++ ascR g e`, sets `DSTART = e`,
`J = j + 1`. -/
theorem fr_leaf_step (t0 : MachineState) (j g nxt s e rowp pp : Nat) (hj : j < 3) (hg : g < 2048)
    (hs : s ≤ 8) (he : e ≤ 8) (hnxt : nxt < 2 ^ 64)
    (hne : ∀ l' < e, (2048 + g) / 2 ^ l' % 2 = 0 → nxt / 2 ^ l' ≠ (2048 + g) / 2 ^ l' ^^^ 1)
    (hend : e = 8 ∨ ((2048 + g) / 2 ^ e % 2 = 0 ∧ nxt / 2 ^ e = (2048 + g) / 2 ^ e ^^^ 1))
    (hrow : rowp + 8 * j + 16 ≤ 2 ^ 24) (hrow8 : rowp % 8 = 0)
    (t : MachineState) (hpc : t.pc = pcOf 280) (h19 : t.getReg .x19 = BitVec.ofNat 64 j)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 s) (h25 : t.getReg .x25 = BitVec.ofNat 64 rowp)
    (h2 : t.getReg .x2 = BitVec.ofNat 64 FTS) (h16 : t.getReg .x16 = BitVec.ofNat 64 pp)
    (hg0 : t.getMem (BitVec.ofNat 64 (rowp + 8 * j)) = BitVec.ofNat 64 g)
    (hnx0 : j = 2 → nxt = 0)
    (hnx1 : j ≠ 2 → ∃ g', g' < 2048 ∧ nxt = 2048 + g' ∧ t.getMem (BitVec.ofNat 64 (rowp + 8 * j + 8)) = BitVec.ofNat 64 g')
    (hpp8 : pp % 8 = 0) (hppl : pp + 16 * 16 ≤ FTS)
    (hheap : ∀ A, FTS ≤ A → A < FTS + 65536 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) :
    ∃ u k, Steps image t k k u ∧ k ≤ 300 ∧ u.pc = pcOf 280 ∧ u.getReg .x19 = BitVec.ofNat 64 (j + 1) ∧
      u.getReg .x23 = BitVec.ofNat 64 e ∧ u.getReg .x20 = BitVec.ofNat 64 (2048 + g) ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * (descL g s ++ ascR g e).length) ∧
      Emitted t0 u pp (descL g s ++ ascR g e) ∧ (descL g s ++ ascR g e).length ≤ 16 ∧
      RegsExcept t u [.x6, .x7, .x16, .x19, .x20, .x21, .x22, .x23, .x28] ∧
      Frame t u (fun A => pp ≤ A ∧ A < pp + 16 * (descL g s ++ ascR g e).length) := by
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk280_spec t hpc j (by omega) h19
  rw [if_pos hj] at t1pc
  obtain ⟨t2, st2, t2pc, t2x20, t2x21, t2x6, t2r, t2f⟩ := blk282_spec t1 t1pc j rowp g hrow hrow8 hg hj
    (by rw [t1r.get (by simp)]; exact h19) (by rw [t1r.get (by simp)]; exact h25)
    (by rw [t1f.get (by omega) (fun h => h)]; exact hg0)
  have f02 : Frame t t2 (fun _ => False) := (t1f.trans t2f).mono (fun _ _ h => by simp_all)
  have r02 : RegsExcept t t2 [.x6, .x7, .x20, .x21] := (t1r.trans t2r).mono (by simp)
  -- the next-leaf value: at `fr_nonext` (295) with `NXT = nxt`
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x21, t3r, t3f⟩ : ∃ t3 k3, Steps image t2 k3 k3 t3 ∧ k3 ≤ 4 ∧
      t3.pc = pcOf 295 ∧ t3.getReg .x21 = BitVec.ofNat 64 nxt ∧ RegsExcept t2 t3 [.x7, .x21] ∧
      Frame t2 t3 (fun _ => False) := by
    by_cases hj2 : j = 2
    · rw [if_pos hj2] at t2pc
      exact ⟨t2, 0, Steps.refl _, by omega, t2pc, by rw [t2x21, hnx0 hj2], RegsExcept.refl _ _, Frame.refl _ _⟩
    · obtain ⟨g', hg', hn, hgm⟩ := hnx1 hj2
      rw [if_neg hj2] at t2pc
      obtain ⟨t3, st3, t3pc, t3x21, t3r, t3f⟩ := blk291_spec t2 t2pc (rowp + 8 * j) g' (by omega) (by omega) hg'
        t2x6 (by rw [f02.get (by omega) (fun h => h)]; exact hgm)
      exact ⟨t3, 4, st3, le_rfl, t3pc, by rw [t3x21, hn], t3r, t3f⟩
  obtain ⟨t4, st4, t4pc, t4x22, t4r, t4f⟩ := blk295_spec t3 t3pc
  have r04 : RegsExcept t t4 [.x6, .x7, .x20, .x21, .x7, .x21, .x22] := ((r02.trans t3r).trans t4r).mono (by simp)
  have f04 : Frame t t4 (fun _ => False) := ((f02.trans t3f).trans t4f).mono (fun _ _ h => by simp_all)
  have h4heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t4.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => (f04.get (by sgo) (fun h => h)).trans (hheap A h1 h2)
  have h4x20 : t4.getReg .x20 = BitVec.ofNat 64 (2048 + g) := by
    rw [t4r.get (by simp), t3r.get (by simp)]; exact t2x20
  -- the descent
  obtain ⟨t5, k5, st5, hk5, t5pc, t5x16, t5em, t5r, t5f⟩ := desc_loop t0 g hg s (by omega) t4 pp t4pc
    (by rw [t4x22, t3r.get (by simp), r02.get (by simp)]; exact h23) h4x20
    (by rw [r04.get (by simp)]; exact h2) (by rw [r04.get (by simp)]; exact h16) hpp8 (by omega) h4heap
  have hdl := descL_length_le g s
  obtain ⟨t6, st6, t6pc, t6x22, t6r, t6f⟩ := blk310_spec t5 t5pc
  have h6heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t6.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => ((t5f.trans t6f).get (by sgo) (fun h => by rcases h with h | h; sgo; exact h.elim)).trans
      (h4heap A h1 h2)
  -- the ascent
  obtain ⟨t7, k7, st7, hk7, t7pc, t7x22, t7x16, t7em, t7r, t7f⟩ := asc_loop t0 g nxt e hg he hnxt hne hend e 0
    (by omega) t6 (pp + 16 * (descL g s).length) t6pc t6x22
    (by rw [t6r.get (by simp), t5r.get (by simp)]; exact h4x20)
    (by rw [t6r.get (by simp), t5r.get (by simp), t4r.get (by simp)]; exact t3x21)
    (by rw [t6r.get (by simp), t5r.get (by simp), r04.get (by simp)]; exact h2)
    (by rw [t6r.get (by simp)]; exact t5x16) (by omega) (by omega) h6heap
  have hal := ascFrom_length_le g e 0
  obtain ⟨t8, st8, t8pc, t8x23, t8x19, t8r, t8f⟩ := blk328_spec t7 t7pc j
    (by rw [t7r.get (by simp), t6r.get (by simp), t5r.get (by simp), r04.get (by simp)]; exact h19)
  rw [← ascR_eq_ascFrom] at t7x16 t7em t7f hal
  refine ⟨t8, 2 + (9 + (k3 + (1 + (k5 + (1 + (k7 + 3)))))),
    st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6.trans (st7.trans st8)))))), by omega, t8pc, t8x19,
    by rw [t8x23]; exact t7x22, ?_, ?_, ?_, by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [t8r.get (by simp), t7r.get (by simp), t6r.get (by simp), t5r.get (by simp)]; exact h4x20
  · rw [t8r.get (by simp), t7x16]; simp only [List.length_append]; congr 1; ring
  · have e6 : Emitted t0 t6 pp (descL g s) := t5em.frame t6f (by sgo) (fun _ _ _ h => h)
    refine Emitted.append ((e6.frame t7f (by sgo) (fun A h1 h2 h => by omega)).frame t8f (by sgo)
      (fun _ _ _ h => h)) ?_
    exact t7em.frame t8f (by sgo) (fun _ _ _ h => h)
  · exact (((((r04.trans t5r).trans t6r).trans t7r).trans t8r)).mono (by simp)
  · refine ((((f04.trans t5f).trans t6f).trans t7f).trans t8f).mono (fun A _ h => ?_)
    simp only [List.length_append]
    rcases h with ((((h | h) | h) | h) | h)
    · exact h.elim
    · omega
    · exact h.elim
    · omega
    · exact h.elim

open SigGolfCandidate.T3M (heap_sib_inv heap_sib lcaLevel_pos div_eq_iff_lca) in
/-- The stop test of the ascent of `g` with next leaf `g' > g` (LCA level `d ≤ 8`): the walk stops exactly at
level `d - 1`. -/
theorem stop_facts {g g' : Nat} (hg : g < 2048) (hg' : g' < 2048) (hlt : g < g') (hd : lcaLevel g g' ≤ 8) :
    (∀ l' < lcaLevel g g' - 1, (2048 + g) / 2 ^ l' % 2 = 0 →
      (2048 + g') / 2 ^ l' ≠ (2048 + g) / 2 ^ l' ^^^ 1) ∧
    ((2048 + g) / 2 ^ (lcaLevel g g' - 1) % 2 = 0 ∧
      (2048 + g') / 2 ^ (lcaLevel g g' - 1) = (2048 + g) / 2 ^ (lcaLevel g g' - 1) ^^^ 1) := by
  have hpos := lcaLevel_pos g g'
  set e := lcaLevel g g' - 1 with he
  have hle : lcaLevel g g' = e + 1 := by omega
  refine ⟨fun l' hl' _ heq => ?_, ?_, ?_⟩
  · have h2 : 2 ≤ (2048 + g') / 2 ^ l' := by
      rw [heap_eq (by omega)]
      have : 2 ≤ 2 ^ (11 - l') := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (11 - l') := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact le_trans this (Nat.le_add_right _ _)
    obtain ⟨_, _, hl⟩ := heap_sib_inv hg hg' heq.symm h2
    omega
  · rw [heap_mod_two (by omega)]
    have hs := div_sib_of_lca (show g ≠ g' by omega) hle
    have hmono : g / 2 ^ e ≤ g' / 2 ^ e := Nat.div_le_div_right hlt.le
    have hx := xor_one_eq (g / 2 ^ e)
    rw [hs] at hmono
    omega
  · exact (heap_sib (show g ≠ g' by omega) (by omega) hle).symm

/-- The last leaf's ascent never stops before level 8 (`NXT = 0`). -/
theorem stop_last {g : Nat} (hg : g < 2048) :
    ∀ l' < 8, (2048 + g) / 2 ^ l' % 2 = 0 → 0 / 2 ^ l' ≠ (2048 + g) / 2 ^ l' ^^^ 1 := by
  intro l' hl' _ h
  have h2 : 2 ≤ (2048 + g) / 2 ^ l' := by
    rw [heap_eq (by omega)]
    have : 2 ≤ 2 ^ (11 - l') := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (11 - l') := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans this (Nat.le_add_right _ _)
  have hx := xor_one_eq ((2048 + g) / 2 ^ l')
  rw [Nat.zero_div] at h
  omega

/-- **The multiproof walk of one coordinate** (`fts_sec_done` .. `fr_done`, words 278..330): for the sorted
row `g0 < g1 < g2` (LCA levels ≤ 8) the machine emits `mf 8 8 [g0, g1, g2]` at `PP`. -/
theorem fr_three (t0 t : MachineState) (g0 g1 g2 rowp pp : Nat) (hg2 : g2 < 2048) (h01 : g0 < g1) (h12 : g1 < g2)
    (hl01 : lcaLevel g0 g1 ≤ 8) (hl12 : lcaLevel g1 g2 ≤ 8)
    (hrow : rowp + 32 ≤ 2 ^ 24) (hrow8 : rowp % 8 = 0)
    (hpc : t.pc = pcOf 278) (h25 : t.getReg .x25 = BitVec.ofNat 64 rowp)
    (h2 : t.getReg .x2 = BitVec.ofNat 64 FTS) (h16 : t.getReg .x16 = BitVec.ofNat 64 pp)
    (hm0 : t.getMem (BitVec.ofNat 64 rowp) = BitVec.ofNat 64 g0)
    (hm1 : t.getMem (BitVec.ofNat 64 (rowp + 8)) = BitVec.ofNat 64 g1)
    (hm2 : t.getMem (BitVec.ofNat 64 (rowp + 16)) = BitVec.ofNat 64 g2)
    (hpp8 : pp % 8 = 0) (hppl : pp + 16 * 48 ≤ FTS) (hdisj : pp + 16 * 48 ≤ rowp)
    (hheap : ∀ A, FTS ≤ A → A < FTS + 65536 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) :
    ∃ u k, Steps image t k k u ∧ k ≤ 1000 ∧ u.pc = pcOf 331 ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * (mf 8 8 [g0, g1, g2]).length) ∧
      u.getReg .x20 = BitVec.ofNat 64 (2048 + g2) ∧
      Emitted t0 u pp (mf 8 8 [g0, g1, g2]) ∧ (mf 8 8 [g0, g1, g2]).length ≤ 48 ∧
      RegsExcept t u [.x6, .x7, .x16, .x19, .x20, .x21, .x22, .x23, .x28] ∧
      Frame t u (fun A => pp ≤ A ∧ A < pp + 16 * (mf 8 8 [g0, g1, g2]).length) := by
  have hpos01 := SigGolfCandidate.T3M.lcaLevel_pos g0 g1
  have hpos12 := SigGolfCandidate.T3M.lcaLevel_pos g1 g2
  set e0 := lcaLevel g0 g1 - 1 with he0
  set e1 := lcaLevel g1 g2 - 1 with he1
  obtain ⟨t1, st1, t1pc, t1x23, t1x19, t1r, t1f⟩ := blk278_spec t hpc
  have hheap0 : ∀ A, FTS ≤ A → A < FTS + 65536 → t1.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => (t1f.get (by sgo) (fun h => h)).trans (hheap A h1 h2')
  obtain ⟨s01, s01e⟩ := stop_facts (by omega) (by omega) h01 hl01
  obtain ⟨s12, s12e⟩ := stop_facts (by omega) (by omega) h12 hl12
  -- leaf 0
  obtain ⟨u0, k0, st0, hk0, u0pc, u0x19, u0x23, u0x20, u0x16, u0em, u0len, u0r, u0f⟩ :=
    fr_leaf_step t0 0 g0 (2048 + g1) 8 e0 rowp pp (by norm_num) (by omega) le_rfl (by omega) (by omega)
      s01 (Or.inr s01e) (by omega) hrow8 t1 t1pc t1x19 t1x23 (by rw [t1r.get (by simp)]; exact h25)
      (by rw [t1r.get (by simp)]; exact h2) (by rw [t1r.get (by simp)]; exact h16)
      (by rw [t1f.get (by omega) (fun h => h)]; simpa using hm0) (fun h => absurd h (by norm_num))
      (fun _ => ⟨g1, by omega, rfl, by rw [t1f.get (by omega) (fun h => h)]; simpa using hm1⟩)
      hpp8 (by omega) hheap0
  set L0 := descL g0 8 ++ ascR g0 e0 with hL0
  have hu0row : ∀ A, rowp ≤ A → A < rowp + 24 → u0.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => (u0f.get (by omega) (by omega)).trans (t1f.get (by omega) (fun h => h))
  have hu0heap : ∀ A, FTS ≤ A → A < FTS + 65536 → u0.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => (u0f.get (by sgo) (by sgo)).trans (hheap0 A h1 h2')
  -- leaf 1
  obtain ⟨u1, k1, st1', hk1, u1pc, u1x19, u1x23, u1x20, u1x16, u1em, u1len, u1r, u1f⟩ :=
    fr_leaf_step t0 1 g1 (2048 + g2) e0 e1 rowp (pp + 16 * L0.length) (by norm_num) (by omega) (by omega)
      (by omega) (by omega) s12 (Or.inr s12e) (by omega) hrow8 u0 u0pc u0x19 u0x23
      (by rw [u0r.get (by simp), t1r.get (by simp)]; exact h25)
      (by rw [u0r.get (by simp), t1r.get (by simp)]; exact h2) u0x16
      (by rw [hu0row _ (by omega) (by omega)]; simpa using hm1) (fun h => absurd h (by norm_num))
      (fun _ => ⟨g2, hg2, rfl, by rw [hu0row _ (by omega) (by omega)]; simpa using hm2⟩)
      (by omega) (by omega) hu0heap
  set L1 := descL g1 e0 ++ ascR g1 e1 with hL1
  have hu1row : ∀ A, rowp ≤ A → A < rowp + 24 → u1.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => (u1f.get (by omega) (by omega)).trans (hu0row A h1 h2')
  have hu1heap : ∀ A, FTS ≤ A → A < FTS + 65536 → u1.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => (u1f.get (by sgo) (by sgo)).trans (hu0heap A h1 h2')
  -- leaf 2
  obtain ⟨u2, k2, st2', hk2, u2pc, u2x19, u2x23, u2x20, u2x16, u2em, u2len, u2r, u2f⟩ :=
    fr_leaf_step t0 2 g2 0 e1 8 rowp (pp + 16 * L0.length + 16 * L1.length) (by norm_num) hg2 (by omega)
      le_rfl (by norm_num) (stop_last hg2) (Or.inl rfl) (by omega) hrow8 u1 u1pc u1x19 u1x23
      (by rw [u1r.get (by simp), u0r.get (by simp), t1r.get (by simp)]; exact h25)
      (by rw [u1r.get (by simp), u0r.get (by simp), t1r.get (by simp)]; exact h2) u1x16
      (by rw [hu1row _ (by omega) (by omega)]; simpa using hm2) (fun _ => rfl) (fun h => absurd rfl h)
      (by omega) (by omega) hu1heap
  set L2 := descL g2 e1 ++ ascR g2 8 with hL2
  obtain ⟨u3, st3, u3pc, u3r, u3f⟩ := blk280_spec u2 u2pc 3 (by norm_num) u2x19
  rw [if_neg (by norm_num)] at u3pc
  have hmf : mf 8 8 [g0, g1, g2] = L0 ++ L1 ++ L2 := by
    simp only [mf, hL0, hL1, hL2, he0, he1, List.append_assoc]
  rw [hmf]
  refine ⟨u3, 2 + (k0 + (k1 + (k2 + 2))), st1.trans (st0.trans (st1'.trans (st2'.trans st3))), by omega, u3pc,
    ?_, by rw [u3r.get (by simp)]; exact u2x20, ?_, ?_, ?_, ?_⟩
  · rw [u3r.get (by simp), u2x16]; simp only [List.length_append]; congr 1; ring
  · refine Emitted.append (Emitted.append ?_ ?_) ?_
    · exact ((u0em.frame u1f (by sgo) (fun A h1 h2' h => by omega)).frame u2f (by sgo)
        (fun A h1 h2' h => by omega)).frame u3f (by sgo) (fun _ _ _ h => h)
    · exact (u1em.frame u2f (by sgo) (fun A h1 h2' h => by omega)).frame u3f (by sgo) (fun _ _ _ h => h)
    · simp only [List.length_append]
      rw [show pp + 16 * (L0.length + L1.length) = pp + 16 * L0.length + 16 * L1.length by ring]
      exact u2em.frame u3f (by sgo) (fun _ _ _ h => h)
  · simp only [List.length_append]; omega
  · exact ((((t1r.trans u0r).trans u1r).trans u2r).trans u3r).mono (by simp)
  · refine ((((t1f.trans u0f).trans u1f).trans u2f).trans u3f).mono (fun A _ h => ?_)
    simp only [List.length_append]
    rcases h with ((((h | h) | h) | h) | h)
    · exact h.elim
    · omega
    · omega
    · omega
    · exact h.elim

end SigGolfCandidate.T3M.Sign
