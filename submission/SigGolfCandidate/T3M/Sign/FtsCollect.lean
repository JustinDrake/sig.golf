import SigGolfCandidate.T3M.Sign.Frontier

/-!
# Sign: the secrets, outer siblings and root of one coordinate (words 256..356)

* `sec_loop` : `fts_sec` (263..277) copies the secrets of the three opened leaves to `SDST`;
* `outer_loop` : `fr_outer` (331..344) emits the three outer siblings `(HS >> LEV) ^ 1`, `LEV = 8, 9, 10`;
* `fts_collect` : from the return of `build_levels` (256) to `fts_coord` (186) of the next coordinate:
  secrets, the multiproof walk `mf 7 7 [g0, g1, g2]`, the outer siblings, the root to the forest slot.
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M (lcaLevel heap_eq two_pow_add_xor_one xor_one_eq)

/-- The three secrets (`fts_sec`, 263..277), from `J = j`: copies `SEC + 16 g_i` to `SDST + 16 i`. -/
theorem sec_loop (t0 : MachineState) (gs : List Nat) (hgs : gs.length = 3) (hgb : ∀ g ∈ gs, g < 2048)
    (rowp sd : Nat) (hrow : rowp + 24 ≤ 2 ^ 24) (hrow8 : rowp % 8 = 0) (hsd8 : sd % 8 = 0)
    (hsd : sd + 48 ≤ 2 ^ 24) (hsdA : sd + 48 ≤ rowp ∨ rowp + 24 ≤ sd)
    (hsdS : sd + 48 ≤ SEC ∨ SEC + 32768 ≤ sd) :
    ∀ n j, j + n = 3 → ∀ (t : MachineState), t.pc = pcOf 263 → t.getReg .x19 = BitVec.ofNat 64 j →
      t.getReg .x25 = BitVec.ofNat 64 rowp → t.getReg .x26 = BitVec.ofNat 64 (sd + 16 * j) →
      (∀ i < 3, t.getMem (BitVec.ofNat 64 (rowp + 8 * i)) = BitVec.ofNat 64 (gs.getD i 0)) →
      (∀ A, SEC ≤ A → A < SEC + 32768 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
      (∀ i < j, DigAt t (sd + 16 * i) (memDig t0 (SEC + 16 * gs.getD i 0))) →
      ∃ u k, Steps image t k k u ∧ k ≤ 15 * n + 2 ∧ u.pc = pcOf 278 ∧
        u.getReg .x26 = BitVec.ofNat 64 (sd + 48) ∧
        (∀ i < 3, DigAt u (sd + 16 * i) (memDig t0 (SEC + 16 * gs.getD i 0))) ∧
        RegsExcept t u [.x6, .x7, .x19, .x26, .x28] ∧ Frame t u (fun A => sd + 16 * j ≤ A ∧ A < sd + 48)
  | 0, j, hjn, t, hpc, h19, _, h26, _, _, hdone => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk263_spec t hpc j (by omega) h19
    rw [if_neg (by omega)] at upc
    refine ⟨u, 2, st, by omega, upc, by rw [ur.get (by simp), h26]; congr 1; omega, fun i hi => ?_,
      ur.mono (by simp), uf.mono (fun _ _ h => h.elim)⟩
    exact (hdone i (by omega)).frame uf (by omega) (fun h => h) (fun h => h)
  | n + 1, j, hjn, t, hpc, h19, h25, h26, hrowm, hsec, hdone => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk263_spec t hpc j (by omega) h19
    rw [if_pos (by omega)] at t1pc
    have hgj : gs.getD j 0 < 2048 := hgb _ (by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
    obtain ⟨t2, st2, t2pc, t2x19, t2x26, m0, m8, t2r, t2f⟩ := blk265_spec t1 t1pc j rowp (sd + 16 * j)
      (gs.getD j 0) (by omega) hrow8 (by omega) (by omega) hgj (by omega) (by rw [t1r.get (by simp)]; exact h19)
      (by rw [t1r.get (by simp)]; exact h25) (by rw [t1r.get (by simp)]; exact h26)
      (by rw [t1f.get (by omega) (fun h => h)]; exact hrowm j (by omega))
    have f12 : Frame t t2 (fun A => A = sd + 16 * j ∨ A = sd + 16 * j + 8) :=
      (t1f.trans t2f).mono (fun _ _ h => by rcases h with h | h; exact h.elim; exact h)
    obtain ⟨u, k, st, hk, upc, u26, uall, ur, uf⟩ := sec_loop t0 gs hgs hgb rowp sd hrow hrow8 hsd8 hsd hsdA hsdS
      n (j + 1) (by omega) t2 t2pc t2x19 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h25)
      (by rw [t2x26, show sd + 16 * j + 16 = sd + 16 * (j + 1) by ring])
      (fun i hi => by rw [f12.get (by omega) (by omega)]; exact hrowm i hi)
      (fun A h1 h2 => by rw [f12.get (by sgo) (by sgo)]; exact hsec A h1 h2)
      (fun i hi => by
        by_cases hij : i = j
        · subst hij
          refine ⟨?_, ?_⟩
          · rw [m0, t1f.get (by sgo) (fun h => h), hsec _ (by omega) (by omega)]; exact (memDig_digAt t0 _).1
          · rw [m8, t1f.get (by sgo) (fun h => h), hsec _ (by omega) (by omega)]; exact (memDig_digAt t0 _).2
        · exact (hdone i (by omega)).frame f12 (by omega) (by omega) (by omega))
    exact ⟨u, 2 + (13 + k), st1.trans (st2.trans st), by omega, upc, u26, uall,
      ((t1r.trans t2r).trans ur).mono (by simp),
      (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩

/-- The outer siblings of leaf `g` at the levels `l .. l + n - 1`. -/
def outerL (g l n : Nat) : List (Nat × Nat) := (List.range n).map fun j => (l + j, g / 2 ^ (l + j) ^^^ 1)

theorem outerL_succ (g l n : Nat) : outerL g l (n + 1) = [(l, g / 2 ^ l ^^^ 1)] ++ outerL g (l + 1) n := by
  unfold outerL
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.add_zero, List.singleton_append]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 j]

theorem outerL_length (g l n : Nat) : (outerL g l n).length = n := by simp [outerL]

/-- **The outer siblings** (`fr_outer`, 332..344) from `LEV = l` to 11: emits `outerL g l (11 - l)`. -/
theorem outer_loop (t0 : MachineState) (g : Nat) (hg : g < 2048) :
    ∀ (n l : Nat), l + n = 11 → 7 ≤ l → ∀ (t : MachineState) (pp : Nat),
    t.pc = pcOf 332 → t.getReg .x22 = BitVec.ofNat 64 l → t.getReg .x20 = BitVec.ofNat 64 (2048 + g) →
    t.getReg .x2 = BitVec.ofNat 64 FTS → t.getReg .x16 = BitVec.ofNat 64 pp →
    pp % 8 = 0 → pp + 16 * n ≤ FTS →
    (∀ A, FTS ≤ A → A < FTS + 65536 → t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A)) →
    ∃ u k, Steps image t k k u ∧ k ≤ 13 * n + 2 ∧ u.pc = pcOf 345 ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * n) ∧ Emitted t0 u pp (outerL g l n) ∧
      RegsExcept t u [.x6, .x7, .x16, .x22, .x28] ∧ Frame t u (fun A => pp ≤ A ∧ A < pp + 16 * n)
  | 0, l, hln, _, t, pp, hpc, h22, _, _, h16, _, _, _ => by
    obtain ⟨u, st, upc, ur, uf⟩ := blk332_spec t hpc l (by omega) h22
    rw [if_neg (by omega)] at upc
    exact ⟨u, 2, st, by omega, upc, by rw [ur.get (by simp), h16]; simp, by simp [outerL, Emitted.nil],
      ur.mono (by simp), uf.mono (fun _ _ h => h.elim)⟩
  | n + 1, l, hln, hl8, t, pp, hpc, h22, h20, h2, h16, hpp8, hppl, hheap => by
    obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := blk332_spec t hpc l (by omega) h22
    rw [if_pos (by omega)] at t1pc
    obtain ⟨t2, st2, t2pc, t2x22, t2x16, m0, m8, t2r, t2f⟩ := blk334_spec t1 t1pc l (2048 + g) pp (by omega)
      (by omega) (by sgo) hpp8 (by rw [t1r.get (by simp)]; exact h22) (by rw [t1r.get (by simp)]; exact h20)
      (by rw [t1r.get (by simp)]; exact h2) (by rw [t1r.get (by simp)]; exact h16)
    have f12 : Frame t t2 (fun A => A = pp ∨ A = pp + 8) := (t1f.trans t2f).mono (fun _ _ h => by
      rcases h with h | h; exact h.elim; exact h)
    have h2heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t2.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) :=
      fun A h1 h2' => (f12.get (by sgo) (by sgo)).trans (hheap A h1 h2')
    obtain ⟨u, k, st, hk, upc, u16, uem, ur, uf⟩ := outer_loop t0 g hg n (l + 1) (by omega) (by omega) t2 (pp + 16)
      t2pc t2x22 (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h20)
      (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2) t2x16 (by omega) (by omega) h2heap
    have hv : (2048 + g) / 2 ^ l < 4096 := by have := Nat.div_le_self (2048 + g) (2 ^ l); omega
    have hxv : (2048 + g) / 2 ^ l ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hv (by norm_num)
    have hfirst : DigAt t2 pp (nodeVal t0 (l, g / 2 ^ l ^^^ 1)) := by
      unfold nodeVal
      rw [hp_sib (by omega)]
      refine ⟨?_, ?_⟩
      · rw [m0, t1f.get (by sgo) (fun h => h), hheap _ (by sgo) (by sgo)]; exact (memDig_digAt t0 _).1
      · rw [m8, t1f.get (by sgo) (fun h => h), hheap _ (by sgo) (by sgo)]; exact (memDig_digAt t0 _).2
    refine ⟨u, 2 + (11 + k), st1.trans (st2.trans st), by omega, upc, by rw [u16]; congr 1; ring, ?_,
      ((t1r.trans t2r).trans ur).mono (by simp), (f12.trans uf).mono (fun A _ h => by rcases h with h | h <;> omega)⟩
    rw [outerL_succ]
    refine Emitted.append ?_ (by simpa using uem)
    intro i hi
    simp only [List.length_singleton] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using hfirst.frame uf (by sgo) (by omega) (by omega)

/-- The forest-block slot of coordinate `c`'s root (`root0 | T11 | root1 .. root6`). -/
def rootOff (c : Nat) : Nat := if c = 0 then 0 else 16 * (c + 1)

/-- Registers the collection may change. -/
def colRegs : List Reg := [.x6, .x7, .x8, .x16, .x19, .x20, .x21, .x22, .x23, .x25, .x26, .x28, .x29]

/-- **The collection of coordinate `c`** (words 256..356): from the return of `build_levels` (256) with the
sorted row `g0 < g1 < g2` at `SEL + 24 c`: the three secrets to `sd`, the multiproof walk and the outer
siblings to `pp`, the root to the forest slot, back to `fts_coord` with `coord = c + 1`. -/
theorem fts_collect (t : MachineState) (c g0 g1 g2 pp sd : Nat) (hc : c < 7) (hg2 : g2 < 2048) (h01 : g0 < g1)
    (h12 : g1 < g2) (hl01 : lcaLevel g0 g1 ≤ 7) (hl12 : lcaLevel g1 g2 ≤ 7)
    (hpc : t.pc = pcOf 256) (h8 : t.getReg .x8 = BitVec.ofNat 64 c) (h2 : t.getReg .x2 = BitVec.ofNat 64 FTS)
    (h16 : t.getReg .x16 = BitVec.ofNat 64 pp) (h26 : t.getReg .x26 = BitVec.ofNat 64 sd)
    (hm0 : t.getMem (BitVec.ofNat 64 (SEL + 24 * c)) = BitVec.ofNat 64 g0)
    (hm1 : t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8)) = BitVec.ofNat 64 g1)
    (hm2 : t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 16)) = BitVec.ofNat 64 g2)
    (hpp8 : pp % 8 = 0) (hpp : pp + 16 * 52 ≤ FOREST) (hsd8 : sd % 8 = 0) (hsd : sd + 48 ≤ pp) :
    ∃ u k, Steps image t k k u ∧ k ≤ 1200 ∧ u.pc = pcOf 186 ∧ u.getReg .x8 = BitVec.ofNat 64 (c + 1) ∧
      u.getReg .x16 = BitVec.ofNat 64 (pp + 16 * ((mf 7 7 [g0, g1, g2]).length + 4)) ∧
      u.getReg .x26 = BitVec.ofNat 64 (sd + 48) ∧
      (∀ i < 3, DigAt u (sd + 16 * i) (memDig t (SEC + 16 * [g0, g1, g2].getD i 0))) ∧
      Emitted t u pp (mf 7 7 [g0, g1, g2] ++ outerL g2 7 4) ∧
      DigAt u (FOREST + rootOff c) (memDig t (FTS + 16)) ∧
      (mf 7 7 [g0, g1, g2]).length ≤ 48 ∧
      RegsExcept t u colRegs ∧
      Frame t u (fun A => (sd ≤ A ∧ A < sd + 48) ∨ (pp ≤ A ∧ A < pp + 16 * ((mf 7 7 [g0, g1, g2]).length + 4)) ∨
        A = FOREST + rootOff c ∨ A = FOREST + rootOff c + 8) := by
  have hrow : SEL + 24 * c + 32 ≤ 2 ^ 24 := by sgo
  obtain ⟨t1, st1, t1pc, t1x25, t1x19, t1r, t1f⟩ := blk256_spec t hpc c hc h8
  have hrowm : ∀ i < 3, t1.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * i)) = BitVec.ofNat 64 ([g0, g1, g2].getD i 0) := by
    intro i hi
    rw [t1f.get (by sgo) (fun h => h)]
    interval_cases i
    · simpa using hm0
    · simpa using hm1
    · simpa using hm2
  -- the secrets
  obtain ⟨t2, k2, st2, hk2, t2pc, t2x26, t2sec, t2r, t2f⟩ := sec_loop t [g0, g1, g2] rfl
    (fun g hg => by simp at hg; omega) (SEL + 24 * c) sd (by sgo) (by sgo) hsd8 (by sgo) (Or.inl (by sgo))
    (Or.inl (by sgo)) 3 0 rfl t1 t1pc t1x19 t1x25 (by rw [t1r.get (by simp)]; simpa using h26) hrowm
    (fun A _ _ => t1f.get (by sgo) (fun h => h)) (fun i hi => absurd hi (by omega))
  have f02 : Frame t t2 (fun A => sd ≤ A ∧ A < sd + 48) :=
    (t1f.trans t2f).mono (fun A _ h => by rcases h with h | h; exact h.elim; omega)
  -- the walk
  obtain ⟨t3, k3, st3, hk3, t3pc, t3x16, t3x20, t3em, t3len, t3r, t3f⟩ := fr_three t t2 g0 g1 g2 (SEL + 24 * c) pp
    hg2 h01 h12 hl01 hl12 hrow (by sgo) t2pc (by rw [t2r.get (by simp), t1x25])
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h2) (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h16)
    (by rw [t2f.get (by sgo) (by sgo)]; simpa using hrowm 0 (by omega))
    (by rw [t2f.get (by sgo) (by sgo)]; simpa using hrowm 1 (by omega))
    (by rw [t2f.get (by sgo) (by sgo)]; simpa using hrowm 2 (by omega)) hpp8 (by sgo) (by sgo)
    (fun A h1 h2' => f02.get (by sgo) (by sgo))
  set Lm := mf 7 7 [g0, g1, g2] with hLm
  clear_value Lm
  have f03 : Frame t t3 (fun A => (sd ≤ A ∧ A < sd + 48) ∨ (pp ≤ A ∧ A < pp + 16 * Lm.length)) :=
    (f02.trans t3f).mono (fun A _ h => h)
  have r03 : RegsExcept t t3 ([.x6, .x7, .x19, .x25] ++ [.x6, .x7, .x19, .x26, .x28] ++
      [.x6, .x7, .x16, .x19, .x20, .x21, .x22, .x23, .x28]) := (t1r.trans t2r).trans t3r
  have h3heap : ∀ A, FTS ≤ A → A < FTS + 65536 → t3.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2' => f03.get (by sgo) (by sgo)
  -- the outer siblings
  obtain ⟨t4, st4, t4pc, t4x22, t4r, t4f⟩ := blk331_spec t3 t3pc
  obtain ⟨t5, k5, st5, hk5, t5pc, t5x16, t5em, t5r, t5f⟩ := outer_loop t g2 hg2 4 7 rfl le_rfl t4 (pp + 16 * Lm.length)
    t4pc t4x22 (by rw [t4r.get (by simp)]; exact t3x20) (by rw [t4r.get (by simp), r03.get (by simp)]; exact h2)
    (by rw [t4r.get (by simp)]; exact t3x16) (by omega) (by sgo)
    (fun A h1 h2' => (t4f.get (by sgo) (fun h => h)).trans (h3heap A h1 h2'))
  have f35 : Frame t3 t5 (fun A => pp + 16 * Lm.length ≤ A ∧ A < pp + 16 * Lm.length + 16 * 4) :=
    (t4f.trans t5f).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have r35 : RegsExcept t3 t5 ([.x22] ++ [.x6, .x7, .x16, .x22, .x28]) := t4r.trans t5r
  -- the root
  have h5x8 : t5.getReg .x8 = BitVec.ofNat 64 c := by
    rw [r35.get (by simp), r03.get (by simp)]; exact h8
  have h5x2 : t5.getReg .x2 = BitVec.ofNat 64 FTS := by
    rw [r35.get (by simp), r03.get (by simp)]; exact h2
  obtain ⟨t6, k6, st6, hk6, t6pc, t6x28, t6r, t6f⟩ : ∃ t6 k6, Steps image t5 k6 k6 t6 ∧ k6 ≤ 3 ∧
      t6.pc = pcOf 348 ∧ t6.getReg .x28 = BitVec.ofNat 64 (rootOff c) ∧ RegsExcept t5 t6 [.x28] ∧
      Frame t5 t6 (fun _ => False) := by
    obtain ⟨a1, sa1, a1pc, a1x28, a1r, a1f⟩ := blk345_spec t5 t5pc c hc h5x8
    by_cases hc0 : c = 0
    · rw [if_pos hc0] at a1pc
      exact ⟨a1, 2, sa1, by omega, a1pc, by subst hc0; rw [a1x28]; rfl, a1r, a1f⟩
    · rw [if_neg hc0] at a1pc
      obtain ⟨a2, sa2, a2pc, a2x28, a2r, a2f⟩ := blk347_spec a1 a1pc (16 * c) a1x28
      exact ⟨a2, 2 + 1, sa1.trans sa2, by omega, a2pc,
        by rw [a2x28, rootOff, if_neg hc0]; congr 1, (a1r.trans a2r).mono (by simp),
        (a1f.trans a2f).mono (fun _ _ h => by simp_all)⟩
  have hro : rootOff c ≤ 112 ∧ rootOff c % 8 = 0 := by unfold rootOff; split_ifs <;> omega
  obtain ⟨t7, st7, t7pc, t7x8, r0, r8, t7r, t7f⟩ := blk348_spec t6 t6pc (rootOff c) c hro.1 hro.2 t6x28
    (by rw [t6r.get (by simp)]; exact h5x2) (by rw [t6r.get (by simp)]; exact h5x8)
  have hroot : DigAt t7 (FOREST + rootOff c) (memDig t (FTS + 16)) := by
    have e1 : t6.getMem (BitVec.ofNat 64 (FTS + 16)) = t.getMem (BitVec.ofNat 64 (FTS + 16)) := by
      rw [t6f.get (by sgo) (fun h => h), f35.get (by sgo) (by sgo), h3heap _ (by sgo) (by sgo)]
    have e2 : t6.getMem (BitVec.ofNat 64 (FTS + 24)) = t.getMem (BitVec.ofNat 64 (FTS + 24)) := by
      rw [t6f.get (by sgo) (fun h => h), f35.get (by sgo) (by sgo), h3heap _ (by sgo) (by sgo)]
    refine ⟨by rw [r0, e1]; exact (memDig_digAt t _).1, by rw [r8, e2]; exact (memDig_digAt t _).2⟩
  have hfr57 : Frame t5 t7 (fun A => A = FOREST + rootOff c ∨ A = FOREST + rootOff c + 8) :=
    (t6f.trans t7f).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  refine ⟨t7, 7 + (k2 + (k3 + (1 + (k5 + (k6 + 9))))),
    st1.trans (st2.trans (st3.trans (st4.trans (st5.trans (st6.trans st7))))), by omega, t7pc, t7x8, ?_, ?_, ?_,
    ?_, hroot, t3len, ?_, ?_⟩
  · rw [t7r.get (by simp), t6r.get (by simp), t5x16, show pp + 16 * Lm.length + 16 * 4 = pp + 16 * (Lm.length + 4) by ring]
  · rw [t7r.get (by simp), t6r.get (by simp), r35.get (by simp), t3r.get (by simp)]; exact t2x26
  · have hF : pp + 832 ≤ 131872 := by simpa [FOREST] using hpp
    have hF2 : FOREST = 131872 := rfl
    have F27 : Frame t2 t7 (fun A => (pp ≤ A ∧ A < pp + 16 * (Lm.length + 4)) ∨ A = FOREST + rootOff c ∨
        A = FOREST + rootOff c + 8) := (t3f.trans (f35.trans hfr57)).mono (fun A _ h => by
      rcases h with h | h | h | h
      · exact Or.inl ⟨h.1, by omega⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))
    intro i hi
    exact (t2sec i hi).frame F27 (by omega) (by intro h; rcases h with h | h | h <;> omega)
      (by intro h; rcases h with h | h | h <;> omega)
  · have hF : pp + 832 ≤ 131872 := by simpa [FOREST] using hpp
    have hF2 : FOREST = 131872 := rfl
    try rw [← hLm]
    have hb1 : pp + 16 * Lm.length < 2 ^ 64 := by
      have h48 : Lm.length ≤ 48 := t3len
      clear * - h48 hF
      omega
    refine Emitted.append (L := Lm) (M := outerL g2 7 4) ((t3em.frame (f35.trans hfr57) hb1
      (fun A h1 h2' h => ?_))) ?_
    · rcases h with h | h | h <;> omega
    · have hol : (outerL g2 7 4).length = 4 := outerL_length _ _ _
      exact t5em.frame hfr57 (by omega) (fun A h1 h2' h => by rcases h with h | h <;> omega)
  · exact ((r03.trans r35).trans (t6r.trans t7r)).mono (by simp [colRegs])
  · refine ((f03.trans f35).trans hfr57).mono (fun A _ h => ?_)
    rcases h with ((h | h) | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨h.1, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr h)

end SigGolfCandidate.T3M.Sign
