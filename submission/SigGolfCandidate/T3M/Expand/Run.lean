import SigGolfCandidate.T3M.Expand.Fts
import SigGolfCandidate.T3M.Expand.Layers
import SigGolfCandidate.T3M.Expand.Wit

/-!
# `expand`: the whole phase as a bounded refinement (stream E)

`expand_tbsim` : given the FTS phase (`FtsSpec`), from the loaded state `einit m pk σ` the machine refines
`expandN m pk (sigDec σ)` within `expCost` cycles: `start`, the digest search (`digestSearch_tbsim` at
`(30, 354)`), `ds_done`, the FTS phase, the canonical tail, the forest pk, the four layers (`layers_tbsim`),
`compare`; on success it halts at `accept` (`HALT(0)`) with the witness `witEnc N w` at `0x800`
(`ExpQ`), on every rejection at `fail` (`HALT(1)`).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest HashOutput Signature Witness forestPk chainCount height)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC NODE NOUT SelRows FailedAt DsPre DsPost DsW dsRegs
  digestSearch_tbsim dsAt_expand kernAt_expand cs0_spec)

set_option autoImplicit false

theorem frame_readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWords h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]

theorem dword_of_halves (w : BitVec 64) :
    w = BitVec.ofNat 64 ((w.extractLsb' 0 32).toNat + 2 ^ 32 * (w.extractLsb' 32 32).toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := w.isLt
  have h1 : w.toNat / 2 ^ 32 % 2 ^ 32 = w.toNat / 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  omega

theorem toNat_extract0_mod (N : BitVec 256) : (N.extractLsb' 0 64).toNat % 2 ^ 31 = N.toNat % 2 ^ 31 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Nat.mod_mod_of_dvd _ (by norm_num)]

/-- The final postcondition: `fail` (`HALT(1)`), or `accept` (`HALT(0)`) with the witness bytes. -/
def ExpQ : Option (HashOutput × Witness) → MachineState → Prop
  | none, t => FailedAt 354 t
  | some (N, w), t => t.pc = pcOf 353 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.readWords (BitVec.ofNat 64 0x800) 3155 = wordsOf (witList N w)

/-- An all-oracle cycle bound of `expand`. -/
def expCost : Nat := 30 + (2 ^ 20 * 666 + 664) + 16 + ftsCost + 1 + (12 * 124 + 4) + 36 + lcost 4 + 11

section run
variable {sk : BitVec 256}

theorem expand_tbsim (hF : FtsSpec sk) (m : Message) (pk : PublicKey) (σ : Bytes 5824) :
    TBSim image sk (einit m pk σ) expCost (expandN m pk (sigDec σ)) ExpQ := by
  set sig := sigDec σ with hsig
  set s0 := einit m pk σ with hs0
  have hsigd : ∀ k < 364, DigAt s0 (0x7000 + 16 * k) (sigDig σ k) := fun k hk => einit_sig m pk σ k hk
  have hz0 : ∀ A, A < 2 ^ 64 → (A < 0x7000 ∨ 0x7000 + 5824 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) → (A < 0x40 ∨ 0x60 ≤ A) →
      s0.getMem (BitVec.ofNat 64 A) = 0 := fun A hA h1 h2 h3 => einit_zero m pk σ A hA ⟨h1, h2, h3⟩
  -- `start`
  obtain ⟨t1, st1, p1, x5_1, x19_1, w800, w808, d0, d8, d32, d40, d48, d56, r1, f1⟩ := s0_spec s0 (einit_pc m pk σ)
  have hrho : DigAt s0 0x7000 sig.rho := hsigd 0 (by decide)
  have hds : DsPre 30 t1 sig.rho m := by
    refine ⟨p1, x5_1, x19_1, ⟨d0.trans hrho.1, d8.trans hrho.2⟩, fun k hk => ?_⟩
    interval_cases k
    · rw [show DIG + 32 + 8 * 0 = DIG + 32 by rfl, d32]; simpa using einit_msg m pk σ 0 (by decide)
    · rw [show DIG + 32 + 8 * 1 = DIG + 40 by rfl, d40]; simpa using einit_msg m pk σ 1 (by decide)
    · rw [show DIG + 32 + 8 * 2 = DIG + 48 by rfl, d48]; simpa using einit_msg m pk σ 2 (by decide)
    · rw [show DIG + 32 + 8 * 3 = DIG + 56 by rfl, d56]; simpa using einit_msg m pk σ 3 (by decide)
  rw [expandN_eq]
  refine (TBSim.steps st1 (TBSim.bind (W₂ := 16 + ftsCost + 1 + (12 * 124 + 4) + 36 + lcost 4 + 11)
    (digestSearch_tbsim (sk := sk) dsAt_expand kernAt_expand hds) (fun r t2 h2 => ?_))).mono
    (by unfold expCost; omega) (fun _ _ h => h)
  rcases r with _ | ⟨counter, N⟩
  · exact (TBSim.pure (Q := ExpQ) (a := none) h2).mono (by omega) (fun _ _ h => h)
  obtain ⟨p2, x5_2, adm2, out2, rows2, r2, f2, hc2, x19_2⟩ := h2
  obtain ⟨t3, st3, p3, x9_3, idx3, dc3, x2_3, x18_3, x22_3, x8_3, r3, f3⟩ :=
    s49_spec t2 p2 counter.toNat x19_2
  have hidx : (t2.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31 = N.toNat % 2 ^ 31 := by
    rw [show NBUF = NBUF + 8 * 0 from rfl, out2 0 (by decide), Nat.mul_zero, toNat_extract0_mod]
  -- memory from the loaded state to `t3`
  have g3 : ∀ A, A < 2 ^ 64 → ¬ (A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
      A = DIG + 48 ∨ A = DIG + 56) → ¬ DsW A → ¬ (A = IDXV ∨ A = 0x810) →
      t3.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 h3 => by rw [f3.get hA h3, f2.get hA h2, f1.get hA h1]
  have nsW : ∀ A, (A < 0x800 ∨ 0x810 ≤ A) → (A < DIG ∨ DIG + 64 ≤ A) → ¬ (A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨
      A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56) := by
    intro A h1 h2 h; simp only [DIG] at h h2; omega
  have ndW : ∀ A, (A < DIG + 16 ∨ DIG + 32 ≤ A) → (A < NBUF ∨ NBUF + 32 ≤ A) → (A < Search.SEL ∨ Search.SEL + 168 ≤ A) →
      ¬ DsW A := by
    intro A h1 h2 h3 h; unfold DsW at h; simp only [DIG, NBUF, Search.SEL] at h h1 h2 h3; omega
  have n49 : ∀ A, A ≠ IDXV → A ≠ 0x810 → ¬ (A = IDXV ∨ A = 0x810) := fun A h1 h2 h => by
    rcases h with h | h <;> contradiction
  -- the FTS entry
  have hfp : FtsPre sig N t3 := by
    refine ⟨p3, by rw [r3.get (by decide)]; exact x5_2, x8_3, by rw [x9_3, hidx], x18_3, x22_3, x2_3, adm2,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc j hj
      rw [f3.get (by unfold Search.SEL; omega) (n49 _ (by unfold Search.SEL IDXV; omega)
        (by unfold Search.SEL; omega))]
      exact rows2 c hc j hj
    · intro k hk
      have hd := hsigd (1 + k) (by omega)
      rw [show 0x7000 + 16 * (1 + k) = 0x7010 + 16 * k by ring] at hd
      exact ⟨(g3 _ (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
          (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
          (n49 _ (by simp only [IDXV]; omega) (by omega))).trans hd.1,
        (g3 _ (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
          (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
          (n49 _ (by simp only [IDXV]; omega) (by omega))).trans hd.2⟩
    · intro k hk
      have hd := hsigd (22 + k) (by omega)
      rw [show 0x7000 + 16 * (22 + k) = 0x7160 + 16 * k by ring] at hd
      exact ⟨(g3 _ (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
          (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
          (n49 _ (by simp only [IDXV]; omega) (by omega))).trans hd.1,
        (g3 _ (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
          (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
          (n49 _ (by simp only [IDXV]; omega) (by omega))).trans hd.2⟩
    all_goals first
      | (intro A h1 h2
         rw [g3 _ (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
           (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
           (n49 _ (by simp only [IDXV]; omega) (by omega)), hz0 _ (by omega) (by omega) (by omega) (by omega)])
      | (rw [g3 _ (by decide) (nsW _ (by decide) (by decide)) (ndW _ (by decide) (by decide) (by decide))
           (n49 _ (by decide) (by decide)), hz0 _ (by decide) (by decide) (by decide) (by decide)])
  refine (TBSim.steps st3 (TBSim.bind (W₂ := 1 + (12 * 124 + 4) + 36 + lcost 4 + 11) (hF sig N t3 hfp)
    (fun st t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
  rcases st with _ | ⟨roots, used⟩
  · exact (TBSim.pure (Q := ExpQ) (a := none) h4).mono (by omega) (fun _ _ h => h)
  obtain ⟨p4, x5_4, x9_4, x18_4, hused, hlen, hroots, hleaf, hstream, r4, f4⟩ := h4
  obtain ⟨t5, st5, p5, x13_5, r5, f5⟩ := s215_spec t4 p4
  have hslots : ∀ k, used ≤ k → k < 124 →
      DigAt t5 (0x7160 + 16 * k) (sig.proof ⟨k % 124, Nat.mod_lt _ (by decide)⟩) := by
    intro k hk1 hk2
    have hd := hfp.proof k hk2
    have e : (⟨k % 124, Nat.mod_lt _ (by decide)⟩ : Fin 124) = ⟨k, hk2⟩ := Fin.ext (Nat.mod_eq_of_lt hk2)
    rw [e]
    have nF : ∀ A, 0x7000 ≤ A → A < 0x7000 + 5824 → ¬ FtsW A := by
      intro A h1 h2 h; unfold FtsW at h; simp only [NODE, NOUT, FLEAF, FOREST] at h; omega
    exact (hd.frame f4 (by omega) (nF _ (by omega) (by omega)) (nF _ (by omega) (by omega))).frame f5 (by omega)
      (by simp) (by simp)
  obtain ⟨c6, t6, st6, hc6, hif⟩ := zt_loop_spec (fun k => sig.proof ⟨k % 124, Nat.mod_lt _ (by decide)⟩)
    (124 - used) used t5 (by omega) p5 (by rw [x13_5, x18_4]) hslots
  have htz : tailZero sig used = (List.range (124 - used)).all
      (fun i => decide (sig.proof ⟨(used + i) % 124, Nat.mod_lt _ (by decide)⟩ = 0)) := rfl
  by_cases hz : tailZero sig used = true
  · rw [← htz, hz] at hif
    obtain ⟨p6, r6, f6⟩ := hif
    simp only [hz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    set index := N.toNat % 2 ^ 31 with hindex
    have hi : index < 2 ^ 31 := Nat.mod_lt _ (by positivity)
    have h9_6 : t6.getReg .x9 = BitVec.ofNat 64 index := by
      rw [r6.get (by decide), r5.get (by decide)]; exact x9_4
    have h5_6 : t6.getReg .x5 = 0 := by rw [r6.get (by decide), r5.get (by decide)]; exact x5_4
    have hroots6 : ∀ c < 7, DigAt t6 (FOREST + slotOff c) (roots.getD c 0) := fun c hc => by
      have hs : slotOff c + 16 ≤ 128 := by unfold slotOff; split_ifs <;> omega
      exact ((hroots c hc).frame f5 (by simp only [FOREST]; omega) (by simp) (by simp)).frame f6
        (by simp only [FOREST]; omega) (by simp) (by simp)
    refine (TBSim.steps (st5.trans st6) (TBSim.bind (W₂ := lcost 4 + 11)
      (forest_tbsim (sk := sk) index hi roots hlen t6 p6 h9_6 h5_6 hroots6) (fun root t7 h7 => ?_))).mono
      (by omega) (fun _ _ h => h)
    obtain ⟨p7, e7, r7, f7⟩ := h7
    -- memory from the loaded state to `t7`
    have F7 := (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7
    have hm7 : ∀ A, A < 2 ^ 64 → (A < 0x800 ∨ 0x810 ≤ A) → (A < DIG ∨ DIG + 64 ≤ A) → (A < NBUF ∨ NBUF + 32 ≤ A) →
        (A < Search.SEL ∨ Search.SEL + 168 ≤ A) → A ≠ IDXV → A ≠ 0x810 → ¬ FtsW A →
        (A < FOREST ∨ FOREST + 128 ≤ A) → (A < FOUT ∨ FOUT + 32 ≤ A) → A ≠ ENC → A ≠ ENC + 8 →
        t7.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
      refine F7.get hA ?_
      rintro ((((((h | h) | h) | h) | h) | h) | h)
      · simp only [DIG] at h h1 h2; omega
      · unfold DsW at h; simp only [DIG, NBUF, Search.SEL] at h h2 h3 h4; omega
      · rcases h with h | h <;> contradiction
      · exact h7 h
      · exact h
      · exact h
      · simp only [FOREST, FOUT, ENC] at h h8 h9 h10 h11; omega
    have nFts : ∀ A, (A < 0x22000 - 512 ∨ 0x22000 ≤ A) → (A < NODE ∨ NOUT + 32 ≤ A ∨ A = NODE + 32 ∨ A = NODE + 40) →
        (A < FLEAF ∨ FLEAF + 64 ≤ A) → (A < FOREST ∨ FOREST + 128 ≤ A) → (A < 0x840 ∨ 0x3418 ≤ A) → ¬ FtsW A := by
      intro A h1 h2 h3 h4 h5 h; unfold FtsW at h; simp only [NODE, NOUT, FLEAF, FOREST] at h h2 h3 h4; omega
    have hm7' : ∀ A, A < 2 ^ 64 → (A < 0x800 ∨ 0x3418 ≤ A) → (A < DIG ∨ DIG + 64 ≤ A) →
        (A < NBUF ∨ NBUF + 32 ≤ A) → (A < Search.SEL ∨ Search.SEL + 168 ≤ A) → A ≠ IDXV →
        (A < 0x22000 - 512 ∨ 0x22000 ≤ A) → (A < NODE ∨ NOUT + 32 ≤ A ∨ A = NODE + 32 ∨ A = NODE + 40) →
        (A < FLEAF ∨ FLEAF + 64 ≤ A) → (A < FOREST ∨ FOREST + 128 ≤ A) → (A < FOUT ∨ FOUT + 32 ≤ A) →
        A ≠ ENC → A ≠ ENC + 8 → t7.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      by
        intro A hA h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
        have e1 : A < 0x800 ∨ 0x810 ≤ A := by rcases h1 with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]
        have e2 : A ≠ 0x810 := by rcases h1 with h | h <;> omega
        have e3 : A < 0x840 ∨ 0x3418 ≤ A := by rcases h1 with h | h <;> [exact Or.inl (by omega); exact Or.inr h]
        exact hm7 A hA e1 h2 h3 h4 h5 e2 (nFts A h6 h7 h8 h9 e3) h9 h10 h11 h12
    have hL : LInv sig index 4 root t7 := by
      refine ⟨by rw [p7]; rfl, le_refl _, by rw [r7.get (by decide)]; exact h5_6, hi, ?_, e7, ⟨0, by norm_num, ?_⟩,
        ?_, ?_⟩
      · rw [f7.get (by decide) (by simp only [IDXV, FOREST, FOUT, ENC]; omega), f6.get (by decide) (by simp),
          f5.get (by decide) (by simp), f4.get (by decide) (nFts _ (by simp only [IDXV]; omega)
            (by simp only [IDXV, NODE, NOUT]; omega) (by simp only [IDXV, FLEAF]; omega)
            (by simp only [IDXV, FOREST]; omega) (by simp only [IDXV]; omega)), idx3, hidx]
      · rw [hm7' (ENC + 32) (by decide) (by simp only [ENC]; omega) (by simp only [ENC, DIG]; omega)
          (by simp only [ENC, NBUF]; omega) (by simp only [ENC, Search.SEL]; omega) (by simp only [ENC, IDXV]; omega)
          (by simp only [ENC]; omega) (by simp only [ENC, NODE, NOUT]; omega) (by simp only [ENC, FLEAF]; omega)
          (by simp only [ENC, FOREST]; omega) (by simp only [ENC, FOUT]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega), hz0 _ (by decide) (by simp only [ENC]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega)]
        rfl
      · intro lay
        have htab := ltable lay
        have hP : lP lay = 0x7000 + 16 * layIdx lay := by fin_cases lay <;> rfl
        have hIdx : layIdx lay + chainCount lay + height lay ≤ 364 := by fin_cases lay <;> decide
        refine ⟨fun i hi' => ?_, fun j hj => ?_⟩
        · have hd := hsigd (layIdx lay + i) (by omega)
          rw [show 0x7000 + 16 * (layIdx lay + i) = lP lay + 16 * i by rw [hP]; ring] at hd
          exact ⟨(hm7' _ (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
            (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega)
            (by simp only [NODE]; omega) (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega)
            (by simp only [FOUT]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)).trans hd.1,
            (hm7' _ (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
            (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega)
            (by simp only [NODE]; omega) (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega)
            (by simp only [FOUT]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)).trans hd.2⟩
        · have hd := hsigd (layIdx lay + (chainCount lay + j)) (by omega)
          rw [show 0x7000 + 16 * (layIdx lay + (chainCount lay + j)) =
            lP lay + 16 * chainCount lay + 16 * j by rw [hP]; ring] at hd
          exact ⟨(hm7' _ (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
            (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega)
            (by simp only [NODE]; omega) (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega)
            (by simp only [FOUT]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)).trans hd.1,
            (hm7' _ (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
            (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega)
            (by simp only [NODE]; omega) (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega)
            (by simp only [FOUT]; omega) (by simp only [ENC]; omega) (by simp only [ENC]; omega)).trans hd.2⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        · rw [hm7' _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide),
            hz0 _ (by decide) (by decide) (by decide) (by decide)]
    refine (TBSim.bind (W₂ := 11) (layers_tbsim (sk := sk) 4 root t7 hL) (fun r8 t8 h8 => ?_)).mono (by omega)
      (fun _ _ h => h)
    rcases r8 with _ | ⟨root', counters⟩
    · exact (TBSim.pure (Q := ExpQ) (a := none) h8).mono (by omega) (fun _ _ h => h)
    obtain ⟨p8, x5_8, e8, hlen8, hout8, hhf8, r8, f8⟩ := h8
    -- the public key, unchanged
    have hpk : ∀ j < 2, t8.getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
      intro j hj
      have nLW : ¬ LW index 4 (0xA0 + 8 * j) := by
        rintro (h | h | ⟨lay, _, h | h⟩)
        · unfold Search.CsW Search.DigW at h; simp only [ENC, Search.EOUT, Search.DIGITS] at h; omega
        · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
        · have := (ltable lay).2.2.2.2.2.2.2.2.2.1; omega
        · have := rlWit_range h; have := ltable_lo lay; omega
      rw [f8.get (by omega) nLW, hm7' _ (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
        (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega) (by simp only [NODE]; omega)
        (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega) (by simp only [FOUT]; omega)
        (by simp only [ENC]; omega) (by simp only [ENC]; omega)]
      exact einit_pk m pk σ j hj
    obtain ⟨t9, st9, p9, x28, x29, r9, f9⟩ := c342_spec t8 p8
    have hlo : (t8.getMem (BitVec.ofNat 64 ENC) = t8.getMem (BitVec.ofNat 64 0xA0)) ↔
        root'.extractLsb' 0 64 = pk.extractLsb' 0 64 := by
      rw [e8.1, show (0xA0 : Nat) = 0xA0 + 8 * 0 from rfl, hpk 0 (by decide)]
    have hhi : (t9.getMem (BitVec.ofNat 64 (ENC + 8)) = t9.getMem (BitVec.ofNat 64 0xA8)) ↔
        root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := by
      rw [f9.get (by decide) (by simp), f9.get (by decide) (by simp), e8.2,
        show (0xA8 : Nat) = 0xA0 + 8 * 1 from rfl, hpk 1 (by decide)]
    have hsplit : root' = pk ↔ root'.extractLsb' 0 64 = pk.extractLsb' 0 64 ∧
        root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h0, h1⟩
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        by_cases h : i < 64
        · have := congrArg (fun x => x.getLsbD i) h0
          simpa [BitVec.getLsbD_extractLsb', h] using this
        · have := congrArg (fun x => x.getLsbD (i - 64)) h1
          simp [BitVec.getLsbD_extractLsb', show i - 64 < 64 by omega, show 64 + (i - 64) = i by omega] at this
          simpa using this
    by_cases heq : root' = pk
    · simp only [heq, ne_eq, not_true_eq_false, ↓reduceIte]
      have h1 := (hsplit.mp heq)
      rw [if_pos (hlo.mpr h1.1)] at p9
      obtain ⟨t10, st10, p10, r10, f10⟩ := c348_spec t9 p9 x28 x29
      rw [if_pos (hhi.mpr h1.2)] at p10
      obtain ⟨t11, st11, p11, x5_11, x10_11, _, r11, f11⟩ := c351_spec t10 p10
      refine (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure ⟨p11, x5_11, x10_11, ?_⟩)).mono (by omega)
        (fun _ _ h => h)
      have f811 : Frame t8 t11 (fun _ => False) := ((f9.trans f10).trans f11).mono (fun _ _ h => by
        rcases h with (h | h) | h <;> exact h)
      rw [frame_readWords f811 0x800 3155 (by decide) (fun _ _ h => h)]
      -- memory of `t8` from the loaded state
      have nLW : ∀ A, (A < 0x810 ∨ (0x828 ≤ A ∧ A < 0x3418)) → ¬ LW index 4 A := by
        intro A hA h
        rcases h with h | h | ⟨lay, _, h | h⟩
        · unfold Search.CsW Search.DigW at h; simp only [ENC, Search.EOUT, Search.DIGITS] at h; omega
        · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
        · have := (ltable lay).2.2.2.2.2.2.2.2.2.1; have := (ltable lay).2.2.2.2.2.2.2.2.1; omega
        · have := rlWit_range h; have := ltable_lo lay; omega
      have g87 : ∀ A, A < 2 ^ 64 → ¬ LW index 4 A →
          t8.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) := fun A hA h => f8.get hA h
      have nFo : ∀ A, A < 0x20000 → ¬ (A = FOREST + 16 ∨ A = FOREST + 24 ∨ (FOUT ≤ A ∧ A < FOUT + 32) ∨ A = ENC ∨
          A = ENC + 8) := by
        intro A hA h; simp only [FOREST, FOUT, ENC] at h; omega
      have F47 : Frame t4 t7 (fun A => (False ∨ False) ∨ (A = FOREST + 16 ∨ A = FOREST + 24 ∨
          (FOUT ≤ A ∧ A < FOUT + 32) ∨ A = ENC ∨ A = ENC + 8)) := (f5.trans f6).trans f7
      have g84 : ∀ A, A < 0x20000 → ¬ LW index 4 A →
          t8.getMem (BitVec.ofNat 64 A) = t4.getMem (BitVec.ofNat 64 A) := by
        intro A hA h
        rw [g87 A (by omega) h, F47.get (by omega) (by rintro ((h' | h') | h'); exact h'; exact h'; exact nFo A hA h')]
      have hleaf8 : t8.readWords (BitVec.ofNat 64 0x840) 128 = wordsOf (leafBytes sig) := by
        rw [frame_readWords f8 0x840 128 (by decide) (fun i hi => nLW _ (by omega)),
          frame_readWords F47 0x840 128 (by decide) (fun i hi => by
            rintro ((h' | h') | h'); exact h'; exact h'; exact nFo _ (by omega) h')]
        exact hleaf
      have hstream8 : t8.readWords (BitVec.ofNat 64 0xC40) 1275 =
          wordsOf (T3M.streamBytes (T3.selections N) sig.proof) := by
        rw [frame_readWords f8 0xC40 1275 (by decide) (fun i hi => nLW _ (by omega)),
          frame_readWords F47 0xC40 1275 (by decide) (fun i hi => by
            rintro ((h' | h') | h'); exact h'; exact h'; exact nFo _ (by omega) h')]
        exact hstream
      -- the header doublewords
      have F37 := (((f4.trans f5).trans f6).trans f7)
      have nF37 : ∀ A, 0x800 ≤ A → A < 0x840 → ¬ ((((FtsW A ∨ False) ∨ False) ∨ (A = FOREST + 16 ∨ A = FOREST + 24 ∨
          (FOUT ≤ A ∧ A < FOUT + 32) ∨ A = ENC ∨ A = ENC + 8))) := by
        intro A h1 h2
        rintro (((h | h) | h) | h)
        · unfold FtsW at h; simp only [NODE, NOUT, FLEAF, FOREST] at h; omega
        · exact h
        · exact h
        · exact nFo A (by omega) h
      have g83 : ∀ A, 0x800 ≤ A → A < 0x840 → ¬ LW index 4 A →
          t8.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) := fun A h1 h2 h3 => by
        rw [g87 A (by omega) h3, F37.get (by omega) (nF37 A h1 h2)]
      have hdw : ∀ D, (D = 0x810 ∨ D = 0x818 ∨ D = 0x820) → ∀ k, k < 2 →
          (∀ lay : T3.Layer, lay.val < 4 → ¬ (lD lay = D ∧ lk lay = k)) →
          (t8.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 =
            (t3.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 := by
        intro D hD k hk hn
        rw [hhf8 D k hD hk hn, F37.get (by omega) (nF37 D (by omega) (by omega))]
      have c0 : (t8.getMem (BitVec.ofNat 64 0x810)).extractLsb' 0 32 = counter := by
        have := hdw 0x810 (Or.inl rfl) 0 (by decide) (fun lay _ h => by
          revert h; fin_cases lay <;> simp [lD, lk])
        simp only [Nat.mul_zero] at this
        rw [this, dc3, show (0 : Nat) = 32 * 0 from rfl, replaceWord32_get _ _ (by decide)]
        apply BitVec.eq_of_toNat_eq; simp
      have c20 : (t8.getMem (BitVec.ofNat 64 0x820)).extractLsb' 32 32 = 0 := by
        have := hdw 0x820 (Or.inr (Or.inr rfl)) 1 (by decide) (fun lay _ h => by
          revert h; fin_cases lay <;> simp [lD, lk])
        simp only [Nat.mul_one] at this
        rw [this, g3 _ (by decide) (nsW _ (by decide) (by decide)) (ndW _ (by decide) (by decide) (by decide))
          (n49 _ (by decide) (by decide)), hz0 _ (by decide) (by decide) (by decide) (by decide)]
        rfl
      have hhalf : ∀ lay : T3.Layer, HalfAt t8 (lD lay) (lk lay) (counters.getD lay.val 0) :=
        fun lay => (hout8 lay (by omega)).1
      have halves : ∀ D lo hi, (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 0 32 = lo →
          (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 32 32 = hi →
          t8.getMem (BitVec.ofNat 64 D) = BitVec.ofNat 64 (lo.toNat + 2 ^ 32 * hi.toNat) := by
        intro D lo hi h1 h2
        rw [dword_of_halves (t8.getMem (BitVec.ofNat 64 D)), h1, h2]
      have hz8 : ∀ A, 0x828 ≤ A → A < 0x840 → t8.getMem (BitVec.ofNat 64 A) = 0 := by
        intro A h1 h2
        rw [g83 A (by omega) h2 (nLW A (by omega)), g3 A (by omega) (nsW _ (by omega) (by simp only [DIG]; omega))
          (ndW _ (by simp only [DIG]; omega) (by simp only [NBUF]; omega) (by simp only [Search.SEL]; omega))
          (n49 _ (by simp only [IDXV]; omega) (by omega)), hz0 _ (by omega) (by omega) (by omega) (by omega)]
      have hh : t8.readWords (BitVec.ofNat 64 0x800) 8 =
          wordsOf (headerBytes ⟨sig, counter, fun lay => counters.getD lay.val 0⟩) := by
        rw [headerBytes_words, readWords_eight]
        have r0 : t8.getMem (BitVec.ofNat 64 0x800) = sig.rho.extractLsb' 0 64 := by
          rw [g83 _ (by decide) (by decide) (nLW _ (by decide)), f3.get (by decide) (n49 _ (by decide) (by decide)),
            f2.get (by decide) (ndW _ (by decide) (by decide) (by decide)), w800]
          exact hrho.1
        have r8 : t8.getMem (BitVec.ofNat 64 (0x800 + 8)) = sig.rho.extractLsb' 64 64 := by
          rw [g83 _ (by decide) (by decide) (nLW _ (by decide)), f3.get (by decide) (n49 _ (by decide) (by decide)),
            f2.get (by decide) (ndW _ (by decide) (by decide) (by decide)), show 0x800 + 8 = 0x808 from rfl, w808]
          exact hrho.2
        have h0 := hhalf 0; have h1 := hhalf 1; have h2 := hhalf 2; have h3 := hhalf 3
        simp only [HalfAt, lD, lk] at h0 h1 h2 h3
        try simp only [Nat.mul_zero, Nat.mul_one] at h0 h1 h2 h3
        rw [r0, r8, show 0x800 + 16 = 0x810 from rfl, halves 0x810 _ _ c0 h0,
          show 0x800 + 24 = 0x818 from rfl, halves 0x818 _ _ h1 h2,
          show 0x800 + 32 = 0x820 from rfl, halves 0x820 _ _ h3 c20,
          hz8 (0x800 + 40) (by decide) (by decide), hz8 (0x800 + 48) (by decide) (by decide),
          hz8 (0x800 + 56) (by decide) (by decide)]
        simp
      have hlay : ∀ lay : T3.Layer, t8.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
          wordsOf (layerBytes lay (T3.route (N.toNat % 2 ^ 31) lay).1 (sig.layers lay)) := by
        intro lay
        have hout := hout8 lay (by omega)
        obtain ⟨hWM, hWC⟩ := lBase_eq lay
        have hlo := ltable_lo lay
        have htab := ltable lay
        refine layer_words t8 lay _ _ (fun i h => ?_) (fun j h => ?_) (fun A h1 h2 hn => ?_)
        · have e : lval sig lay i = (sig.layers lay).values ⟨i, h⟩ := by unfold lval; rw [dif_pos h]
          rw [← e]; exact hout.2.1 i h
        · have e : lpath sig lay j = (sig.layers lay).path ⟨j, h⟩ := by unfold lpath; rw [dif_pos h]
          rw [← e]; exact hout.2.2 j h
        · have hA : 0x3418 ≤ A ∧ A < 0x6A98 := by
            constructor
            · have : 0x3418 ≤ lBase lay := by fin_cases lay <;> decide
              omega
            · have : lBase lay + 64 * (height lay + chainCount lay) ≤ 0x6A98 := by fin_cases lay <;> decide
              omega
          have nLW' : ¬ LW index 4 A := by
            rintro (h | h | ⟨lay', _, h | h⟩)
            · unfold Search.CsW Search.DigW at h; simp only [ENC, Search.EOUT, Search.DIGITS] at h; omega
            · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
            · have := (ltable lay').2.2.2.2.2.2.2.2.1; omega
            · by_cases he : lay' = lay
              · subst he; exact hn h
              · have hr := rlWit_range h
                obtain ⟨hWM', hWC'⟩ := lBase_eq lay'
                rcases ltable_disj lay' lay he with hd | hd <;> omega
          rw [g87 A (by omega) nLW', hm7' A (by omega) (by omega) (by simp only [DIG]; omega) (by simp only [NBUF]; omega)
            (by simp only [Search.SEL]; omega) (by simp only [IDXV]; omega) (by omega) (by simp only [NODE]; omega)
            (by simp only [FLEAF]; omega) (by simp only [FOREST]; omega) (by simp only [FOUT]; omega)
            (by simp only [ENC]; omega) (by simp only [ENC]; omega), hz0 A (by omega) (by omega) (by omega) (by omega)]
      exact witList_words t8 N ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ hh hleaf8 hstream8 hlay
    · simp only [ne_eq, heq, not_false_eq_true, ↓reduceIte]
      by_cases h0 : root'.extractLsb' 0 64 = pk.extractLsb' 0 64
      · rw [if_pos (hlo.mpr h0)] at p9
        obtain ⟨t10, st10, p10, r10, f10⟩ := c348_spec t9 p9 x28 x29
        have h1 : ¬ root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := fun h => heq (hsplit.mpr ⟨h0, h⟩)
        rw [if_neg (fun h => h1 (hhi.mp h))] at p10
        obtain ⟨t11, st11, p11, x5_11, x10_11, _⟩ := cs0_spec kernAt_expand t10 p10
        exact (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure (Q := ExpQ) (a := none)
          ⟨p11, x5_11, x10_11⟩)).mono (by omega) (fun _ _ h => h)
      · rw [if_neg (fun h => h0 (hlo.mp h))] at p9
        obtain ⟨t10, st10, p10, x5_10, x10_10, _⟩ := cs0_spec kernAt_expand t9 p9
        exact (TBSim.steps (st9.trans st10) (TBSim.pure (Q := ExpQ) (a := none)
          ⟨p10, x5_10, x10_10⟩)).mono (by omega) (fun _ _ h => h)
  · rw [← htz, if_neg hz] at hif
    simp only [Bool.not_eq_true] at hz
    simp only [hz, Bool.not_false, ↓reduceIte]
    exact (TBSim.steps (st5.trans st6) (TBSim.pure (Q := ExpQ) (a := none) hif)).mono (by omega)
      (fun _ _ h => h)

end run

end SigGolfCandidate.T3M.Expand
