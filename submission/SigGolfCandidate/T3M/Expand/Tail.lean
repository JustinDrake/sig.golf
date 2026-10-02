import SigGolfCandidate.T3M.Expand.Init
import SigGolfCandidate.T3M.Expand.Layer

/-!
# `expand`: the canonical tail and the forest pk (stream E)

* `zt_loop_spec` : from `zt_loop` (word 216) with `a3 = j`, the machine checks the proof slots `j .. 123` (two
  doublewords each, 12 cycles per slot) and reaches `zt_done` iff they are all zero, else halts through `fail`;
* `forest_tbsim` : from `zt_done` (word 228) with the seven coordinate roots in the forest block, the machine refines
  Core's `forestPk index roots` (one 2-block HASH into `FOUT`) and stops at `layer_3` (word 249) with the pk at `ENC`.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest forestPk shortHash pad64 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (ENC KernAt kernAt_expand cs0_spec FailedAt)

set_option autoImplicit false

theorem dig_eq_zero_iff (d : BitVec 128) : d = 0 ↔ d.extractLsb' 0 64 = 0 ∧ d.extractLsb' 64 64 = 0 := by
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

/-- **The canonical tail** `zt_loop`: proof slots `j .. 123` all zero, else `fail`. -/
theorem zt_loop_spec (proof : Nat → Digest) : ∀ (n j : Nat) (s : MachineState), j + n = 121 →
    s.pc = pcOf 216 → s.getReg .x13 = BitVec.ofNat 64 j →
    (∀ k, j ≤ k → k < 121 → DigAt s (0x7160 + 16 * k) (proof k)) →
    ∃ c t, Steps image s c c t ∧ c ≤ 12 * n + 4 ∧
      (if (List.range n).all (fun i => decide (proof (j + i) = 0)) then
        t.pc = pcOf 228 ∧ RegsExcept s t [.x6, .x13, .x28, .x29] ∧ Frame s t (fun _ => False)
      else FailedAt 354 t)
  | 0, j, s, hj, hpc, h13, _ => by
    obtain ⟨t, st, pt, rt, ft⟩ := s216_spec s hpc j (by omega) h13
    rw [if_pos (by omega)] at pt
    exact ⟨2, t, st, by omega, by simpa using ⟨pt, rt.mono (by decide), ft⟩⟩
  | n + 1, j, s, hj, hpc, h13, hm => by
    obtain ⟨t1, s1, p1, r1, f1⟩ := s216_spec s hpc j (by omega) h13
    rw [if_neg (by omega)] at p1
    have hd := hm j (le_refl _) (by omega)
    obtain ⟨t2, s2, p2, x28, r2, f2⟩ := s218_spec t1 p1 j (by omega) (by rw [r1.get (by decide)]; exact h13)
    have hall : (List.range (n + 1)).all (fun i => decide (proof (j + i) = 0)) =
        (decide (proof j = 0) && (List.range n).all (fun i => decide (proof (j + 1 + i) = 0))) := by
      rw [List.range_succ_eq_map, List.all_cons, List.all_map]
      simp only [Nat.add_zero, Function.comp_def]
      congr 2; funext i; congr 3; omega
    have g1 : t1.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) :=
      f1.get (by omega) (by simp)
    by_cases hlo : t1.getMem (BitVec.ofNat 64 (0x7160 + 16 * j)) = 0
    · rw [if_pos hlo] at p2
      obtain ⟨t3, s3, p3, r3, f3⟩ := s224_spec t2 p2 j (by omega) x28
      have g2 : t2.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = s.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) := by
        rw [f2.get (by omega) (by simp), f1.get (by omega) (by simp)]
      by_cases hhi : t2.getMem (BitVec.ofNat 64 (0x7160 + 16 * j + 8)) = 0
      · rw [if_pos hhi] at p3
        obtain ⟨t4, s4, p4, x13', r4, f4⟩ := s226_spec t3 p3 j (by omega)
          (by rw [r3.get (by decide), r2.get (by decide), r1.get (by decide)]; exact h13)
        have f04 : Frame s t4 (fun _ => False) :=
          (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp_all)
        obtain ⟨c, t, st, hc, ht⟩ := zt_loop_spec proof n (j + 1) t4 (by omega) p4 x13' (fun k hk1 hk2 => by
          exact (hm k (by omega) hk2).frame f04 (by omega) (by simp) (by simp))
        have hz : proof j = 0 := by
          rw [dig_eq_zero_iff]
          rw [g1, hd.1] at hlo
          rw [g2, hd.2] at hhi
          exact ⟨hlo, hhi⟩
        refine ⟨_, t, (((s1.trans s2).trans s3).trans s4).trans st, by omega, ?_⟩
        rw [hall, hz]
        simp only [decide_true, Bool.true_and]
        split_ifs at ht ⊢ with hc'
        · obtain ⟨pt, rt, ft⟩ := ht
          exact ⟨pt, ((((r1.trans r2).trans r3).trans r4).trans rt).mono (by decide),
            (f04.trans ft).mono (fun _ _ h => by rcases h with h | h <;> exact h)⟩
        · exact ht
      · rw [if_neg hhi] at p3
        obtain ⟨t4, s4, p4, h5, h10, _⟩ := cs0_spec kernAt_expand t3 p3
        have hnz : proof j ≠ 0 := by
          intro h
          rw [dig_eq_zero_iff] at h
          rw [g2, hd.2] at hhi
          exact hhi h.2
        refine ⟨_, t4, ((s1.trans s2).trans s3).trans s4, by omega, ?_⟩
        rw [hall]
        simp only [hnz, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact ⟨p4, h5, h10⟩
    · rw [if_neg hlo] at p2
      obtain ⟨t3, s3, p3, h5, h10, _⟩ := cs0_spec kernAt_expand t2 p2
      have hnz : proof j ≠ 0 := by
        intro h
        rw [dig_eq_zero_iff] at h
        rw [g1, hd.1] at hlo
        exact hlo h.1
      refine ⟨_, t3, (s1.trans s2).trans s3, by omega, ?_⟩
      rw [hall]
      simp only [hnz, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact ⟨p3, h5, h10⟩

/-- The forest pk input `root0 | T11 | root1 .. root6` (128 bytes). -/
theorem forestInput_words (index : Nat) (roots : List Digest) (hlen : roots.length = 7) :
    wordsOf (pad64 (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
        (roots.drop 1).flatMap (bytesLE 16))) =
      wordsOf (bytesLE 16 (roots.getD 0 0)) ++
        [BitVec.ofNat 64 (hdr0 11 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] ++
        wordsOf ((roots.drop 1).flatMap (bytesLE 16)) := by
  have hfl : ((roots.drop 1).flatMap (bytesLE 16)).length = 96 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]
  rw [pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, hfl])]
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_header]
  rfl

theorem forestInput_length (index : Nat) (roots : List Digest) (hlen : roots.length = 7) :
    (pad64 (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
        (roots.drop 1).flatMap (bytesLE 16))).length = 128 := by
  have hfl : ((roots.drop 1).flatMap (bytesLE 16)).length = 96 := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen]
  rw [pad64_of_aligned _ (by simp only [List.length_append, bytesLE_length, hfl])]
  simp only [List.length_append, bytesLE_length, hfl]

section forest
variable {sk : BitVec 256}

/-- **The forest pk** (`zt_done` .. `layer_3`): Core's `forestPk index roots`, the pk to `ENC`; 36 cycles. -/
theorem forest_tbsim (index : Nat) (hi : index < 2 ^ 31) (roots : List Digest) (hlen : roots.length = 7)
    (s : MachineState) (hpc : s.pc = pcOf 228) (h9 : s.getReg .x9 = BitVec.ofNat 64 index)
    (h5 : s.getReg .x5 = 0) (hroots : ∀ c < 7, DigAt s (FOREST + slotOff c) (roots.getD c 0)) :
    TBSim image sk s 36 (forestPk index roots)
      (fun root t => t.pc = pcOf 249 ∧ DigAt t ENC root ∧
        RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
        Frame s t (fun A => A = FOREST + 16 ∨ A = FOREST + 24 ∨ (FOUT ≤ A ∧ A < FOUT + 32) ∨ A = ENC ∨
          A = ENC + 8)) := by
  obtain ⟨t1, s1, p1, m16, m24, h10, h11, h12, r1, f1⟩ := s228_spec s hpc index hi h9
  have g1 : ∀ A, A < 2 ^ 64 → A ≠ FOREST + 16 → A ≠ FOREST + 24 →
      t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f1.get hA (by rintro (h | h) <;> contradiction)
  have h0 : DigAt t1 FOREST (roots.getD 0 0) := by
    have := hroots 0 (by decide)
    simp only [slotOff, if_pos rfl, Nat.add_zero] at this
    exact ⟨(g1 _ (by decide) (by decide) (by decide)).trans this.1, (g1 _ (by decide) (by decide) (by decide)).trans this.2⟩
  have hrest : DigsAt t1 (FOREST + 32) (roots.drop 1) := by
    intro c hc
    simp only [List.length_drop, hlen] at hc
    have := hroots (c + 1) (by omega)
    simp only [slotOff, if_neg (show c + 1 ≠ 0 by omega)] at this
    rw [show FOREST + 32 + 16 * c = FOREST + (16 * (c + 1) + 16) by ring]
    have e : (roots.drop 1).getD c 0 = roots.getD (c + 1) 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_comm]
    rw [e]
    exact ⟨(g1 _ (by simp only [FOREST]; omega) (by simp only [FOREST]; omega) (by simp only [FOREST]; omega)).trans
      this.1, (g1 _ (by simp only [FOREST]; omega) (by simp only [FOREST]; omega) (by simp only [FOREST]; omega)).trans
      this.2⟩
  have hw : t1.readWords (BitVec.ofNat 64 FOREST) 16 = wordsOf (pad64 (bytesLE 16 (roots.getD 0 0) ++
      bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16))) := by
    rw [forestInput_words index roots hlen]
    have hd : (roots.drop 1).length = 6 := by simp [hlen]
    have hhd : t1.readWords (BitVec.ofNat 64 (FOREST + 16)) 2 =
        [BitVec.ofNat 64 (hdr0 11 0 index 0), BitVec.ofNat 64 (hdr1 index 0)] := by
      rw [readWords_two, m16, show FOREST + 16 + 8 = FOREST + 24 from rfl, m24,
        hdr0_eq 11 0 index 0 (by decide) (by decide) (by omega) (by decide), hdr1_eq index 0 (by omega) (by decide)]
      simp
    have e16 : t1.readWords (BitVec.ofNat 64 FOREST) 16 =
        t1.readWords (BitVec.ofNat 64 FOREST) (2 + (2 + 2 * (roots.drop 1).length)) := by rw [hd]
    rw [e16, readWords_add, readWords_add, h0.words, hhd, hrest.words]
    simp only [List.append_assoc]
  have hq : hashInput t1 = toQ (pad64 (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
      (roots.drop 1).flatMap (bytesLE 16))) :=
    hashInput_toQ t1 _ 1 FOREST (by rw [forestInput_length index roots hlen]) h10 (by decide) (by decide) h11
      (by decide) hw
  have hv : hashArgumentsValid t1 = true :=
    hashArgs_const t1 FOREST 128 FOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5' : t1.getReg .x5 = 0 := by rw [r1.get (by decide)]; exact h5
  have hblk : (toQ (pad64 (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
      (roots.drop 1).flatMap (bytesLE 16)))).blocks = 2 := by
    rw [blocks_toQ ⟨by rw [forestInput_length index roots hlen]; omega, by rw [forestInput_length index roots hlen]⟩,
      forestInput_length index roots hlen]
  unfold forestPk
  have hprog : shortHash (bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++
      (roots.drop 1).flatMap (bytesLE 16)) = (shortHash (bytesLE 16 (roots.getD 0 0) ++
      bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)) >>= pure) := by rw [bind_pure]
  rw [hprog]
  refine (TBSim.steps s1 (tb_shortHash_bind' (W := 8) (fetch_240 t1 p1) h5' hv hq (fun a => ?_))).mono
    (by rw [hblk]) (fun _ _ h => h)
  have p2 : (writeHash t1 a).pc = pcOf 241 := by rw [pc_writeHash, p1, pcOf_add4]
  obtain ⟨t3, s3, p3, e0, e8, r3, f3⟩ := s241_spec (writeHash t1 a) p2
  have hd := DigAt.writeHash_lo t1 a FOUT h12 (by decide)
  have fw := Frame.writeHash t1 a FOUT h12 (by decide)
  refine TBSim.steps s3 (TBSim.pure ⟨p3, ⟨e0.trans hd.1, e8.trans hd.2⟩, ?_, ?_⟩)
  · have rw0 : RegsExcept t1 (writeHash t1 a) [] := fun r _ => getReg_writeHash t1 a r
    exact ((r1.trans rw0).trans r3).mono (by decide)
  · refine ((f1.trans fw).trans f3).mono (fun A _ h => ?_)
    rcases h with ((h | h) | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

end forest

end SigGolfCandidate.T3M.Expand
