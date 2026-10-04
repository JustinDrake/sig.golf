import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack
import SigGolfCandidate.T3M.Expand.Layers
import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.T3M.ImageSlice
import SigGolfCandidate.T3M.Images.DataPartsExpand
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Defs
import SigGolfCandidate.T3M.Verify.Code
import SigGolfCandidate.ClaudeWCT.W9.T3M.Final.Pending
import SigGolfCandidate.T3M.Sign.WctFinal
import SigGolfCandidate.T3M.Submission

section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Layer height chainCount route)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC OutAt FailedAt TOP_DATA TableOK KernAt NODE NOUT EOUT DIGITS)
open SigGolfCandidate.T3M.Expand (IDXV LInv LPost lcost lP lD lk lWC lWM lBase LW LZero SigLayersAt HalfAt
  RlScratch RlWit entryOf layer_words readWords_zero headerBytes_words ltable ltable_lo ltable_disj rlWit_range
  lBase_eq lval lpath sideOff CHAIN LEAFPK)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec sigDigests_layValue sigDigests_layPath)
set_option linter.unusedSimpArgs false
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
def ExpQW : Option (HashOutput × WCT9.Witness) → MachineState → Prop
  | none, t => FailedAt 354 t ∨ FailedAt 1418 t
  | some (N, w), t => t.pc = pcOf 353 ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.readWords (BitVec.ofNat 64 0x800) 3033 = wordsOf (ClaudeWCT.W9.T3M.witList N w)
def expCostW : Nat := 30 + newCost + (lcost 4 + 11)
theorem lcost_four : lcost 4 ≤ 2831226883 := by decide
theorem expCostW_lt : expCostW + 1 < CYCLE_LIMIT := by
  have h := lcost_four
  unfold expCostW newCost CYCLE_LIMIT
  omega
theorem hookAt_of_front {im : Image} (hF : FrontAt im) : HookAt im :=
  codeAt_appR (n := 0) (a := SigGolfCandidate.T3M.Expand.seg_0) hF (by decide)
theorem lP_eq (lay : Layer) : lP lay = 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 127) ∧ 127 ≤ ClaudeWCT.W9.T3M.layIdx lay ∧
    ClaudeWCT.W9.T3M.layIdx lay + chainCount lay + height lay ≤ 341 := by
  fin_cases lay <;> decide
def FrontW (A : Nat) : Prop :=
  A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56
section run
variable {sk : BitVec 256}
theorem expandW_tbsim {im : Image} (hc : NewCodeAt im) (hF : FrontAt im) (hd : ExpandDataOK im)
    (hB : BackSpec im) (m : Message) (pk : PublicKey) (σ : Bytes 5456) :
    TBSim im sk (w9init im m pk σ) expCostW (ClaudeWCT.W9.T3M.expandN m pk (sigDec σ)) ExpQW := by
  set sig := sigDec σ with hsig
  set s0 := w9init im m pk σ with hs0
  obtain ⟨t1, st1, hpre, w800, w808, f1⟩ := front_pre30 hF hd m pk σ
  have hz0 : ∀ A, A < HB0 → (A < 0x7000 ∨ 0x7000 + 5456 ≤ A) → (A < 0xA0 ∨ 0xB0 ≤ A) → (A < 0x40 ∨ 0x60 ≤ A) →
      s0.getMem (BitVec.ofNat 64 A) = 0 := fun A hA h1 h2 h3 => w9init_zero hd m pk σ A hA ⟨h1, h2, h3⟩
  unfold HB0 at hz0
  rw [expandN_split]
  refine (TBSim.steps st1 (TBSim.bind (W₂ := lcost 4 + 11)
    (newCodeSpec_holds hc (hookAt_of_front hF) sk m sig t1 hpre) (fun r t7 h7 => ?_))).mono
    (by unfold expCostW; omega) (fun _ _ h => h)
  rcases r with _ | ⟨counter, N, root⟩
  · exact (TBSim.pure (Q := ExpQW) (a := none) (Or.inr h7)).mono (by omega) (fun _ _ h => h)
  have P := h7
  simp only [NewPost] at P
  set index := N.toNat % 2 ^ 31 with hindex
  have hi : index < 2 ^ 31 := Nat.mod_lt _ (by positivity)
  have F7 : Frame s0 t7 (fun A => FrontW A ∨ NewW A) := f1.trans P.frame
  have g7 : ∀ A, A < 2 ^ 64 → ¬ FrontW A → ¬ NewW A → t7.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => F7 A hA (fun h => h.elim h1 h2)
  have nFW : ∀ A, (A < 0x800 ∨ 0x810 ≤ A) → (A < DIG ∨ DIG + 64 ≤ A) → ¬ FrontW A := by
    intro A h1 h2 h; unfold FrontW at h; simp only [DIG] at h h2; omega
  have nNW : ∀ A, A ≠ 0x810 → (A < 0x60 ∨ 0x80 ≤ A) → (A < 0x100 ∨ 0x120 ≤ A) → (A < 0x700 ∨ 0x7c0 ≤ A) →
      (A < 0x840 ∨ 0x3148 ≤ A) → (A < 0x7890 ∨ 0x85f0 ≤ A) → (A < DIG + 16 ∨ DIG + 32 ≤ A) →
      (A < NBUF ∨ NBUF + 32 ≤ A) → A ≠ IDXV → A ≠ ENC → A ≠ ENC + 8 → ¬ NewW A := by
    intro A h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h
    unfold NewW at h; simp only [DIG, NBUF, IDXV, ENC] at h h7 h8 h9 h10 h11; omega
  have hT3 : (WCT9.toT3Signature sig).layers = sig.layers := rfl
  have hL : LInv (WCT9.toT3Signature sig) index 4 root t7 := by
    refine ⟨by rw [P.pc]; rfl, le_refl _, P.x5, hi, P.idx, P.enc, ⟨0, by norm_num, ?_⟩, ?_, ?_, ?_⟩
    · rw [g7 _ (by decide) (nFW _ (by decide) (by decide))
        (nNW _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)), hz0 _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    · intro lay
      obtain ⟨hP, h127, hlen⟩ := lP_eq lay
      refine ⟨fun i hi' => ?_, fun j hj => ?_⟩
      · have hd := P.layers (ClaudeWCT.W9.T3M.layIdx lay - 127 + i) (by omega)
        rw [show 127 + (ClaudeWCT.W9.T3M.layIdx lay - 127 + i) = ClaudeWCT.W9.T3M.layIdx lay + i by omega, sigDigests_layValue sig lay i hi',
          show 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 127 + i) = lP lay + 16 * i by rw [hP]; ring] at hd
        exact hd
      · have hd := P.layers (ClaudeWCT.W9.T3M.layIdx lay - 127 + (chainCount lay + j)) (by omega)
        rw [show 127 + (ClaudeWCT.W9.T3M.layIdx lay - 127 + (chainCount lay + j)) = ClaudeWCT.W9.T3M.layIdx lay + (chainCount lay + j) by omega,
          sigDigests_layPath sig lay j hj,
          show 0x7000 + 2192 + 16 * (ClaudeWCT.W9.T3M.layIdx lay - 127 + (chainCount lay + j)) = lP lay + 16 * chainCount lay + 16 * j by
            rw [hP]; ring] at hd
        exact hd
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      · rw [g7 _ (by decide) (nFW _ (by decide) (by decide))
          (nNW _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide)), hz0 _ (by decide) (by decide) (by decide) (by decide)]
    · apply (w9init_table hd m pk σ).frame F7
      intro i hi h
      rcases h with h | h
      · unfold FrontW at h; simp only [TOP_DATA, DIG] at h; omega
      · unfold NewW at h; simp only [TOP_DATA, DIG, NBUF, IDXV, ENC] at h; omega
  simp only [tailProg]
  refine (TBSim.bind (W₂ := 11) (hB.1 sk (WCT9.toT3Signature sig) index root t7 hL) (fun r8 t8 h8 => ?_)).mono
    (by omega) (fun _ _ h => h)
  rcases r8 with _ | ⟨root', counters⟩
  · exact (TBSim.pure (Q := ExpQW) (a := none) (Or.inl h8)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p8, x5_8, e8, hlen8, hout8, hhf8, r8, f8⟩ := h8
  have g87 : ∀ A, A < 2 ^ 64 → ¬ LW index 4 A → t8.getMem (BitVec.ofNat 64 A) = t7.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => f8.get hA h
  have hpk : ∀ j < 2, t8.getMem (BitVec.ofNat 64 (0xA0 + 8 * j)) = pk.extractLsb' (64 * j) 64 := by
    intro j hj
    have nLW : ¬ LW index 4 (0xA0 + 8 * j) := by
      rintro (h | h | ⟨lay, _, h | h⟩)
      · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
      · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
      · have := (ltable lay).2.2.2.2.2.2.2.2.2.1; omega
      · have := rlWit_range h; have := ltable_lo lay; omega
    rw [g87 _ (by omega) nLW, g7 _ (by omega) (nFW _ (by omega) (by simp only [DIG]; omega))
      (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG]; omega)
        (by simp only [NBUF]; omega) (by simp only [IDXV]; omega) (by simp only [ENC]; omega)
        (by simp only [ENC]; omega))]
    exact w9init_pk hd m pk σ j hj
  obtain ⟨t9, st9, p9, x28, x29, r9, f9⟩ := c342W hB.2.1 t8 p8
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
    obtain ⟨t10, st10, p10, r10, f10⟩ := c348W hB.2.1 t9 p9 x28 x29
    rw [if_pos (hhi.mpr h1.2)] at p10
    obtain ⟨t11, st11, p11, x5_11, x10_11, _, r11, f11⟩ := c351W hB.2.1 t10 p10
    refine (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure ⟨p11, x5_11, x10_11, ?_⟩)).mono (by omega)
      (fun _ _ h => h)
    have f811 : Frame t8 t11 (fun _ => False) := ((f9.trans f10).trans f11).mono (fun _ _ h => by
      rcases h with (h | h) | h <;> exact h)
    rw [frame_readWords f811 0x800 3033 (by decide) (fun _ _ h => h)]
    have nLW : ∀ A, (A < 0x810 ∨ (0x828 ≤ A ∧ A < 0x3148)) → ¬ LW index 4 A := by
      intro A hA h
      rcases h with h | h | ⟨lay, _, h | h⟩
      · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
      · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
      · have := (ltable lay).2.2.2.2.2.2.2.2.2.1; have := (ltable lay).2.2.2.2.2.2.2.2.1; omega
      · have := rlWit_range h; have := ltable_lo lay; omega
    set w : WCT9.Witness := ⟨sig, counter, fun lay => counters.getD lay.val 0⟩ with hw
    have hdw : ∀ D, (D = 0x810 ∨ D = 0x818 ∨ D = 0x820) → ∀ k, k < 2 →
        (∀ lay : Layer, lay.val < 4 → ¬ (lD lay = D ∧ lk lay = k)) →
        (t8.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 =
          (t7.getMem (BitVec.ofNat 64 D)).extractLsb' (32 * k) 32 := by
      intro D hD k hk hn
      exact hhf8 D k hD hk hn
    have c0 : (t8.getMem (BitVec.ofNat 64 0x810)).extractLsb' 0 32 = counter := by
      have := hdw 0x810 (Or.inl rfl) 0 (by decide) (fun lay _ h => by
        revert h; fin_cases lay <;> simp [lD, lk])
      simp only [Nat.mul_zero] at this
      rw [this]; exact P.dc
    have c20 : (t8.getMem (BitVec.ofNat 64 0x820)).extractLsb' 32 32 = 0 := by
      have := hdw 0x820 (Or.inr (Or.inr rfl)) 1 (by decide) (fun lay _ h => by
        revert h; fin_cases lay <;> simp [lD, lk])
      simp only [Nat.mul_one] at this
      rw [this, g7 _ (by decide) (nFW _ (by decide) (by decide))
        (nNW _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)), hz0 _ (by decide) (by decide) (by decide) (by decide)]
      rfl
    have hhalf : ∀ lay : Layer, HalfAt t8 (lD lay) (lk lay) (counters.getD lay.val 0) :=
      fun lay => (hout8 lay (by omega)).1
    have halves : ∀ D lo hi, (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 0 32 = lo →
        (t8.getMem (BitVec.ofNat 64 D)).extractLsb' 32 32 = hi →
        t8.getMem (BitVec.ofNat 64 D) = BitVec.ofNat 64 (lo.toNat + 2 ^ 32 * hi.toNat) := by
      intro D lo hi h1 h2
      rw [dword_of_halves (t8.getMem (BitVec.ofNat 64 D)), h1, h2]
    have hz8 : ∀ A, 0x828 ≤ A → A < 0x840 → t8.getMem (BitVec.ofNat 64 A) = 0 := by
      intro A h1 h2
      rw [g87 A (by omega) (nLW A (by omega)), g7 A (by omega) (nFW _ (by omega) (by simp only [DIG]; omega))
        (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG]; omega)
          (by simp only [NBUF]; omega) (by simp only [IDXV]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega)), hz0 _ (by omega) (by omega) (by omega) (by omega)]
    have hh : t8.readWords (BitVec.ofNat 64 0x800) 8 = wordsOf (ClaudeWCT.W9.T3M.headerBytes w) := by
      rw [headerW_eq, headerBytes_words, readWords_eight]
      have r0 : t8.getMem (BitVec.ofNat 64 0x800) = sig.rho.extractLsb' 0 64 := by
        rw [g87 _ (by decide) (nLW _ (by decide)), P.frame _ (by decide) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
        exact w800
      have r8 : t8.getMem (BitVec.ofNat 64 (0x800 + 8)) = sig.rho.extractLsb' 64 64 := by
        rw [g87 _ (by decide) (nLW _ (by decide)), P.frame _ (by decide) (by unfold NewW; simp only [DIG, NBUF, IDXV, ENC]; omega)]
        exact w808
      have h0 := hhalf 0; have h1 := hhalf 1; have h2 := hhalf 2; have h3 := hhalf 3
      simp only [HalfAt, lD, lk] at h0 h1 h2 h3
      try simp only [Nat.mul_zero, Nat.mul_one] at h0 h1 h2 h3
      rw [r0, r8, show 0x800 + 16 = 0x810 from rfl, halves 0x810 _ _ c0 h0,
        show 0x800 + 24 = 0x818 from rfl, halves 0x818 _ _ h1 h2,
        show 0x800 + 32 = 0x820 from rfl, halves 0x820 _ _ h3 c20,
        hz8 (0x800 + 40) (by decide) (by decide), hz8 (0x800 + 48) (by decide) (by decide),
        hz8 (0x800 + 56) (by decide) (by decide)]
      simp [WCT9.toT3Witness, WCT9.toT3Signature, w]
    have hplaced8 : Placed N sig t8 := fun k i hk hi' => by
      rw [g87 _ (by unfold regBase; omega) (nLW _ (by unfold regBase; omega))]
      exact P.placed k i hk hi'
    have hwct : t8.readWords (BitVec.ofNat 64 0x840) 1152 = wordsOf (ClaudeWCT.W9.T3M.wctBytes N w.signature) :=
      placed_words hplaced8
    have hgap : t8.readWords (BitVec.ofNat 64 0x2c40) 161 = List.replicate 161 0 := by
      apply readWords_zero t8 0x2c40 161 (by decide)
      intro j hj
      rw [g87 _ (by omega) (nLW _ (by omega))]
      exact P.gap _ (by omega) (by omega)
    have g8L : ∀ A, 0x3148 ≤ A → A < 0x66C8 → ¬ LW index 4 A → t8.getMem (BitVec.ofNat 64 A) = 0 := by
      intro A h1 h2 hn
      rw [g87 A (by omega) hn, g7 A (by omega) (nFW _ (by omega) (by simp only [DIG]; omega))
        (nNW _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by simp only [DIG]; omega)
          (by simp only [NBUF]; omega) (by simp only [IDXV]; omega) (by simp only [ENC]; omega)
          (by simp only [ENC]; omega)), hz0 _ (by omega) (by omega) (by omega) (by omega)]
    have hlay : ∀ lay : Layer, t8.readWords (BitVec.ofNat 64 (lBase lay)) (8 * (height lay + chainCount lay)) =
        wordsOf (layerBytes lay (route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) := by
      intro lay
      have hout := hout8 lay (by omega)
      obtain ⟨hWM, hWC⟩ := lBase_eq lay
      have hlo := ltable_lo lay
      have htab := ltable lay
      refine layer_words t8 lay _ _ (fun i h => ?_) (fun j h => ?_) (fun A h1 h2 hn => ?_)
      · have e : lval (WCT9.toT3Signature sig) lay i = (sig.layers lay).values ⟨i, h⟩ := by unfold lval; rw [dif_pos h]; rfl
        rw [← e]; exact hout.2.1 i h
      · have e : lpath (WCT9.toT3Signature sig) lay j = (sig.layers lay).path ⟨j, h⟩ := by unfold lpath; rw [dif_pos h]; rfl
        rw [← e]; exact hout.2.2 j h
      · have hA : 0x3148 ≤ A ∧ A < 0x66C8 := by
          constructor
          · have : 0x3148 ≤ lBase lay := by fin_cases lay <;> decide
            omega
          · have : lBase lay + 64 * (height lay + chainCount lay) ≤ 0x66C8 := by fin_cases lay <;> decide
            omega
        have nLW' : ¬ LW index 4 A := by
          rintro (h | h | ⟨lay', _, h | h⟩)
          · unfold Search.CsW Search.DigW at h; simp only [ENC, EOUT, DIGITS] at h; omega
          · unfold RlScratch at h; simp only [CHAIN, NODE, NOUT, LEAFPK, ENC] at h; omega
          · have := (ltable lay').2.2.2.2.2.2.2.2.1; omega
          · by_cases he : lay' = lay
            · subst he; exact hn h
            · have hr := rlWit_range h
              obtain ⟨hWM', hWC'⟩ := lBase_eq lay'
              rcases ltable_disj lay' lay he with hd | hd <;> omega
        exact g8L A hA.1 hA.2 nLW'
    exact witListW_words t8 N w hh hwct hgap hlay
  · simp only [ne_eq, heq, not_false_eq_true, ↓reduceIte]
    by_cases h0 : root'.extractLsb' 0 64 = pk.extractLsb' 0 64
    · rw [if_pos (hlo.mpr h0)] at p9
      obtain ⟨t10, st10, p10, r10, f10⟩ := c348W hB.2.1 t9 p9 x28 x29
      have h1 : ¬ root'.extractLsb' 64 64 = pk.extractLsb' 64 64 := fun h => heq (hsplit.mpr ⟨h0, h⟩)
      rw [if_neg (fun h => h1 (hhi.mp h))] at p10
      obtain ⟨t11, st11, p11, x5_11, x10_11, _⟩ := Search.cs0_spec hB.2.2 t10 p10
      exact (TBSim.steps (st9.trans (st10.trans st11)) (TBSim.pure (Q := ExpQW) (a := none)
        (Or.inl ⟨p11, x5_11, x10_11⟩))).mono (by omega) (fun _ _ h => h)
    · rw [if_neg (fun h => h0 (hlo.mp h))] at p9
      obtain ⟨t10, st10, p10, x5_10, x10_10, _⟩ := Search.cs0_spec hB.2.2 t9 p9
      exact (TBSim.steps (st9.trans st10) (TBSim.pure (Q := ExpQW) (a := none)
        (Or.inl ⟨p10, x5_10, x10_10⟩))).mono (by omega) (fun _ _ h => h)
end run
theorem expqW_output {imgs : Phase → Image} {N : HashOutput} {w : WCT9.Witness} {t : MachineState}
    (h : t.readWords (BitVec.ofNat 64 0x800) 3033 = wordsOf (ClaudeWCT.W9.T3M.witList N w)) :
    readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t = ClaudeWCT.W9.T3M.witEnc N w :=
  readBuffer_of_words t 0x800 3033 (ClaudeWCT.W9.T3M.witList N w) (by decide) (by decide)
    (ClaudeWCT.W9.T3M.witList_length_eq N w) h
theorem expqW_halt (imgs : Phase → Image) (hc : NewCodeAt (imgs .expand)) (hB : BackSpec (imgs .expand))
    (a : Option (HashOutput × WCT9.Witness)) (t : MachineState) (h : ExpQW a t) :
    fetch ((w9Sub imgs).image .expand) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      (a.map fun x => ClaudeWCT.W9.T3M.witEnc x.1 x.2) =
        (if t.getReg .x10 = 0 then some (readOutput (w9Sub imgs).sizes (w9Sub imgs).layout .expand t) else none) := by
  rcases a with _ | ⟨N, w⟩
  · rcases h with ⟨p, x5, x10⟩ | ⟨p, x5, x10⟩
    · refine ⟨((Search.codeAt_k_2 hB.2.2).fetch t p).trans rfl, x5, ?_⟩
      rw [x10]; rfl
    · refine ⟨((codeAt_1420 hc).fetch t p).trans rfl, x5, ?_⟩
      rw [x10]; rfl
  · obtain ⟨p, x5, x10, hw⟩ := h
    refine ⟨((codeAt_353W hB.2.1).fetch t p).trans rfl, x5, ?_⟩
    rw [x10, if_pos (show (0#64 : BitVec 64) = 0 from rfl), expqW_output hw]; rfl
set_option maxRecDepth 10000 in
theorem expandComposeSpec_holds : ExpandComposeSpec := by
  intro imgs hv hc hF hd hB
  have hsim : ∀ (m : Message) (pk : PublicKey) (σ : Bytes 5456),
      Sim ((w9Sub imgs).image .expand) (w9init (imgs .expand) m pk σ) expCostW
        (mrealize 0 (ClaudeWCT.W9.T3M.expandN m pk (sigDec σ))) ExpQW :=
    fun m pk σ => expandW_tbsim (sk := 0) hc hF hd hB m pk σ
  refine ⟨fun m pk σ => ?_, fun hash m pk σ => ?_⟩
  · exact Sim.run_eq (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ) (hsim m pk σ)
      (Nat.lt_of_succ_lt expCostW_lt) _ (expqW_halt imgs hc hB)
  · obtain ⟨h1, h2⟩ := Sim.runWith (w9Sub imgs) .expand (m, pk, σ) (initialState_w9 imgs hv m pk σ)
      (hsim m pk σ) expCostW_lt (fun a t h => ⟨(expqW_halt imgs hc hB a t h).1, (expqW_halt imgs hc hB a t h).2.1⟩) hash
    exact ⟨h1, lt_of_le_of_lt h2 expCostW_lt⟩
end ClaudeWCT.W9.Machine.Expand
end

section





namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (BackSpec compareCode)
theorem wct_compareCode : CodeAt image (pcOf 342) compareCode := by
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
theorem wct_backSpec : BackSpec Images.expandImage := by
  exact ⟨fun sk sig index value s h => layers_tbsim 4 value s h, wct_compareCode, Search.kernAt_expand⟩
theorem wct_headerBank : Images.expandPrefixData =
    ClaudeWCT.W9.Machine.Expand.hdrBankBytes := by
  set_option maxRecDepth 100000 in decide +kernel
theorem wct_expandData : Images.expandImage.data =
    ClaudeWCT.W9.Machine.Expand.hdrBankBytes ++ Images.expandLegacyData := by
  change Images.expandPrefixData ++ Images.expandLegacyData = _
  rw [wct_headerBank]
theorem wct_frontAt : ClaudeWCT.W9.Machine.Expand.FrontAt Images.expandImage := by
  apply codeAt_slice
  · decide +kernel
  · decide +kernel
end SigGolfCandidate.T3M.Expand
end

section


namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open ClaudeWCT.W9.Machine.Expand (NewCodeAt expChunks expChunks_len_le)
set_option maxRecDepth 100000
private def chunks : List (List (BitVec 32)) :=
  [Images.expandCode_0, Images.expandCode_1, Images.expandCode_2, Images.expandCode_3, Images.expandCode_4, Images.expandCode_5, Images.expandCode_6, Images.expandCode_7, Images.expandCode_8, Images.expandCode_9, Images.expandCode_10, Images.expandCode_11, Images.expandCode_12, Images.expandCode_13, Images.expandCode_14, Images.expandCode_15, Images.expandCode_16, Images.expandCode_17, Images.expandCode_18, Images.expandCode_19, Images.expandCode_20, Images.expandCode_21, Images.expandCode_22, Images.expandCode_23, Images.expandCode_24, Images.expandCode_25, Images.expandCode_26, Images.expandCode_27, Images.expandCode_28, Images.expandCode_29, Images.expandCode_30, Images.expandCode_31, Images.expandCode_32, Images.expandCode_33, Images.expandCode_34, Images.expandCode_35, Images.expandCode_36, Images.expandCode_37, Images.expandCode_38, Images.expandCode_39, Images.expandCode_40, Images.expandCode_41, Images.expandCode_42, Images.expandCode_43, Images.expandCode_44, Images.expandCode_45, Images.expandCode_46, Images.expandCode_47, Images.expandCode_48, Images.expandCode_49, Images.expandCode_50, Images.expandCode_51, Images.expandCode_52, Images.expandCode_53, Images.expandCode_54, Images.expandCode_55, Images.expandCode_56, Images.expandCode_57, Images.expandCode_58, Images.expandCode_59, Images.expandCode_60, Images.expandCode_61, Images.expandCode_62, Images.expandCode_63, Images.expandCode_64, Images.expandCode_65, Images.expandCode_66, Images.expandCode_67, Images.expandCode_68, Images.expandCode_69, Images.expandCode_70, Images.expandCode_71, Images.expandCode_72, Images.expandCode_73, Images.expandCode_74, Images.expandCode_75, Images.expandCode_76, Images.expandCode_77, Images.expandCode_78, Images.expandCode_79, Images.expandCode_80, Images.expandCode_81, Images.expandCode_82, Images.expandCode_83, Images.expandCode_84, Images.expandCode_85, Images.expandCode_86, Images.expandCode_87, Images.expandCode_88, Images.expandCode_89, Images.expandCode_90, Images.expandCode_91, Images.expandCode_92, Images.expandCode_93, Images.expandCode_94, Images.expandCode_95, Images.expandCode_96, Images.expandCode_97, Images.expandCode_98, Images.expandCode_99, Images.expandCode_100, Images.expandCode_101, Images.expandCode_102, Images.expandCode_103, Images.expandCode_104, Images.expandCode_105, Images.expandCode_106, Images.expandCode_107, Images.expandCode_108, Images.expandCode_109, Images.expandCode_110, Images.expandCode_111, Images.expandCode_112, Images.expandCode_113, Images.expandCode_114, Images.expandCode_115, Images.expandCode_116, Images.expandCode_117, Images.expandCode_118, Images.expandCode_119, Images.expandCode_120, Images.expandCode_121, Images.expandCode_122, Images.expandCode_123, Images.expandCode_124, Images.expandCode_125, Images.expandCode_126, Images.expandCode_127, Images.expandCode_128, Images.expandCode_129, Images.expandCode_130, Images.expandCode_131, Images.expandCode_132, Images.expandCode_133, Images.expandCode_134, Images.expandCode_135, Images.expandCode_136, Images.expandCode_137, Images.expandCode_138, Images.expandCode_139, Images.expandCode_140, Images.expandCode_141, Images.expandCode_142, Images.expandCode_143, Images.expandCode_144, Images.expandCode_145, Images.expandCode_146, Images.expandCode_147, Images.expandCode_148, Images.expandCode_149, Images.expandCode_150, Images.expandCode_151, Images.expandCode_152, Images.expandCode_153, Images.expandCode_154, Images.expandCode_155, Images.expandCode_156, Images.expandCode_157, Images.expandCode_158, Images.expandCode_159, Images.expandCode_160, Images.expandCode_161, Images.expandCode_162]
private theorem chunks_ok : (chunks.dropLast.all fun c => c.length == 256) = true := by
  decide +kernel
private theorem chunks_length : chunks.length = 163 := by rfl
private theorem chunks_new : expChunks = chunks.drop 4 := by
  decide +kernel
private theorem code_chunks : Images.expandCode = chunks.flatten := by
  change chunks.foldl (· ++ ·) [] = chunks.flatten
  rw [Verify.foldl_append_flatten, List.nil_append]
theorem wct_chunk_prefix {α : Type} (cs : List (List α)) (k : Nat) :
    cs.getD k [] <+: (cs.drop k).flatten := by
  induction cs generalizing k with
  | nil => simp
  | cons c cs ih =>
    cases k with
    | zero => exact ⟨cs.flatten, rfl⟩
    | succ k => simpa using ih k
theorem wct_newCodeAt : NewCodeAt Images.expandImage := by
  intro c hc
  have hlen := expChunks_len_le c hc
  have hp : expChunks.getD c [] <+: Images.expandCode.drop (256 * (c + 4)) := by
    rw [code_chunks, Verify.drop_chunks 256 chunks (c + 4) chunks_ok (by rw [chunks_length]; omega)]
    have hh := wct_chunk_prefix (chunks.drop 4) c
    rw [List.drop_drop] at hh
    rw [chunks_new]
    simpa [Nat.add_comm] using hh
  apply codeAt_slice (by omega)
  change List.take (expChunks.getD c []).length (Images.expandCode.drop (256 * (c + 4))) = _
  obtain ⟨rest, hrest⟩ := hp
  rw [← hrest, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
end SigGolfCandidate.T3M.Expand
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 100000 in
theorem expChunks_full : ∀ c, c < 158 → (expChunks.getD c []).length = 256 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_flatten_length : expChunks.flatten.length = 40694 := by decide +kernel
theorem drop_flatten_chunks : ∀ (L : List (List (BitVec 32))) (c : Nat), (∀ i, i < c → (L.getD i []).length = 256) →
    c ≤ L.length → L.flatten.drop (256 * c) = (L.drop c).flatten
  | L, 0, _, _ => by simp
  | [], c + 1, _, h => by simp at h
  | a :: L, c + 1, h, hl => by
    have ha : a.length = 256 := by simpa using h 0 (by omega)
    rw [List.flatten_cons, List.drop_append, List.drop_eq_nil_of_le (by rw [ha]; omega), List.nil_append, ha,
      show 256 * (c + 1) - 256 = 256 * c by ring_nf; omega,
      drop_flatten_chunks L c (fun i hi => by simpa using h (i + 1) (by omega)) (by simp at hl; omega)]
    rfl
theorem newCodeAt_of_drop {im : Image} (h : im.code.drop 1024 = expChunks.flatten) : NewCodeAt im := by
  intro c hc
  have hpc : (pcOf (256 * (c + 4))).toNat = 0x1000 + 4 * (256 * (c + 4)) := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen := expChunks_len_le c hc
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * (256 * (c + 4)) - 0x1000) / 4 = 1024 + 256 * c by omega, ← List.drop_drop, h,
    drop_flatten_chunks expChunks c (fun i hi => expChunks_full i (by omega)) (by rw [expChunks_length]; omega)]
  rw [List.drop_eq_getElem_cons (by rw [expChunks_length]; omega), List.flatten_cons,
    ← List.getD_eq_getElem _ [] (by rw [expChunks_length]; omega)]
  exact List.prefix_append _ _
theorem expand_pending (I : ClaudeWCT.W9.T3M.Images)
    (hv : I.expand.Valid (ClaudeWCT.W9.T3M.submission I).sizes (ClaudeWCT.W9.T3M.submission I).layout)
    (hc : NewCodeAt I.expand) (hF : FrontAt I.expand) (hd : ExpandDataOK I.expand) (hB : BackSpec I.expand) :
    ClaudeWCT.W9.T3M.Final.ExpandRefines I ∧ ClaudeWCT.W9.T3M.Final.ExpandTerminates I :=
  expandComposeSpec_holds (ClaudeWCT.W9.T3M.submission I).image hv hc hF hd hB
end ClaudeWCT.W9.Machine.Expand
end

section




namespace ClaudeWCT.W9.Machine.ExpandLink
open SigGolfCandidate.T3M
def I0 : ClaudeWCT.W9.T3M.Images := ⟨Images.signImage, Images.expandImage, Images.verifyImage⟩
theorem I0_eq_finalImages : I0 = Sign.Boundary.finalImages := rfl
theorem v2a_valid : I0.expand.Valid (ClaudeWCT.W9.T3M.submission I0).sizes (ClaudeWCT.W9.T3M.submission I0).layout :=
  submission_expand_valid
theorem v2a_dataOK : ClaudeWCT.W9.Machine.Expand.ExpandDataOK I0.expand := Expand.wct_expandData
theorem expand_pending_v2a :
    ClaudeWCT.W9.T3M.Final.ExpandRefines I0 ∧ ClaudeWCT.W9.T3M.Final.ExpandTerminates I0 :=
  ClaudeWCT.W9.Machine.Expand.expand_pending I0 v2a_valid Expand.wct_newCodeAt Expand.wct_frontAt v2a_dataOK
    Expand.wct_backSpec
theorem sign_pending_v2a :
    ClaudeWCT.W9.T3M.Final.SignRefines I0 ∧ ClaudeWCT.W9.T3M.Final.SignTerminates I0 :=
  ⟨Sign.Boundary.wct_final_sign_refines, Sign.Boundary.wct_final_sign_terminates⟩
#print axioms expand_pending_v2a
#print axioms sign_pending_v2a
end ClaudeWCT.W9.Machine.ExpandLink
end
