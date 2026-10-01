import SigGolfCandidate.Verify.LayArith
import SigGolfCandidate.Verify.LayerCheck
import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Sign.Enc

/-! # Hypertree layers (W1a): route + encoding, the encoding check and the entry of the chain code

A layer starts at one of the copies of its transition (`preStart lay t`): route and encoding hash,
the check of the encoding, then `li s6, base; sub s9, s11, t3`, the extraction of triple 0 and the
`jalr ra` into the layer-shared chain code (`ChainIn c 0 []`, with the return pc of the copy's leaf
block in `ra`). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure LCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  idx : Nat

def LCtx.ok (L : LCtx) : Prop := L.lay < 5 ∧ L.idx < 2 ^ 34 ∧ L.wl.length = 16384
def LCtx.e (L : LCtx) : Nat := L.idx / 2 ^ layS L.lay % 2 ^ heightL L.lay
def LCtx.tau (L : LCtx) : Nat := L.idx / 2 ^ (layS L.lay + heightL L.lay)
/-- Known registers on entry of a layer (W1a: one list `gkL = gkL0` for all layers; the chain
constants `K40`, `TMASK`, `TTA5` are set once, before layer 4). -/
def LCtx.gk (_L : LCtx) : List (Reg × Word) := gkL0

/-- t0's `CB + 32 .. CB + 48 = 0` (the zero pad of the chain buffer). W1a hashes the chains in place
in their witness blocks and the layers neither read nor write CB, so this conjunct of `LayerIn` is
vacuous; it is kept (with the `0xC0` conjunct) for the shape of the interface with `Top`. -/
def CBZ (_s : MachineState) : Prop := True

/-- At the start of a transition copy of layer `lay`, with the message `M` in EB+32: the chain
array of the layers `≤ lay` is still the witness (`Fresh L.wl L.lay 0`). -/
def LayerIn (L : LCtx) (M : Val) (s : MachineState) : Prop :=
  Glob L.gk L.wl L.pk s ∧ KnownOK (preK L.lay) s ∧
  s.getReg (routeReg L.lay) = BitVec.ofNat 64 (routeIn L.idx L.lay) ∧
  s.getMem (BitVec.ofNat 64 0x120) = vw0 M ∧ s.getMem (BitVec.ofNat 64 0x128) = vw1 M ∧
  M.length = 16 ∧ (L.lay < 4 → CBZ s) ∧ (s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 48 = 0 ∧
  Fresh L.wl L.lay 0 s ∧
  ∃ t, t < nCopy L.lay ∧ s.pc = pcOf (preStart L.lay t)

/-- After the encoding hash of transition copy `t` (answer `a` in EO). -/
def EncOut (L : LCtx) (t : Nat) (a : BitVec 256) (s : MachineState) : Prop :=
  Glob gkL L.wl L.pk s ∧ KnownOK (bK L.lay) s ∧
  s.getReg .x23 = BitVec.ofNat 64 (L.e + 2 ^ heightL L.lay) ∧ s.getReg .x30 = BitVec.ofNat 64 (if L.lay = 0 then L.e else L.tau) ∧
  s.getReg .x31 = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) ∧
  s.getMem (BitVec.ofNat 64 288) = a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 296) = a.extractLsb' 64 64 ∧
  s.getMem (BitVec.ofNat 64 304) = a.extractLsb' 128 64 ∧
  s.getMem (BitVec.ofNat 64 312) = a.extractLsb' 192 64 ∧
  CB0 s ∧ Fresh L.wl L.lay 0 s ∧
  s.pc = pcOf (encPc L.lay t + 1)

/-! ## The per-layer check, by parts -/

section
variable {lay : Nat} (hl : lay < 5)
include hl

theorem lc_copy {t : Nat} (ht : t < nCopy lay) : copyCheck lay t = true := by
  have h := layerCheck_at lay hl
  simp only [layerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.1 t ht

theorem lc_pre {t : Nat} (ht : t < nCopy lay) :
    specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) [] = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  exact h.1.1

theorem lc_enc (hi : Nat) (hhi : hi < 4) {t : Nat} (ht : t < nCopy lay) :
    specOB gkL (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br false, .br false, .jmp])) (specBok hi lay) encObligs
      (chKa lay t) [.x23, .x30, .x31] = true ∧
    specOB [] (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br true])) (specRej1 hi) encObligs [] [] = true ∧
    specOB [] (runAt (bK lay) [] (encPc lay t + 1) (selDirs hi ++ [.br false, .br true])) (specRej2 hi lay) encObligs [] [] = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1.2 hi (List.mem_range.mpr hhi)
  simpa only [halfCheck, Bool.and_eq_true, and_assoc] using hh

theorem lc_leaf {t : Nat} (ht : t < nCopy lay) :
    specB gkL (runAt (leafK lay) [] (retPc lay t) [.jmp]) (specLeaf lay) (leafPost lay) leafKeep = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  exact h.2

theorem lc_cmp {t : Nat} (ht : t < 32) (h0 : lay = 0) :
    specB [] (runAt cmpK [] (cmpPc t) [.br false]) (specAcc t) [] [] = true ∧
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [] = true := by
  have h := layerCheck_at lay hl
  subst h0
  simp only [layerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_self_eq_false,
    Bool.false_or] at h
  exact h.2 t ht

end

theorem e_lt (L : LCtx) (hL : L.ok) : L.e < 2048 := e_lt32 L.lay L.idx hL.1

theorem hWord_lt (lay : Nat) (h : lay < 5) : hWord lay < 2 ^ 32 := by unfold hWord; omega

/-! ## Route and encoding -/

/-- The doubleword holding the layer's counter: `c4` below the chain array (`WitOK`), `c0 .. c3`
in the tweak slot of block `(0, 0)` (fresh at the start of every layer). -/
theorem ctrA_word (L : LCtx) (hL : L.ok) (s : MachineState) (hW : WitOK L.wl s)
    (hF : Fresh L.wl L.lay 0 s) :
    s.getMem (BitVec.ofNat 64 (ctrA L.lay)) = w64 (slice L.wl (ctrA L.lay - 0x800) 8) := by
  obtain ⟨hlay, -, -⟩ := hL
  by_cases h4 : L.lay = 4
  · rw [show ctrA L.lay = 0x800 + 2392 by simp [ctrA, h4]]
    exact wit_word hW 2392 (by decide) (by decide)
  · have e : ctrA L.lay = blkN 0 0 + 8 * (L.lay / 2) := by
      rw [blkN_eq]; simp only [ctrA, if_neg h4] <;> omega
    have e2 : ctrA L.lay - 0x800 = blockOff 0 0 + 8 * (L.lay / 2) := by
      rw [blockOff_eq]; simp only [ctrA, if_neg h4] <;> omega
    rw [e2, e]
    exact hF 0 0 _ (FreshW_ctr hlay (by omega))

theorem enc_step (L : LCtx) (hL : L.ok) (M : Val) (s : MachineState) (hs : LayerIn L M s) :
    ∃ t, t < nCopy L.lay ∧ ∃ u, Steps image s (stepsA L.lay) (stepsA L.lay) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (encInput L.lay L.tau L.e M (witCounter L.wl L.lay)) ∧
      ∀ a, EncOut L t a (writeHash u a) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨hG, hK, hR, hM0, hM1, hMl, -, hC0, hF, t, ht, hpc⟩ := hs
  obtain ⟨u, hu⟩ := spec_run (lc_pre hlay ht) s hpc hK (by simp [specA])
  have hK' := hu.known
  have gk : ∀ p ∈ gkL, p ∈ bK L.lay := fun p hp => by simp [bK, hp]
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x100 := hK' (.x10, 0x100) (by simp [bK])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [bK])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x120 := hK' (.x12, 0x120) (by simp [bK])
  have hx31 : (x31Er L.lay).eval s = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) :=
    x31Er_eval L.idx L.lay hlay hidx s hR
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hmem := hu.mem
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 312 → A ≠ 304 → A ≠ 264 → A ≠ 256 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      simp only [specA, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have hm : ∀ A, u.getMem A = memEval s (specA L.lay t).mem A := hmem
  have hctr := ctrA_word L ⟨hlay, hidx, hwl⟩ s hG.2.1 hF
  refine ⟨t, ht, u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (gk _ (by simp [gkL, gkL0, baseK])),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
  · rw [hashInput_ofNat _ 0x100 0 h10 h11 (by decide) (by decide), pad64_encInput _ _ _ _ hMl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold twLo hWord; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_eq _ _ _ _ _ rfl, hx31]
      congr 1; unfold twHi; omega
    · rw [mfr 0x110 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x118 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x120 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM0
    · rw [mfr 0x128 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM1
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      rw [ctrE_eval L.lay hlay L.wl hwl s hctr, BitVec.toNat_ofNat]
      have := witCounter_lt L.wl L.lay
      omega
    · rw [hm]; simp only [specA]; rw [memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x120 ∨ 0x120 + 32 ≤ A) =>
      writeHash_frame _ a 0x120 A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hu.glob _ _ _ hG) a _ h12 (by decide), Known_writeHash hK' a, ?_, ?_, ?_,
      writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega),
      by simpa using writeHash_getMem_ofNat u a 288 304 h12 (by decide) (by decide),
      by simpa using writeHash_getMem_ofNat u a 288 312 h12 (by decide) (by decide), ?_, ?_, ?_⟩
    · rw [writeHash_getReg, hu.regs (.x23, uHE L.lay) (by simp [specA]), uHE_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x30, carryEr L.lay) (by simp [specA]), carryEr_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x31, x31Er L.lay) (by simp [specA]), hx31]
    · unfold CB0
      rw [wf 0xC0 (by omega) (by omega), mfr 0xC0 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hC0
    · refine Fresh_frame hF (fun A hA hA' => ?_)
      rw [wf A hA (Or.inr (by omega)), mfr A hA (by omega) (by omega) (by omega) (by omega)]
    · rw [writeHash_pc, hu.pc rfl, pcOf_add4]; rfl

/-! ## The encoding check and the entry of the chain code -/

/-- The chain context of layer `L` entered from transition copy `t` with the encoding answer `a`:
the chain code returns to the copy's leaf block. -/
def LCtx.cctx (L : LCtx) (t : Nat) (a : BitVec 256) : CCtx :=
  ⟨L.wl, L.pk, L.lay, L.tau, L.e, (encodingAnswer a).extractLsb' 0 64, (encodingAnswer a).extractLsb' 64 64, pcOf (retPc L.lay t)⟩

theorem pcOf_even (n : Nat) : pcOf n &&& ~~~1#64 = pcOf n := by
  show BitVec.ofNat 64 (0x1000 + 4 * n) &&& ~~~1#64 = BitVec.ofNat 64 (0x1000 + 4 * n)
  exact even_andNot1 _ (by omega)

theorem slice0_answer (a : BitVec 256) : leNat (slice (answerBytes 16 a) 0 8) = (a.extractLsb' 0 64).toNat := by
  rw [← vw0_answer, vw0, w64_toNat _ (by simp)]; rfl

theorem slice8_answer (a : BitVec 256) : leNat (slice (answerBytes 16 a) 8 8) = (a.extractLsb' 64 64).toNat := by
  rw [← vw1_answer, vw1, w64_toNat _ (by simp)]
  simp only [slice]
  rw [List.take_of_length_le (by simp)]

theorem digits_getD (d0 d1 : Nat) (i : Nat) (hi : i < 42) :
    (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 =
      (if i < 21 then d0 else d1) / 8 ^ (i % 21) % 8 := by
  simp only [List.getD_eq_getElem?_getD, digitsOfWord]
  split
  · rw [List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_map, show i < 21 by omega, Nat.mod_eq_of_lt (show i < 21 by omega)]
  · rw [List.getElem?_append_right (by simp; omega), show i % 21 = i - 21 by omega]
    simp [List.getElem?_map, show i - 21 < 21 by omega]

/-- The dispatch of triple 0 from the transition (`slli a4, a6, 9; and sp; add a5; jalr -2048(a4)`,
with `a6` loaded from EO): the table slot of row `kOf c 0`. -/
theorem tgt0_eval (hi : Nat) (c : CCtx) (s : MachineState) (hD : (d0E hi).eval s = c.d0) :
    (tgt0 hi).eval s = pcOf (entW 0 (kOf c 0)) := by
  have hk : kOf c 0 < 512 := by
    unfold kOf; have := dig_lt c (3 * 0); have := dig_lt c (3 * 0 + 1); have := dig_lt c (3 * 0 + 2); omega
  have hrow : c.d0.toNat % 512 = kOf c 0 := by
    have := triRow c 0 (by decide)
    simpa [triW] using this
  simp only [tgt0, E.eval, BinOp.eval, hD, cw]
  have e : (c.d0 <<< ((BitVec.ofNat 64 9).toNat % 64) &&& TMASK) + BitVec.ofNat 64 0x4f800 =
      BitVec.ofNat 64 (0x1000 + 4 * entW 0 (kOf c 0)) := by
    have h0 := congrArg BitVec.toNat (tri_case0 c.d0)
    rw [hrow] at h0
    have ht := ttab_pc 0 (kOf c 0)
    apply BitVec.eq_of_toNat_eq
    generalize (c.d0 <<< ((BitVec.ofNat 64 9).toNat % 64) &&& TMASK) = X at h0 ⊢
    have hX := X.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, TTA5_toNat] at h0 ⊢
    omega
  rw [e, even_andNot1 _ (by omega)]
  rfl

theorem encpost_step (L : LCtx) (hL : L.ok) (t : Nat) (ht : t < nCopy L.lay) (a : BitVec 256) (s : MachineState)
    (hs : EncOut L t a s) :
    (decodeDigits L.lay (encodingBytes a) = none →
      ∃ k, k ≤ 33 ∧ ∃ c, c ≤ 33 ∧ ∃ u, Steps image s k c u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (∀ xs, decodeDigits L.lay (encodingBytes a) = some xs →
      ∃ u, Steps image s (stepsBPath (selOf a) L.lay) (cyclesBPath (selOf a) L.lay) u ∧ ChainIn (L.cctx t a) 0 [] u ∧
        (L.cctx t a).ok ∧ (∀ i < 42, xs.getD i 0 = dig (L.cctx t a) i) ∧ xs.sum = targetFor L.lay ∧
        xs.length = 42) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  let hi := selOf a
  have hhi : hi < 4 := by unfold hi selOf; split_ifs <;> omega
  have hsteps : selSteps hi ≤ 7 := by unfold selSteps; split_ifs <;> omega
  obtain ⟨hBok, hR1, hR2⟩ := lc_enc hlay hi hhi ht
  obtain ⟨hG, hK, h23, h30, h31, w0, w1, w2, w3, hCB, hF, hpc⟩ := hs
  have hD0 : (d0E hi).eval s = (encodingAnswer a).extractLsb' 0 64 := by
    have hw := Sign.encoding_word a 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at hw
    rw [hw]
    cases h127 : a[127] <;> cases h63 : a[63] <;>
      by_cases hg : 125 ≤ a.toNat >>> 55 % 512 <;>
      simp [hi, selOf, d0E, h127, h63, hg, ldE, cw, E.eval, w0, w1, w2]
  have hD1 : (d1E hi).eval s = (encodingAnswer a).extractLsb' 64 64 := by
    have hw := Sign.encoding_word a 1 (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at hw
    rw [hw]
    cases h127 : a[127] <;> cases h63 : a[63] <;>
      by_cases hg : 125 ≤ a.toNat >>> 55 % 512 <;>
      simp [hi, selOf, d1E, h127, h63, hg, ldE, cw, E.eval, w1, w2, w3]
  have hsel : ∀ b ∈ selBrs hi, b.holds s := by
    have htop : (a.toNat % 18446744073709551616) >>> 55 = a.toNat >>> 55 % 512 := by
      simpa using Sign.encoding_top9_toNat a
    intro b hb
    simp only [selBrs, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    all_goals
      cases h127 : a[127] <;> cases h63 : a[63] <;>
        by_cases hg : 125 ≤ a.toNat >>> 55 % 512 <;>
        simp [hi, selOf, selLow, selSecond, h127, h63, hg, Br.holds, CmpOp.eval,
          ldE, cw, E.eval, BinOp.eval, w0, w1, BitVec.slt_zero_eq_msb, BitVec.msb,
          BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_extractLsb', BitVec.ult, Sign.encoding_top9_toNat] <;> omega
  have hor : CmpOp.lt.eval ((orE hi).eval s) ((E.c 0).eval s) =
      decide (2 ^ 63 ≤ ((encodingAnswer a).extractLsb' 0 64).toNat ∨ 2 ^ 63 ≤ ((encodingAnswer a).extractLsb' 64 64).toNat) := by
    rw [show (orE hi).eval s = (d0E hi).eval s ||| (d1E hi).eval s from rfl,
      hD0, hD1]
    exact lt_or_eval _ _
  have hdA : dA hi s = ((encodingAnswer a).extractLsb' 0 64).toNat := by simp only [dA, hD0]
  have hdB : dB hi s = ((encodingAnswer a).extractLsb' 64 64).toNat := by simp only [dB, hD1]
  have hT : targetFor L.lay < 2 ^ 64 := by have := targetFor_le L.lay; omega
  unfold encodingBytes decodeDigits
  simp only [slice0_answer, slice8_answer]
  simp only [← show targetFor L.lay = Ref.targetFor L.lay from rfl]
  constructor
  · intro hnone
    by_cases hlt : ((encodingAnswer a).extractLsb' 0 64).toNat < 2 ^ 63 ∧ ((encodingAnswer a).extractLsb' 64 64).toNat < 2 ^ 63
    · rw [if_pos hlt] at hnone
      have hsum : ¬ (digitsOfWord ((encodingAnswer a).extractLsb' 0 64).toNat ++ digitsOfWord ((encodingAnswer a).extractLsb' 64 64).toNat).sum
          = targetFor L.lay := by intro h; rw [if_pos h] at hnone; cases hnone
      obtain ⟨u, hu⟩ := specO_run hR2 s hpc hK (encObligs_holds s) (by
        intro b hb
        simp only [specRej2, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with (rfl | rfl) | hb
        · simp only [Br.holds, CmpOp.eval, bne_iff_ne, ne_eq]
          intro h
          apply hsum
          have := (swS_eq hi s L.lay (by omega) (by omega)).mp h
          rwa [hdA, hdB] at this
        · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega)
        · exact hsel _ hb)
      exact ⟨19 + selSteps hi, by omega,
        22 + selSteps hi, by omega, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej2, rejK]),
        hu.regs (.x10, cw 1) (by simp [specRej2, rejK])⟩
    · obtain ⟨u, hu⟩ := specO_run hR1 s hpc hK (encObligs_holds s) (by
        intro b hb
        simp only [specRej1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | hb
        · simp only [Br.holds]; rw [hor]; exact decide_eq_true (by omega)
        · exact hsel _ hb)
      exact ⟨selSteps hi + 5, by omega, selSteps hi + 5, by omega, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej1, rejK]),
        hu.regs (.x10, cw 1) (by simp [specRej1, rejK])⟩
  · intro xs hxs
    by_cases hlt : ((encodingAnswer a).extractLsb' 0 64).toNat < 2 ^ 63 ∧ ((encodingAnswer a).extractLsb' 64 64).toNat < 2 ^ 63
    · rw [if_pos hlt] at hxs
      by_cases hsum : (digitsOfWord ((encodingAnswer a).extractLsb' 0 64).toNat ++
          digitsOfWord ((encodingAnswer a).extractLsb' 64 64).toNat).sum = targetFor L.lay
      · rw [if_pos hsum] at hxs
        cases hxs
        obtain ⟨u, hu⟩ := specO_run hBok s hpc hK (encObligs_holds s) (by
          intro b hb
          simp only [specBok, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with (rfl | rfl) | hb
          · simp only [Br.holds, CmpOp.eval, bne_eq_false_iff_eq]
            apply (swS_eq hi s L.lay (by omega) (by omega)).mpr
            rw [hdA, hdB]; exact hsum
          · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega)
          · exact hsel _ hb)
        have hcok : (L.cctx t a).ok :=
          ⟨hlay, by have := tau_lt L.lay L.idx hlay hidx; simp only [LCtx.cctx, LCtx.tau] at this ⊢; omega,
            by have := e_lt L ⟨hlay, hidx, hwl⟩; simp only [LCtx.cctx] at this ⊢; omega, hwl, hlt.1, hlt.2⟩
        have hmem : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
        have hK' := hu.known
        have hK0 : KnownOK chK0 u := fun p hp => hK' p (List.mem_append_left _ hp)
        refine ⟨u, hu.steps, ⟨⟨hu.glob _ _ _ hG, hK0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
          fun j hj => by simp at hj, rfl, by simp, ?_⟩, ?_, ?_, ?_⟩, hcok, ?_, hsum, by simp [digitsOfWord]⟩
        · rw [hu.regs (.x16, d0E hi) (by simp [specBok])]; exact hD0
        · rw [hu.regs (.x17, d1E hi) (by simp [specBok])]; exact hD1
        · rw [hu.keep .x23 (by simp)]; exact h23
        · rw [hu.keep .x30 (by simp)]; exact h30
        · rw [hu.keep .x31 (by simp)]; exact h31
        · exact hK' (.x22, BitVec.ofNat 64 (s6N L.lay)) (by simp [chKa])
        · exact hK' (.x27, BitVec.ofNat 64 (hWord L.lay + 768)) (by simp [chKa])
        · exact hK' (.x1, pcOf (retPc L.lay t)) (by simp [chKa])
        · unfold CB0; rw [hmem]; exact hCB
        · trivial
        · exact Fresh_frame hF (fun A _ _ => hmem _)
        · rw [hu.spc _ rfl, tgt0_eval hi (L.cctx t a) s hD0]
          simp [startPc]
        · intro i hi
          rw [digits_getD _ _ i hi]; unfold dig; simp only [LCtx.cctx]; split <;> rfl
      · rw [if_neg hsum] at hxs; cases hxs
    · rw [if_neg hlt] at hxs; cases hxs

end SigGolfCandidate.Verify
