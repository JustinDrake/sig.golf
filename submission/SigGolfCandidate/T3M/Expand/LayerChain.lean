import SigGolfCandidate.T3M.Expand.LayerBlocks
import SigGolfCandidate.T3M.Expand.Basic
import SigGolfCandidate.T3M.Expand.PackedHeader
import SigGolfCandidate.T3M.Keygen.PackedShared
import SigGolfCandidate.T3M.Keygen.PackedInput

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
theorem chainInput_length' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, T3.zero16]
theorem wordsOf_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (pad64 (chainInput lay tree leaf i step v)) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_length'])]
  exact Keygen.Packed.wordsOf_chainInput lay tree leaf i step v
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x9 : t.getReg .x9 = BitVec.ofNat 64 tree
  x18 : t.getReg .x18 = BitVec.ofNat 64 leaf
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  z32 : t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
def StepW (A : Nat) : Prop := (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x18 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x9 := by rw [hr.get hl.2.2.1]; exact h.x9
  x18 := by rw [hr.get hl.2.2.2.1]; exact h.x18
  x19 := by rw [hr.get hl.2.2.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
  z32 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z32
  z40 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z40
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
theorem chain_step (lay : Layer) (tree leaf i st e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hst : st < e) (he : e ≤ 7)
    (hi : i < 64) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim image sk t 45 (shortHash (chainInput lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, a10, a11, a12, m16, m24, r2, f2⟩ := rl1032_spec t1 p1 lay tree leaf i st hr hf hi (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact hc.x9) (by rw [r1.get (by simp)]; exact hc.x18)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have fr : ∀ A, A < 2 ^ 64 → ¬ (A = CHAIN + 16 ∨ A = CHAIN + 24) → t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => f12.get hA hn
  have hq : hashInput t2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
    refine hashInput_toQ t2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
      a10 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) a11 (by norm_num) ?_
    rw [readWords_eight, wordsOf_chainInput', fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega), m16, m24,
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      fr _ (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega),
      hc.z0, hc.z8, hc.z32, hc.z40, hv.1,
      show CHAIN + 48 + 8 = CHAIN + 56 from rfl, hv.2]
  have hv2 : hashArgumentsValid t2 = true :=
    hashArgs_const t2 CHAIN 64 (CHAIN + 48) a10 a11 a12 (by simp only [CHAIN]) (by norm_num) (by simp only [CHAIN]; omega)
      (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
  refine (TBSim.steps (s1.trans s2) (tb_shortHash_bind' (W := 2) (fetch_1046 t2 p2)
    (by rw [r2.get (by simp), r1.get (by simp)]; exact hc.x5) hv2 hq (fun a => ?_))).mono
    (by rw [blocks_chainInput']; fin_cases lay <;> norm_num [Keygen.headerK]) (fun _ _ h => h)
  have p3 : (writeHash t2 a).pc = pcOf 1047 := by rw [pc_writeHash, p2, pcOf_add4]
  obtain ⟨u, s4, p4, u20, r4, f4⟩ := rl1047_spec (writeHash t2 a) p3 st
    (by rw [getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h20)
  refine TBSim.steps s4 (TBSim.pure ⟨p4, u20, ?_, ?_, ?_, ?_, ?_⟩)
  · rw [r4.get (by simp), getReg_writeHash, r2.get (by simp), r1.get (by simp)]; exact h21
  · have fw := Frame.writeHash t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    have fall : Frame t u StepW := ((f12.trans fw).trans f4).mono (fun A _ h => by
      unfold StepW; rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
    refine hc.frame (l := stepRegs) (by simp [stepRegs]) ?_ fall
    intro r hr
    rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), getReg_writeHash,
      r2.get (not_mem_of_sub (by simp [stepRegs]) hr), r1.get (by simp)]
  · have hd := DigAt.writeHash_lo t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    exact ⟨by rw [f4.get (by simp only [CHAIN]; omega) (by simp)]; exact hd.1,
      by rw [f4.get (by simp only [CHAIN]; omega) (by simp)]; exact hd.2⟩
  · intro r hr
    rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), getReg_writeHash,
      r2.get (not_mem_of_sub (by simp [stepRegs]) hr), r1.get (by simp)]
  · have fw := Frame.writeHash t2 a (CHAIN + 48) a12 (by simp only [CHAIN]; omega)
    exact ((f12.trans fw).trans f4).mono (fun A _ h => by
      unfold StepW; rcases h with (h | h) | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
theorem chain_loop (lay : Layer) (tree leaf i d e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hd : d ≤ e) (he : e ≤ 7)
    (hi : i < 64) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim image sk t ((e - d) * 45 + 1) (chain lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := image) (sk := sk) d (e - d)
    (fun value step => shortHash (chainInput lay tree leaf i step value)) v Inv 45
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step lay tree leaf i (d + j) e hr hf (by omega) he hi w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : chain lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => shortHash (chainInput lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)
def slotOff (c : Nat) : Nat := if c = 0 then 0 else 16 * c + 16
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8 ∨ A = W + 48 ∨ A = W + 56
def endpoint (lay : Layer) (i n4 : Nat) : Nat :=
  if lay = 0 then (if i < n4 then 4 else 3) else 7
def endpointExtra (lay : Layer) (i n4 : Nat) : Nat :=
  if lay = 0 then (if i < n4 then 5 else 3) else 0
theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hi : i < n) (hn : n ≤ 58)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim image sk t 351 (chain lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW i W)) := by
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps image t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec ta pa i n4 (by omega) (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19) (by rw [rr.get (by simp)]; exact h27)
      by_cases hi' : i < n4
      · rw [if_pos hi'] at pb
        obtain ⟨tc, qc, pc, xc, rc, fc⟩ := rl1160_spec tb pb
        refine ⟨tc, ?_, pc, ?_, ?_, ?_⟩
        · simpa only [endpointExtra, if_pos hl, if_pos hi'] using (qa.trans qb).trans qc
        · simpa only [he, endpoint, if_pos hl, if_pos hi'] using xc
        · exact ((ra.trans rb).trans rc).mono (by simp)
        · exact ((fa.trans fb).trans fc).mono (by simp)
      · rw [if_neg hi'] at pb
        refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
        · simpa only [endpointExtra, if_pos hl, if_neg hi'] using qa.trans qb
        · simpa only [he, endpoint, if_pos hl, if_neg hi'] using xb
        · exact (ra.trans rb).mono (by simp)
        · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x9 := by rw [g5 _ (by simp)]; exact hc.x9
      x18 := by rw [g5 _ (by simp)]; exact hc.x18
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8
      z32 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z32
      z40 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z40 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (sk := sk) lay tree leaf i d e hr hf hd he7 (by omega) v t5 p5 hc5 x20' x21' hv5
  have hprog : chain lay tree leaf i d (e - d) v = (chain lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * 45 + 1 + 14) ≤ 351 := by
    rw [he]; unfold endpointExtra endpoint
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 14) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u1, q1, pu1, y28, ry1, fy1⟩ := rl1049_spec u pu i (by omega) cu.x19
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ : ∃ u2, Steps image u1 (if i = 0 then 0 else 1) (if i = 0 then 0 else 1) u2 ∧
      u2.pc = pcOf 1052 ∧ u2.getReg .x28 = BitVec.ofNat 64 (slotOff i) ∧ RegsExcept u1 u2 [.x28] ∧
      Frame u1 u2 (fun _ => False) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at pu1
      exact ⟨u1, by simpa [h0] using Steps.refl u1, pu1, by rw [y28, slotOff, if_pos h0, h0], RegsExcept.refl _ _,
        Frame.refl _ _⟩
    · rw [if_neg h0] at pu1
      obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1051_spec u1 pu1 (16 * i) y28
      exact ⟨u2, by simpa [h0] using q2, pu2, by rw [z28, slotOff, if_neg h0], ry2, fy2⟩
  have hslot8 : slotOff i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec u2 pu2 i (slotOff i) hslot8 hslot z28
    (by rw [ry2.get (by simp), ry1.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := (fy1.trans fy2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have hslotC : ∀ A, (A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q1.trans (q2.trans q3)) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x8
        x9 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x9
        x18 := by rw [ry3.get (by simp), ry2.get (by simp), ry1.get (by simp)]; exact cu.x18
        x19 := w19
        z0 := ?_, z8 := ?_, z32 := ?_, z40 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8 | exact cu.z32 | exact cu.z40
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff i ∨ A = LEAFPK + slotOff i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry1.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]
def ChW (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff c ∨ A = LEAFPK + slotOff c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
theorem not_ChW_of {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 80 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
theorem not_ChW_hdr {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24 ∨
    A = LEAFPK + 880 ∨ A = LEAFPK + 888) (hk : k ≤ 54) : ¬ ChW WC k A := by
  unfold ChW StepW
  rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
    first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW WC ends.length)
end chain
end SigGolfCandidate.T3M.Expand
