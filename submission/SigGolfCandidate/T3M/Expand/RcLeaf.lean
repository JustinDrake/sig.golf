import SigGolfCandidate.T3M.Expand.Rc

/-!
# `recover_child`: the leaf case (stream E)

`rc_leaf` : at a selected leaf (level 0) the machine closes the open segment unless it is the coordinate's first leaf,
opens one with the leaf's parity, and refines Core's `ftsLeaf index c node secret` (one 1-block HASH into `NOUT`).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest hasLeaf recoverChild ftsLeaf shortHash pad64 header zero16)
open SigGolfCandidate.T3M.Search (NODE NOUT SEL FailedAt kernAt_expand cs0_spec)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

theorem ftsLeafInput_length (c index node : Nat) (sec : Digest) :
    (zero16 ++ bytesLE 16 (header 9 c index 0 node) ++ bytesLE 16 sec ++ zero16).length = 64 := by
  simp [bytesLE_length, zero16]

theorem wordsOf_ftsLeafInput (c index node : Nat) (sec : Digest) :
    wordsOf (pad64 (zero16 ++ bytesLE 16 (header 9 c index 0 node) ++ bytesLE 16 sec ++ zero16)) =
      [0, 0, BitVec.ofNat 64 (hdr0 9 c index index), BitVec.ofNat 64 (T3.nodeWord 9 0 node), sec.extractLsb' 0 64,
        sec.extractLsb' 64 64, 0, 0] := by
  rw [pad64_of_aligned _ (by rw [ftsLeafInput_length])]
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [zero16]), wordsOf_zero16, wordsOf_packed_header 9 _ _ _ _ (by decide), wordsOf_bytesLE16]
  rfl

theorem replaceByte_zero (b : Nat) (hb : b < 256) :
    replaceByte (0 : BitVec 64) 0 ((BitVec.ofNat 64 b).truncate 8) = BitVec.ofNat 64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [replaceByte, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, BitVec.truncate_eq_setWidth, BitVec.getLsbD_zero, hi,
    decide_true, Bool.true_and, Bool.false_and, Bool.false_or, Nat.zero_mul]
  by_cases h : i < 8
  · simp [h]; omega
  · have : b.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (by
      calc 256 = 2 ^ 8 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, this]

theorem idxOf_three (g0 g1 g2 node j : Nat) (hj : j < 3) (he : [g0, g1, g2].getD j 0 = node)
    (hlt : ∀ i < j, [g0, g1, g2].getD i 0 ≠ node) : [g0, g1, g2].idxOf node = j := by
  interval_cases j
  · simp at he; subst he; simp
  · have h0 := hlt 0 (by decide); simp at he h0; subst he
    simp [List.idxOf_cons, h0]
  · have h0 := hlt 0 (by decide); have h1 := hlt 1 (by decide); simp at he h0 h1; subst he
    simp [List.idxOf_cons, h0, h1]

theorem rcCost_leaf (L : List Nat) (node : Nat) (h : hasLeaf L 0 node = true) : rcCost L 0 node = 118 := by
  unfold rcCost; simp [h]

theorem rcEm_leaf (L : List Nat) (pf : Nat → Digest) (node used : Nat) (e : Em) (h : hasLeaf L 0 node = true) :
    rcEm L pf 0 node used e = if L.idxOf node = 0 then ⟨e.segs, e.cur, node % 2⟩ else e.close false (node % 2) := by
  unfold rcEm; simp [h]

section leaf
variable {sk : BitVec 256} {c index g0 g1 g2 : Nat} {values : List Digest} {proof : Fin 115 → Digest}

/-- The close-or-not step at a leaf (`rc_has` with level 0 .. `rc_open`). -/
theorem rc_leaf_close {s t2 : MachineState} {node used : Nat} {e : Em} {fresh : Bool} {ret sp j : Nat}
    (hpre : RcPre c index g0 g1 g2 values proof s 0 node used e fresh ret sp)
    (hj : j < 3) (hfj : j = 0 ↔ fresh = true) (hp2 : t2.pc = pcOf 859)
    (x20 : t2.getReg .x20 = BitVec.ofNat 64 j)
    (hreg : ∀ r, r ∉ [Reg.x2, .x14, .x20, .x28, .x29, .x30] → t2.getReg r = s.getReg r)
    (hstr : StreamAt t2 e) (hroom : (img e).length + (if j = 0 then 0 else 1) ≤ 1275) :
    ∃ k t3, Steps image t2 k k t3 ∧ k ≤ 9 ∧ t3.pc = pcOf 868 ∧
      t3.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl (if j = 0 then e else e.close false 0)) ∧
      StreamAt t3 (if j = 0 then e else e.close false 0) ∧
      RegsExcept t2 t3 [.x22, .x28, .x30] ∧ Frame t2 t3 (fun A => 0xC40 ≤ A ∧ A < 0xC40 + 8 * 1275) := by
  obtain ⟨t3, s3, p3, r3, f3⟩ := rc859_spec t2 hp2 j hj x20
  by_cases h0 : j = 0
  · rw [if_pos h0] at p3
    refine ⟨1, t3, s3, by omega, p3, ?_, ?_, r3.mono (by decide), f3.mono (fun _ _ h => h.elim)⟩
    · rw [if_pos h0, r3.get (by decide), hreg _ (by decide)]; exact hpre.x22
    · rw [if_pos h0]; exact hstr.frame f3 (fun _ _ h => h)
  · rw [if_neg h0] at p3
    have hfr : fresh = false := by
      cases hf : fresh
      · rfl
      · exact absurd (hfj.mpr hf) h0
    obtain ⟨x23, x24⟩ := hpre.regs hfr
    have hcnt := hpre.hcnt; have hpar := hpre.hpar
    have hlen := length_img e
    obtain ⟨t4, s4, p4, m4, x22_4, r4, f4⟩ := rc860_spec t3 p3 (0xC40 + 8 * wl e) e.cur.length e.par (by omega)
      (by rw [if_neg h0] at hroom; omega) (by omega) hpar (by rw [if_neg h0] at hroom; omega)
      (by rw [r3.get (by decide), hreg _ (by decide)]; exact hpre.x22)
      (by rw [r3.get (by decide), hreg _ (by decide)]; exact x23)
      (by rw [r3.get (by decide), hreg _ (by decide)]; exact x24)
    have hz : t3.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e)) = 0 := by
      rw [f3.get (by omega) (by simp)]
      rw [hstr (wl e) (by rw [if_neg h0] at hroom; omega)]
      simp only [img, wl]
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
    refine ⟨1 + 8, t4, s3.trans s4, le_refl _, p4, ?_, ?_, (r3.trans r4).mono (by decide), ?_⟩
    · rw [if_neg h0, x22_4, wl_close]; congr 1; ring
    · rw [if_neg h0]
      refine streamAt_close false 0 (hstr.frame f3 (fun _ _ h => h)) ?_ (fun k hk hne => ?_)
      · rw [m4, hz, replaceByte_zero _ (by omega)]; congr 1; simp; ring
      · rw [f4.get (by omega) (by omega)]
    · exact (f3.trans f4).mono (fun A _ h => by rcases h with h | h; exact h.elim; omega)

theorem img_close_par (e : Em) (m : Bool) (p q : Nat) : img (e.close m p) = img (e.close m q) := rfl
theorem wl_close_par (e : Em) (m : Bool) (p q : Nat) : wl (e.close m p) = wl (e.close m q) := rfl

/-- **The leaf case** (`hasLeaf` at level 0). -/
theorem rc_leaf (hc : c < 7) (hi : index < 2 ^ 32) (hg : g0 < g1 ∧ g1 < g2 ∧ g2 < 2 ^ 11) {s : MachineState}
    {node used : Nat} {e : Em} {fresh : Bool} {ret sp : Nat}
    (hpre : RcPre c index g0 g1 g2 values proof s 0 node used e fresh ret sp)
    (h1 : hasLeaf [g0, g1, g2] 0 node = true) :
    TBSim image sk s (rcCost [g0, g1, g2] 0 node) (recoverChild index c [g0, g1, g2] values proof 0 node used)
      (RcPost c index g0 g1 g2 values proof s 0 node used e fresh ret sp) := by
  have hsp := hpre.hsp; have hsp' := hpre.hsp'; have hsp8 := hpre.hsp8
  obtain ⟨k, t2, s2, hk, x2_2, m48, m40, m32, r2, f2, hif⟩ := rc_prefix hc hpre ⟨by omega, by omega, by omega⟩
  rw [if_pos h1] at hif
  obtain ⟨p2, j, hj, x20_2, x29_2, hjn, hjlt⟩ := hif
  simp only [pow_zero, Nat.div_one] at hjn hjlt
  have hidx : [g0, g1, g2].idxOf node = j := idxOf_three g0 g1 g2 node j hj hjn hjlt
  have hfj : j = 0 ↔ fresh = true := by
    rw [hpre.hfresh]
    simp only [pow_zero, Nat.mul_one, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · intro h0; subst h0; simp at hjn; omega
    · intro ⟨a, _, _⟩
      by_contra hne
      have := hjlt 0 (by omega); simp at this
      interval_cases j <;> simp at hjn <;> omega
  rw [rc_eq_leaf index c _ values proof node used h1, rcCost_leaf _ _ h1]
  obtain ⟨t3, s3, p3, r3, f3⟩ := rc858_spec t2 p2 0 (by decide) (by rw [r2.get (by decide)]; exact hpre.x10)
  rw [if_pos rfl] at p3
  have hroomf := hpre.room
  rw [rcEm_leaf _ _ _ _ _ h1, hidx] at hroomf
  have hroom : (img e).length + (if j = 0 then 0 else 1) ≤ 1275 := by
    split_ifs at hroomf ⊢ with h0
    · rw [img_len_par] at hroomf; omega
    · rw [img_len_close] at hroomf; omega
  have hreg3 : ∀ r, r ∉ [Reg.x2, .x14, .x20, .x28, .x29, .x30] → t3.getReg r = s.getReg r :=
    fun r hr => by rw [r3.get (by simp), r2.get hr]
  have hstr3 : StreamAt t3 e := (hpre.stream.frame f2 (fun k hk h => by rcases h with h | h | h <;> omega)).frame f3
    (fun _ _ h => h)
  obtain ⟨k4, t4, s4, hk4, p4, x22_4, str4, r4, f4⟩ := rc_leaf_close hpre hj hfj p3
    (by rw [r3.get (by simp)]; exact x20_2) hreg3 hstr3 hroom
  have hreg4 : ∀ r, r ∉ [Reg.x2, .x14, .x20, .x28, .x29, .x30, .x22] → t4.getReg r = s.getReg r :=
    fun r hr => by rw [r4.get (fun h => hr (by simp at h ⊢; tauto)), hreg3 r (fun h => hr (by simp at h ⊢; tauto))]
  have hnode11 : node < 2048 := by have := hpre.hnode; simp at this; omega
  obtain ⟨t5, s5, p5, x23_5, x24_5, m32, m40, m16, m24, x10_5, x11_5, x12_5, r5, f5⟩ :=
    rc868_spec t4 p4 c j node index hc hj hnode11 hi (by rw [hreg4 _ (by decide)]; exact hpre.ctx.x8)
      (by rw [r4.get (by decide), r3.get (by simp)]; exact x20_2)
      (by rw [r4.get (by decide), r3.get (by simp), x29_2, hjn])
      (by rw [hreg4 _ (by decide)]; exact hpre.ctx.x9)
  -- memory of `t4` = memory of `s` outside the stack frame and the stream
  have F04 : Frame s t4 (fun A => (((A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) ∨ False) ∨
      (0xC40 ≤ A ∧ A < 0xC40 + 8 * 1275))) := (f2.trans f3).trans f4
  have g4 : ∀ A, A < 2 ^ 64 → (A < sp - 48 ∨ sp ≤ A) → (A < 0xC40 ∨ 0xC40 + 8 * 1275 ≤ A) →
      t4.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
    F04.get hA (by rintro (((h | h | h) | h) | h) <;> first | omega | exact h.elim)
  have hsec := hpre.ctx.sec j hj
  have hsec4 : DigAt t4 (0x7010 + 16 * (3 * c + j)) (values.getD j 0) :=
    ⟨(g4 _ (by omega) (by omega) (by omega)).trans hsec.1, (g4 _ (by omega) (by omega) (by omega)).trans hsec.2⟩
  have hfl : ∀ A, (A = FLEAF ∨ A = FLEAF + 8 ∨ A = FLEAF + 48 ∨ A = FLEAF + 56) →
      t5.getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA
    rw [f5.get (by simp only [FLEAF] at hA; omega) (by simp only [FLEAF] at hA ⊢; omega),
      g4 _ (by simp only [FLEAF] at hA; omega) (by simp only [FLEAF] at hA; omega) (by simp only [FLEAF] at hA; omega)]
    rcases hA with rfl | rfl | rfl | rfl
    · exact hpre.ctx.f0
    · exact hpre.ctx.f8
    · exact hpre.ctx.f48
    · exact hpre.ctx.f56
  have hq : hashInput t5 = toQ (pad64 (zero16 ++ bytesLE 16 (header 9 c index 0 node) ++
      bytesLE 16 (values.getD j 0) ++ zero16)) := by
    refine hashInput_toQ t5 _ 0 FLEAF (by rw [pad64_of_aligned _ (by rw [ftsLeafInput_length]), ftsLeafInput_length])
      x10_5 (by decide) (by decide) x11_5 (by decide) ?_
    rw [readWords_eight, wordsOf_ftsLeafInput, hfl _ (Or.inl rfl), hfl _ (Or.inr (Or.inl rfl)), m16, m24, m32, m40,
      hfl _ (Or.inr (Or.inr (Or.inl rfl))), hfl _ (Or.inr (Or.inr (Or.inr rfl))), hsec4.1,
      show 0x7010 + 16 * (3 * c + j) + 8 = 0x7010 + 16 * (3 * c + j) + 8 from rfl, hsec4.2,
      hdr0_eq 9 c index index (by decide) (by omega) hi hi, nodeWord_9_leaf node hnode11]
    all_goals (try simp only [Nat.mul_zero, Nat.add_zero])
  have hv : hashArgumentsValid t5 = true :=
    hashArgs_const t5 FLEAF 64 NOUT x10_5 x11_5 x12_5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have h5 : t5.getReg .x5 = 0 := by rw [r5.get (by decide), hreg4 _ (by decide)]; exact hpre.ctx.x5
  have hblk : (toQ (pad64 (zero16 ++ bytesLE 16 (header 9 c index 0 node) ++ bytesLE 16 (values.getD j 0) ++
      zero16))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [ftsLeafInput_length]), blocks_toQ ⟨by rw [ftsLeafInput_length]; omega,
      by rw [ftsLeafInput_length]⟩, ftsLeafInput_length]
  unfold ftsLeaf
  rw [hidx]
  refine (TBSim.steps (s2.trans (s3.trans (s4.trans s5))) (tb_shortHash_bind' (W := 5) (fetch_899 t5 p5) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  have p6 : (writeHash t5 a).pc = pcOf 900 := by rw [pc_writeHash, p5, pcOf_add4]
  obtain ⟨t7, s7, p7, x10_7, r7, f7⟩ := rc900_spec (writeHash t5 a) p6
  have hra : t7.getMem (BitVec.ofNat 64 (sp - 48)) = pcOf ret := by
    rw [f7.get (by omega) (by simp), (Frame.writeHash t5 a NOUT x12_5 (by decide)).get (by omega)
      (by simp only [NOUT]; omega), f5.get (by omega) (by simp only [FLEAF]; omega),
      f4.get (by omega) (by omega), f3.get (by omega) (by simp)]
    exact m48
  have x2_7 : t7.getReg .x2 = BitVec.ofNat 64 (sp - 48) := by
    rw [r7.get (by decide), getReg_writeHash, r5.get (by decide), r4.get (by decide), r3.get (by simp)]; exact x2_2
  obtain ⟨t8, s8, p8, x2_8, x1_8, r8, f8⟩ := rc994_spec t7 p7 (sp - 48) ret (by omega) (by omega) x2_7 hra
  have fw := Frame.writeHash t5 a NOUT x12_5 (by decide)
  have F48 : Frame t4 t8 (fun A => (((A = FLEAF + 16 ∨ A = FLEAF + 24 ∨ A = FLEAF + 32 ∨ A = FLEAF + 40) ∨
      (NOUT ≤ A ∧ A < NOUT + 32)) ∨ False) ∨ False) := ((f5.trans fw).trans f7).trans f8
  have R48 : RegsExcept t4 t8 ([.x6, .x7, .x10, .x11, .x12, .x14, .x23, .x24, .x28, .x30] ++ [] ++ [.x10] ++
      [.x1, .x2]) := ((r5.trans (fun r _ => getReg_writeHash t5 a r)).trans r7).trans r8
  have hreg8 : ∀ r, r ∉ [Reg.x2, .x14, .x20, .x28, .x29, .x30, .x22, .x6, .x7, .x10, .x11, .x12, .x23, .x24, .x1] →
      t8.getReg r = s.getReg r := by
    intro r hr
    have k1 : r ∉ ([.x6, .x7, .x10, .x11, .x12, .x14, .x23, .x24, .x28, .x30] ++ [] ++ [.x10] ++ [.x1, .x2] :
        List Reg) := by revert hr; cases r <;> decide
    have k2 : r ∉ [Reg.x2, .x14, .x20, .x28, .x29, .x30, .x22] := by revert hr; cases r <;> decide
    rw [R48.get k1, hreg4 r k2]
  refine (TBSim.steps (s7.trans s8) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  have hd := DigAt.writeHash_lo t5 a NOUT x12_5 (by decide)
  have hFall : Frame s t8 (RcW sp 0) := (F04.trans F48).mono (fun A _ h => by
    unfold RcW
    rcases h with (((h | h | h) | h) | h) | ((((h | h | h | h) | h) | h) | h)
    all_goals first
      | exact h.elim
      | (left; omega)
      | (right; right; right; right; right; right; right; right; right; right; right; right; omega)
      | (right; right; right; right; right; right; right; right; left; exact h)
      | (right; right; right; right; right; right; right; right; right; left; exact h)
      | (right; right; right; right; right; right; right; right; right; right; left; exact h)
      | (right; right; right; right; right; right; right; right; right; right; right; left; exact h)
      | (right; right; right; right; right; right; right; left; exact h))
  have hRall : RegsExcept s t8 rcRegs := by
    intro r hr
    by_cases h2 : r = .x2
    · subst h2; rw [x2_8, hpre.x2]; congr 1; omega
    · exact hreg8 r (by revert hr h2; cases r <;> decide)
  simp only [RcPost, rcEm_leaf _ _ _ _ _ h1, hidx, h1, Bool.not_true, Bool.and_false, ↓reduceIte,
    frontier_leaf _ _ h1, List.length_nil, Nat.add_zero]
  refine ⟨p8, x1_8, by rw [x2_8]; congr 1; omega, by rw [r8.get (by decide)]; exact x10_7,
    ⟨by rw [f8.get (by decide) (by simp), f7.get (by decide) (by simp)]; exact hd.1,
      by rw [f8.get (by decide) (by simp), f7.get (by decide) (by simp)]; exact hd.2⟩, trivial,
    hpre.hused, fun h => absurd h (by simp),
    by rw [hreg8 _ (by decide)]; exact hpre.x18, ?_, ?_, fun h => absurd h (by simp), ?_, ?_, ?_, ?_, hRall,
    hFall, hpre.ctx.frame hc hRall (by decide) (by decide) (by decide) hFall (fun A hA h =>
      not_RcW_static hsp hsp' hA h)⟩
  · rw [R48.get (by decide)]
    by_cases h0 : j = 0
    · rw [if_pos h0] at x22_4; simp only [h0, ↓reduceIte]; exact x22_4
    · rw [if_neg h0] at x22_4; simp only [h0, ↓reduceIte]; exact x22_4
  · intro _
    have hcur0 : (if j = 0 then (⟨e.segs, e.cur, node % 2⟩ : Em) else e.close false (node % 2)).cur.length = 0 := by
      by_cases h0 : j = 0
      · simp only [h0, ↓reduceIte]; rw [hpre.hcur (hfj.mp h0)]; rfl
      · simp only [h0, ↓reduceIte]; rfl
    have rw0 : RegsExcept t5 (writeHash t5 a) [] := fun r _ => getReg_writeHash t5 a r
    have R58 : RegsExcept t5 t8 ([] ++ [.x10] ++ [.x1, .x2]) := (rw0.trans r7).trans r8
    refine ⟨by rw [R58.get (by decide), hcur0]; exact x23_5, ?_⟩
    rw [R58.get (by decide), x24_5]
    by_cases h0 : j = 0 <;> simp only [h0, ↓reduceIte] <;> rfl
  · by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte]; rw [hpre.hcur (hfj.mp h0)]; simp
    · simp only [h0, ↓reduceIte]; simp [Em.close]
  · by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte]; exact hpre.hcnt
    · simp only [h0, ↓reduceIte]; simp [Em.close]
  · by_cases h0 : j = 0 <;> simp only [h0, ↓reduceIte] <;> simp [Em.close] <;> omega
  · have hS : StreamAt t8 (if j = 0 then e else e.close false 0) := str4.frame F48 (fun k hk h => by
      rcases h with (((h | h | h | h) | h) | h) | h <;> first | exact h.elim | (simp only [FLEAF, NOUT] at h; omega))
    by_cases h0 : j = 0
    · simp only [h0, ↓reduceIte] at hS ⊢; exact hS
    · simp only [h0, ↓reduceIte] at hS ⊢; exact hS

end leaf

end SigGolfCandidate.T3M.Expand
