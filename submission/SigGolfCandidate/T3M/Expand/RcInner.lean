import SigGolfCandidate.T3M.Expand.RcLeaf

/-!
# `recover_child`: the inner node and the recursion (stream E)

`rc_tbsim` : by induction on the level, `recover_child` refines Core's `recoverChild` (`RcPre` → `RcPost`): the empty
subtree (`rc_empty`), the leaf (`rc_leaf`), the inner node (two recursive calls with the frame on the stack, the node
block, a fold `L` / `R` or a merge, the node HASH).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest hasLeaf recoverChild nodeHash shortHash pad64 header zero16)
open SigGolfCandidate.T3M.Search (NODE NOUT SEL FailedAt kernAt_expand cs0_spec)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

theorem div_pow_succ' (g l : Nat) : g / 2 ^ (l + 1) = g / 2 ^ l / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem hasLeaf_succ_iff (L : List Nat) (l node : Nat) :
    hasLeaf L (l + 1) node = true ↔ (hasLeaf L l (2 * node) = true ∨ hasLeaf L l (2 * node + 1) = true) := by
  simp only [hasLeaf_iff, div_pow_succ']
  constructor
  · rintro ⟨g, hg, h⟩
    rcases Nat.even_or_odd (g / 2 ^ l) with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; exact ⟨g, hg, by omega⟩
    · right; exact ⟨g, hg, by omega⟩
  · rintro (⟨g, hg, h⟩ | ⟨g, hg, h⟩) <;> exact ⟨g, hg, by omega⟩

theorem fresh_left (L : List Nat) (l node : Nat) :
    (∀ g ∈ L, node * 2 ^ (l + 1) ≤ g) ↔ (∀ g ∈ L, 2 * node * 2 ^ l ≤ g) := by
  rw [show node * 2 ^ (l + 1) = 2 * node * 2 ^ l by rw [pow_succ]; ring]

theorem fresh_right (L : List Nat) (l node : Nat) (fresh : Bool)
    (hf : fresh = true ↔ ∀ g ∈ L, node * 2 ^ (l + 1) ≤ g) :
    (fresh && !hasLeaf L l (2 * node)) = true ↔ ∀ g ∈ L, (2 * node + 1) * 2 ^ l ≤ g := by
  rw [Bool.and_eq_true, hf, Bool.not_eq_true', ← Bool.not_eq_true, hasLeaf_iff]
  have hp : 0 < 2 ^ l := Nat.two_pow_pos l
  constructor
  · rintro ⟨h1, h2⟩ g hg
    have := h1 g hg
    by_contra hlt
    exact h2 ⟨g, hg, by
      rw [show node * 2 ^ (l + 1) = 2 * node * 2 ^ l by rw [pow_succ]; ring] at this
      exact Nat.div_eq_of_lt_le (by linarith) (by push_neg at hlt; linarith)⟩
  · intro h
    refine ⟨fun g hg => ?_, fun ⟨g, hg, he⟩ => ?_⟩
    · have := h g hg
      rw [show node * 2 ^ (l + 1) = 2 * node * 2 ^ l by rw [pow_succ]; ring]
      nlinarith
    · have h1 := h g hg
      have h2 : (2 * node + 1) * 2 ^ l / 2 ^ l ≤ g / 2 ^ l := Nat.div_le_div_right h1
      rw [Nat.mul_div_cancel _ hp] at h2
      omega

theorem rcCost_inner (L : List Nat) (l node : Nat) (h : hasLeaf L (l + 1) node = true) :
    rcCost L (l + 1) node = 116 + rcCost L l (2 * node) + rcCost L l (2 * node + 1) := by
  rw [rcCost]; simp [h]

theorem rcEm_inner (L : List Nat) (pf : Nat → Digest) (l node used : Nat) (e : Em)
    (h : hasLeaf L (l + 1) node = true) :
    rcEm L pf (l + 1) node used e =
      (let e1 := rcEm L pf l (2 * node) used e
       let u1 := used + (T3.frontier L l (2 * node)).length
       let e2 := rcEm L pf l (2 * node + 1) u1 e1
       if hasLeaf L l (2 * node) = false then ⟨e2.segs, e2.cur ++ [(true, pf used)], e2.par⟩
       else if hasLeaf L l (2 * node + 1) = false then ⟨e2.segs, e2.cur ++ [(false, pf u1)], e2.par⟩
       else e2.close true (node % 2)) := by
  rw [rcEm]; simp [h]

theorem node_bound (node l : Nat) (hl : l + 1 ≤ 11) (h : node * 2 ^ (l + 1) < 2 ^ 11) :
    (2 * node + 1) * 2 ^ l < 2 ^ 11 := by
  have e1 : (2 : Nat) ^ 11 = 2 ^ (11 - (l + 1)) * 2 ^ (l + 1) := by rw [← pow_add]; congr 1; omega
  rw [e1] at h
  have h2 : node < 2 ^ (11 - (l + 1)) := Nat.lt_of_mul_lt_mul_right h
  have e2 : (2 : Nat) ^ 11 = 2 ^ (11 - (l + 1)) * 2 * 2 ^ l := by rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega
  rw [e2]
  have hp : 0 < 2 ^ l := Nat.two_pow_pos l
  have : 2 * node + 1 < 2 ^ (11 - (l + 1)) * 2 := by omega
  exact Nat.mul_lt_mul_of_pos_right this hp

theorem streamAt_zero {t : MachineState} {e : Em} (hS : StreamAt t e) (k : Nat) (hk : k < 1275)
    (hge : (img e).length ≤ k) : t.getMem (BitVec.ofNat 64 (0xC40 + 8 * k)) = 0 := by
  rw [hS k hk, getD_of_ge_len _ _ _ hge]

/-- A fold block written after the image (values given doubleword by doubleword). -/
theorem streamAt_fold' {s t : MachineState} {e : Em} (f : Fold) (hS : StreamAt s e)
    (hw : ∀ r < 10, (img e).length + r < 1275 →
      t.getMem (BitVec.ofNat 64 (0xC40 + 8 * ((img e).length + r))) = (foldWords f).getD r 0)
    (hrest : ∀ k < 1275, (k < (img e).length ∨ (img e).length + 10 ≤ k) →
      t.getMem (BitVec.ofNat 64 (0xC40 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xC40 + 8 * k))) :
    StreamAt t ⟨e.segs, e.cur ++ [f], e.par⟩ := by
  intro k hk
  rw [img_fold]
  by_cases h1 : k < (img e).length
  · rw [hrest k hk (Or.inl h1), hS k hk, getD_append_of_lt _ _ _ _ h1]
  · by_cases h2 : (img e).length + 10 ≤ k
    · rw [hrest k hk (Or.inr h2), hS k hk, getD_of_ge_len _ _ _ (by omega), getD_of_ge_len _ _ _ (by
        rw [List.length_append, length_foldWords]; omega)]
    · obtain ⟨r, hr, rfl⟩ : ∃ r, r < 10 ∧ k = (img e).length + r := ⟨k - (img e).length, by omega, by omega⟩
      rw [hw r hr hk, getD_append_of_ge _ _ _ _ (by omega), show (img e).length + r - (img e).length = r by omega]

theorem RcW_succ {sp l A : Nat} (h : RcW (sp - 48) l A) : RcW sp (l + 1) A := by
  unfold RcW at h ⊢
  rcases h with h | h
  · left; omega
  · right; exact h

section inner
variable {sk : BitVec 256} {c index g0 g1 g2 : Nat} {values : List Digest} {proof : Fin 118 → Digest}

/-- **The inner node** (`hasLeaf` at level `l + 1`), given the recursion at level `l`. -/
theorem rc_inner (hc : c < 7) (hi : index < 2 ^ 32) (hg : g0 < g1 ∧ g1 < g2 ∧ g2 < 2 ^ 11) {l : Nat}
    (ih : ∀ node used e fresh ret sp (s : MachineState),
      RcPre c index g0 g1 g2 values proof s l node used e fresh ret sp →
      TBSim image sk s (rcCost [g0, g1, g2] l node) (recoverChild index c [g0, g1, g2] values proof l node used)
        (RcPost c index g0 g1 g2 values proof s l node used e fresh ret sp))
    {s : MachineState} {node used : Nat} {e : Em} {fresh : Bool} {ret sp : Nat}
    (hpre : RcPre c index g0 g1 g2 values proof s (l + 1) node used e fresh ret sp)
    (h1 : hasLeaf [g0, g1, g2] (l + 1) node = true) :
    TBSim image sk s (rcCost [g0, g1, g2] (l + 1) node)
      (recoverChild index c [g0, g1, g2] values proof (l + 1) node used)
      (RcPost c index g0 g1 g2 values proof s (l + 1) node used e fresh ret sp) := by
  have hsp := hpre.hsp; have hsp' := hpre.hsp'; have hsp8 := hpre.hsp8; have hlev := hpre.hlev
  have hnode := hpre.hnode
  obtain ⟨k, t2, s2, hk, x2_2, m48, m40, m32, r2, f2, hif⟩ := rc_prefix hc hpre ⟨by omega, by omega, by omega⟩
  rw [if_pos h1] at hif
  obtain ⟨p2, _⟩ := hif
  obtain ⟨t3, s3, p3, r3, f3⟩ := rc858_spec t2 p2 (l + 1) (by omega)
    (by rw [r2.get (by decide)]; exact hpre.x10)
  rw [if_neg (by omega)] at p3
  have h2node : 2 * node < 2 ^ 64 := by
    have : 1 ≤ 2 ^ (l + 1) := Nat.one_le_two_pow
    have : node ≤ node * 2 ^ (l + 1) := Nat.le_mul_of_pos_right _ this
    omega
  obtain ⟨t4, s4, p4, x10_4, x11_4, x1_4, r4, f4⟩ := rc902_spec t3 p3 (l + 1) node (by omega) (by omega) h2node
    (by rw [r3.get (by simp), r2.get (by decide)]; exact hpre.x10)
    (by rw [r3.get (by simp), r2.get (by decide)]; exact hpre.x11)
  have R04 : RegsExcept s t4 ([.x2, .x14, .x20, .x28, .x29, .x30] ++ [] ++ [.x1, .x10, .x11]) :=
    (r2.trans r3).trans r4
  have F04 : Frame s t4 (fun A => ((A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) ∨ False) ∨ False) :=
    (f2.trans f3).trans f4
  -- the left child's precondition
  have hroomL : (img (rcEm [g0, g1, g2] (pfN proof) l (2 * node) used e)).length ≤ 1275 := by
    have h := hpre.room
    rw [rcEm_inner _ _ _ _ _ _ h1] at h
    simp only [] at h
    have m := rcEm_mono [g0, g1, g2] (pfN proof) l (2 * node + 1)
      (used + (T3.frontier [g0, g1, g2] l (2 * node)).length) (rcEm [g0, g1, g2] (pfN proof) l (2 * node) used e)
    split_ifs at h
    · rw [img_len_fold] at h; omega
    · rw [img_len_fold] at h; omega
    · rw [img_len_close] at h; omega
  have hpreL : RcPre c index g0 g1 g2 values proof t4 l (2 * node) used e fresh 905 (sp - 48) := by
    refine ⟨p4, x1_4, by rw [r4.get (by decide), r3.get (by simp)]; exact x2_2, x10_4, x11_4,
      by rw [R04.get (by decide)]; exact hpre.x18, by rw [R04.get (by decide)]; exact hpre.x22, ?_, ?_, hpre.hcur,
      hpre.hcnt, hpre.hpar, ?_, hroomL, by omega, by omega, by omega, by omega, ?_, hpre.hused, ?_⟩
    · intro hf
      obtain ⟨a, b⟩ := hpre.regs hf
      exact ⟨by rw [R04.get (by decide)]; exact a, by rw [R04.get (by decide)]; exact b⟩
    · rw [hpre.hfresh, fresh_left]
    · exact hpre.stream.frame F04 (fun k hk h => by rcases h with ((h | h | h) | h) | h <;> first | omega | exact h.elim)
    · rw [show 2 * node * 2 ^ l = node * 2 ^ (l + 1) by rw [pow_succ]; ring]; exact hnode
    · exact hpre.ctx.frame hc R04 (by decide) (by decide) (by decide) F04 (fun A hA h => by
        rcases h with ((h | h | h) | h) | h <;> first | exact h.elim |
          (simp only [SEL, FLEAF, NODE] at hA; omega))
  rw [rc_eq_inner index c _ values proof l node used h1, rcCost_inner _ _ _ h1]
  refine (TBSim.steps ((s2.trans s3).trans s4) (TBSim.bind (W₂ := 116 - 35 - 1 - 3 + rcCost [g0, g1, g2] l (2 * node + 1))
    (ih (2 * node) used e fresh 905 (sp - 48) t4 hpreL) (fun r t5 h5 => ?_))).mono (by omega) (fun _ _ h => h)
  rcases r with _ | ⟨vl, next⟩
  · exact (TBSim.pure (Q := RcPost c index g0 g1 g2 values proof s (l + 1) node used e fresh ret sp) (a := none)
      h5).mono (by omega) (fun _ _ h => h)
  obtain ⟨p5, x1_5, x2_5, x10_5, nout5, hnext, hnext124, hvl, x18_5, x22_5, regs5, cur5, cntl5, cnt5, par5, str5,
    R45, F45, ctx5⟩ := h5
  have hsp48 : 0x22000 - 512 + 48 * (l + 1) ≤ sp - 48 := by omega
  have nF45 : ∀ A, sp - 48 ≤ A → A < 0x22000 → ¬ RcW (sp - 48) l A := by
    intro A h1 h2 h; unfold RcW at h; simp only [NODE, NOUT, FLEAF] at h; omega
  have m40' : t5.getMem (BitVec.ofNat 64 (sp - 48 + 8)) = BitVec.ofNat 64 (l + 1) := by
    rw [F45.get (by omega) (nF45 _ (by omega) (by omega)), f4.get (by omega) (by simp),
      f3.get (by omega) (by simp), show sp - 48 + 8 = sp - 40 by omega]; exact m40
  have m32' : t5.getMem (BitVec.ofNat 64 (sp - 48 + 16)) = BitVec.ofNat 64 node := by
    rw [F45.get (by omega) (nF45 _ (by omega) (by omega)), f4.get (by omega) (by simp),
      f3.get (by omega) (by simp), show sp - 48 + 16 = sp - 32 by omega]; exact m32
  obtain ⟨t6, s6, p6, x1_6, x10_6, x11_6, m24, mv32, mv40, r6, f6⟩ := rc905_spec t5 p5 (sp - 48) (by omega)
    (by omega) (by omega) x2_5 (l + 1) node (by omega) (by omega) (by omega) m40' m32'
  set e1 := rcEm [g0, g1, g2] (pfN proof) l (2 * node) used e with he1
  set freshR := fresh && !hasLeaf [g0, g1, g2] l (2 * node) with hfreshR
  have hroomR : (img (rcEm [g0, g1, g2] (pfN proof) l (2 * node + 1) next e1)).length ≤ 1275 := by
    have h := hpre.room
    rw [rcEm_inner _ _ _ _ _ _ h1] at h
    simp only [] at h
    rw [← hnext, ← he1] at h
    split_ifs at h
    · rw [img_len_fold] at h; omega
    · rw [img_len_fold] at h; omega
    · rw [img_len_close] at h; omega
  have hpreR : RcPre c index g0 g1 g2 values proof t6 l (2 * node + 1) next e1 freshR 918 (sp - 48) := by
    refine ⟨p6, x1_6, by rw [r6.get (by decide)]; exact x2_5, x10_6, x11_6,
      by rw [r6.get (by decide)]; exact x18_5, by rw [r6.get (by decide)]; exact x22_5, ?_, ?_, cur5,
      cnt5, par5, ?_, hroomR, by omega, by omega, by omega, by omega, ?_, hnext124, ?_⟩
    · intro hf
      obtain ⟨a, b⟩ := regs5 hf
      exact ⟨by rw [r6.get (by decide)]; exact a, by rw [r6.get (by decide)]; exact b⟩
    · exact fresh_right _ _ _ _ hpre.hfresh
    · exact str5.frame f6 (fun k hk h => by rcases h with h | h | h <;> omega)
    · exact node_bound node l (by omega) hnode
    · exact ctx5.frame hc r6 (by decide) (by decide) (by decide) f6 (fun A hA h => by
        rcases h with h | h | h <;> simp only [SEL, FLEAF, NODE] at hA <;> omega)
  refine (TBSim.steps s6 (TBSim.bind (W₂ := 64) (ih (2 * node + 1) next e1 freshR 918 (sp - 48) t6 hpreR)
    (fun r' t7 h7 => ?_))).mono (by omega) (fun _ _ h => h)
  rcases r' with _ | ⟨vr, next'⟩
  · exact (TBSim.pure (Q := RcPost c index g0 g1 g2 values proof s (l + 1) node used e fresh ret sp) (a := none)
      h7).mono (by omega) (fun _ _ h => h)
  obtain ⟨p7, x1_7, x2_7, x10_7, nout7, hnext', hnext'118, hvr, x18_7, x22_7, regs7, cur7, cntl7, cnt7, par7, str7,
    R67, F67, ctx7⟩ := h7
  have nF67 : ∀ A, sp - 48 ≤ A → A < 0x22000 → ¬ RcW (sp - 48) l A := nF45
  have g7 : ∀ A, sp - 48 ≤ A → A < sp → t7.getMem (BitVec.ofNat 64 A) = t6.getMem (BitVec.ofNat 64 A) :=
    fun A h1 h2 => F67.get (by omega) (nF67 A h1 (by omega))
  set ll := hasLeaf [g0, g1, g2] l (2 * node) with hll
  set rl := hasLeaf [g0, g1, g2] l (2 * node + 1) with hrl
  obtain ⟨t8, s8, p8, n0, n8, n48, n56, n16, n24, r8, f8⟩ := rc918_spec t7 p7 (sp - 48) (by omega) (by omega)
    (by omega) x2_7 (l + 1) node c index (by omega) (by omega) (by
      have := hnode; have : 1 ≤ 2 ^ (l + 1) := Nat.one_le_two_pow
      have : node ≤ node * 2 ^ (l + 1) := Nat.le_mul_of_pos_right _ this; omega) hc hi ll
    (by rw [g7 _ (by omega) (by omega), f6.get (by omega) (by omega)]; exact m40')
    (by rw [g7 _ (by omega) (by omega), f6.get (by omega) (by omega)]; exact m32')
    (by rw [g7 _ (by omega) (by omega), m24, x10_5])
    ctx7.x8 ctx7.x9
  set e2 := rcEm [g0, g1, g2] (pfN proof) l (2 * node + 1) next e1 with he2
  set e' : Em := if ll = false then ⟨e2.segs, e2.cur ++ [(true, pfN proof used)], e2.par⟩
    else if rl = false then ⟨e2.segs, e2.cur ++ [(false, pfN proof next)], e2.par⟩
    else e2.close true (node % 2) with he'
  have hlr : ll = true ∨ rl = true := (hasLeaf_succ_iff _ _ _).mp h1
  have hfr7 : (freshR && !rl) = false := by
    rcases hlr with h | h
    · simp [hfreshR, ← hll, h]
    · simp [h]
  obtain ⟨x23_7, x24_7⟩ := regs7 hfr7
  have F78 : Frame t7 t8 (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
      A = NODE + 56) := f8
  have str8 : StreamAt t8 e2 := str7.frame F78 (fun k hk h => by simp only [NODE] at h; omega)
  have hroom2 : (img e').length ≤ 1275 := by
    have h := hpre.room
    rw [rcEm_inner _ _ _ _ _ _ h1] at h
    simp only [] at h
    rw [← hnext, ← he1, ← he2] at h
    exact h
  have hlen2 := length_img e2
  have hvl32 : t8.getMem (BitVec.ofNat 64 (sp - 48 + 32)) = vl.extractLsb' 0 64 := by
    rw [f8.get (by omega) (by simp only [NODE]; omega), g7 _ (by omega) (by omega), mv32]; exact nout5.1
  have hvl40 : t8.getMem (BitVec.ofNat 64 (sp - 48 + 40)) = vl.extractLsb' 64 64 := by
    rw [f8.get (by omega) (by simp only [NODE]; omega), g7 _ (by omega) (by omega), mv40]; exact nout5.2
  have hvr0 : t8.getMem (BitVec.ofNat 64 NOUT) = vr.extractLsb' 0 64 := by
    rw [f8.get (by decide) (by simp only [NODE, NOUT]; omega)]; exact nout7.1
  have hvr8 : t8.getMem (BitVec.ofNat 64 (NOUT + 8)) = vr.extractLsb' 64 64 := by
    rw [f8.get (by decide) (by simp only [NODE, NOUT]; omega)]; exact nout7.2
  have x22_8 : t8.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e2) := by rw [r8.get (by decide)]; exact x22_7
  have x23_8 : t8.getReg .x23 = BitVec.ofNat 64 e2.cur.length := by rw [r8.get (by decide)]; exact x23_7
  have x24_8 : t8.getReg .x24 = BitVec.ofNat 64 e2.par := by rw [r8.get (by decide)]; exact x24_7
  have x2_8 : t8.getReg .x2 = BitVec.ofNat 64 (sp - 48) := by rw [r8.get (by decide)]; exact x2_7
  have x10_8 : t8.getReg .x10 = BitVec.ofNat 64 (if rl then 1 else 0) := by rw [r8.get (by decide)]; exact x10_7
  have hnd8 : t8.getMem (BitVec.ofNat 64 (sp - 48 + 16)) = BitVec.ofNat 64 node := by
    rw [f8.get (by omega) (by simp only [NODE]; omega), g7 _ (by omega) (by omega), f6.get (by omega) (by omega)]
    exact m32'
  have hbr : ∃ k9 t9, Steps image t8 k9 k9 t9 ∧ k9 ≤ 13 ∧ t9.pc = pcOf 987 ∧
      t9.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e') ∧ t9.getReg .x23 = BitVec.ofNat 64 e'.cur.length ∧
      t9.getReg .x24 = BitVec.ofNat 64 e'.par ∧ StreamAt t9 e' ∧
      RegsExcept t8 t9 [.x6, .x7, .x22, .x23, .x24, .x28, .x29, .x30] ∧
      Frame t8 t9 (fun A => 0xC40 ≤ A ∧ A < 0xC40 + 8 * 1275) := by
    by_cases hL : ll = false
    · have he'L : e' = ⟨e2.segs, e2.cur ++ [(true, pfN proof used)], e2.par⟩ := by rw [he', if_pos hL]
      rw [hL] at p8
      simp only [Bool.false_eq_true, ↓reduceIte] at p8
      have hfit : (img e').length ≤ 1275 := hroom2
      rw [he'L, img_len_fold] at hfit
      obtain ⟨t9, s9, p9, w8, w16, x23_9, r9, f9⟩ := rc952_spec t8 p8 (sp - 48) (by omega) (by omega) x2_8
        (0xC40 + 8 * wl e2) e2.cur.length (by omega) (by omega) (by omega) x22_8 x23_8
      have hvl' : vl = pfN proof used := hvl hL
      refine ⟨10, t9, s9, by omega, p9, ?_, ?_, ?_, ?_, r9.mono (by decide), f9.mono (fun A _ h => by omega)⟩
      · rw [r9.get (by decide), x22_8, he'L]; rfl
      · rw [x23_9, he'L]; simp
      · rw [r9.get (by decide), x24_8, he'L]
      · rw [he'L]
        refine streamAt_fold' _ str8 (fun r hr hrk => ?_) (fun k hk hk' => f9.get (by omega) (by omega))
        have hpos : 0xC40 + 8 * ((img e2).length + r) = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * r := by
          rw [hlen2]; ring
        rw [hpos]
        interval_cases r
        · rw [show 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * 0 = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8
            by ring, w8, hvl32, hvl']; simp [foldWords]
        · rw [show 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * 1 = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 16
            by ring, w16, hvl40, hvl']; simp [foldWords]
        all_goals
          rw [f9.get (by omega) (by omega), ← hpos, streamAt_zero str8 _ (by omega) (by omega)]; simp [foldWords]
    · have hLt : ll = true := by simpa using hL
      rw [hLt] at p8
      simp only [↓reduceIte] at p8
      obtain ⟨t9, s9, p9, r9, f9⟩ := rc962_spec t8 p8 rl x10_8
      have x22_9 : t9.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e2) := by rw [r9.get (by decide)]; exact x22_8
      have x23_9 : t9.getReg .x23 = BitVec.ofNat 64 e2.cur.length := by rw [r9.get (by decide)]; exact x23_8
      have x24_9 : t9.getReg .x24 = BitVec.ofNat 64 e2.par := by rw [r9.get (by decide)]; exact x24_8
      have str9 : StreamAt t9 e2 := str8.frame f9 (fun _ _ h => h)
      by_cases hR : rl = false
      · have he'R : e' = ⟨e2.segs, e2.cur ++ [(false, pfN proof next)], e2.par⟩ := by
          rw [he', if_neg (by rw [hLt]; decide), if_pos hR]
        rw [hR] at p9
        simp only [Bool.false_eq_true, ↓reduceIte] at p9
        have hfit : (img e').length ≤ 1275 := hroom2
        rw [he'R, img_len_fold] at hfit
        obtain ⟨t10, s10, p10, w56, w64, x23_10, r10, f10⟩ := rc963_spec t9 p9 (0xC40 + 8 * wl e2) e2.cur.length
          (by omega) (by omega) (by omega) x22_9 x23_9
        have hvr' : vr = pfN proof next := hvr hR
        have hvr0' : t9.getMem (BitVec.ofNat 64 NOUT) = vr.extractLsb' 0 64 := by
          rw [f9.get (by decide) (by simp)]; exact hvr0
        have hvr8' : t9.getMem (BitVec.ofNat 64 (NOUT + 8)) = vr.extractLsb' 64 64 := by
          rw [f9.get (by decide) (by simp)]; exact hvr8
        refine ⟨1 + 12, t10, s9.trans s10, by omega, p10, ?_, ?_, ?_, ?_, (r9.trans r10).mono (by decide),
          (f9.trans f10).mono (fun A _ h => by rcases h with h | h; exact h.elim; omega)⟩
        · rw [r10.get (by decide), x22_9, he'R]; rfl
        · rw [x23_10, he'R]; simp
        · rw [r10.get (by decide), x24_9, he'R]
        · rw [he'R]
          refine streamAt_fold' _ str9 (fun r hr hrk => ?_) (fun k hk hk' => f10.get (by omega) (by omega))
          have hpos : 0xC40 + 8 * ((img e2).length + r) = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * r := by
            rw [hlen2]; ring
          rw [hpos]
          interval_cases r
          all_goals first
            | (rw [show 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * 6 = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 56
                by ring, w56, hvr0', hvr']; simp [foldWords])
            | (rw [show 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 8 + 8 * 7 = 0xC40 + 8 * wl e2 + 80 * e2.cur.length + 64
                by ring, w64, hvr8', hvr']; simp [foldWords])
            | (rw [f10.get (by omega) (by omega), ← hpos, streamAt_zero str9 _ (by omega) (by omega)]; simp [foldWords])
      · have hRt : rl = true := by simpa using hR
        have he'M : e' = e2.close true (node % 2) := by
          rw [he', if_neg (by rw [hLt]; decide), if_neg (by rw [hRt]; decide)]
        rw [hRt] at p9
        simp only [↓reduceIte] at p9
        have hfit : (img e').length ≤ 1275 := hroom2
        rw [he'M, img_len_close] at hfit
        have hcnt2 : e2.cur.length ≤ l := cntl7 hRt
        obtain ⟨t10, s10, p10, wh, x22_10, x23_10, x24_10, r10, f10⟩ := rc975_spec t9 p9 (sp - 48) (by omega)
          (by omega) (by rw [r9.get (by decide)]; exact x2_8) (0xC40 + 8 * wl e2) e2.cur.length e2.par node
          (by omega) (by omega) par7 (by omega) (by omega)
          (by rw [f9.get (by omega) (by simp)]; exact hnd8) x22_9 x23_9 x24_9
        have hz : t9.getMem (BitVec.ofNat 64 (0xC40 + 8 * wl e2)) = 0 := by
          rw [str9 (wl e2) (by omega)]
          simp only [img, wl]
          rw [List.append_assoc, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl
        refine ⟨1 + 12, t10, s9.trans s10, by omega, p10, ?_, ?_, ?_, ?_, (r9.trans r10).mono (by decide),
          (f9.trans f10).mono (fun A _ h => by rcases h with h | h; exact h.elim; omega)⟩
        · rw [x22_10, he'M, wl_close]; congr 1; ring
        · rw [x23_10, he'M]; rfl
        · rw [x24_10, he'M]; rfl
        · rw [he'M]
          refine streamAt_close true _ str9 ?_ (fun k hk hne => f10.get (by omega) (by omega))
          rw [wh, hz, replaceByte_zero _ (by omega)]
          congr 1; simp; ring
  obtain ⟨k9, t9, s9, hk9, p9, x22_9, x23_9, x24_9, str9, r9, f9⟩ := hbr
  obtain ⟨t10, s10, p10, x10_10, x11_10, x12_10, r10, f10⟩ := rc987_spec t9 p9
  have F810 : Frame t8 t10 (fun A => (0xC40 ≤ A ∧ A < 0xC40 + 8 * 1275) ∨ False) := f9.trans f10
  have g10 : ∀ A, A < 2 ^ 64 → (A < 0xC40 ∨ 0xC40 + 8 * 1275 ≤ A) →
      t10.getMem (BitVec.ofNat 64 A) = t8.getMem (BitVec.ofNat 64 A) :=
    fun A hA h => F810.get hA (by rintro (h' | h'); omega; exact h'.elim)
  set heap := 2 ^ (11 - (l + 1)) + node with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (11 - (l + 1)) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : node ≤ node * 2 ^ (l + 1) := Nat.le_mul_of_pos_right _ Nat.one_le_two_pow
    omega
  have hn32 : t10.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [g10 _ (by decide) (by simp only [NODE]; omega), f8.get (by decide) (by simp only [NODE]; omega)]
    exact ctx7.n32
  have hn40 : t10.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [g10 _ (by decide) (by simp only [NODE]; omega), f8.get (by decide) (by simp only [NODE]; omega)]
    exact ctx7.n40
  have hq : hashInput t10 = toQ (pad64 (bytesLE 16 vl ++ bytesLE 16 (header 10 c index 0 heap) ++ zero16 ++
      bytesLE 16 vr)) := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length'])]
    refine hashInput_toQ t10 _ 0 NODE (nodeInput_length' _ _ _ _ _ _) x10_10 (by decide) (by decide) x11_10
      (by decide) ?_
    rw [wordsOf_nodeInput' 10 _ _ _ _ _ (by decide), readWords_eight, g10 _ (by decide) (by simp only [NODE]; omega),
      g10 _ (by decide) (by simp only [NODE]; omega), g10 _ (by decide) (by simp only [NODE]; omega),
      g10 _ (by decide) (by simp only [NODE]; omega), hn32, hn40,
      g10 _ (by decide) (by simp only [NODE]; omega), g10 _ (by decide) (by simp only [NODE]; omega),
      n0, n8, n16, n24, n48, n56, g7 _ (by omega) (by omega), g7 _ (by omega) (by omega), mv32, mv40,
      nout5.1, nout5.2, nout7.1, nout7.2,
      hdr0_eq 10 c index index (by decide) (by omega) hi hi, hdr1_eq heap 0 hheap' (by decide)]
    simp only [Nat.mul_zero, Nat.add_zero]
  have hv : hashArgumentsValid t10 = true :=
    hashArgs_const t10 NODE 64 NOUT x10_10 x11_10 x12_10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have R710 : RegsExcept t7 t10 ([.x6, .x7, .x13, .x28, .x29, .x30] ++ [.x6, .x7, .x22, .x23, .x24, .x28, .x29, .x30] ++
      [.x10, .x11, .x12]) := (r8.trans r9).trans r10
  have h5 : t10.getReg .x5 = 0 := by rw [R710.get (by decide)]; exact ctx7.x5
  have hblk : (toQ (pad64 (bytesLE 16 vl ++ bytesLE 16 (header 10 c index 0 heap) ++ zero16 ++
      bytesLE 16 vr))).blocks = 1 := by
    rw [pad64_of_aligned _ (by rw [nodeInput_length']), blocks_toQ ⟨by rw [nodeInput_length']; omega,
      by rw [nodeInput_length']⟩, nodeInput_length']
  simp only []
  unfold nodeHash
  refine (TBSim.steps (s8.trans (s9.trans s10)) (tb_shortHash_bind' (W := 4) (fetch_992 t10 p10) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  have p11 : (writeHash t10 a).pc = pcOf 993 := by rw [pc_writeHash, p10, pcOf_add4]
  obtain ⟨t12, s12, p12, x10_12, r12, f12⟩ := rc993_spec (writeHash t10 a) p11
  have fw := Frame.writeHash t10 a NOUT x12_10 (by decide)
  have hra : t12.getMem (BitVec.ofNat 64 (sp - 48)) = pcOf ret := by
    rw [f12.get (by omega) (by simp), fw.get (by omega) (by simp only [NOUT]; omega), g10 _ (by omega) (by omega),
      f8.get (by omega) (by simp only [NODE]; omega), g7 _ (by omega) (by omega), f6.get (by omega) (by omega),
      F45.get (by omega) (nF45 _ (by omega) (by omega)), f4.get (by omega) (by simp), f3.get (by omega) (by simp)]
    exact m48
  have x2_12 : t12.getReg .x2 = BitVec.ofNat 64 (sp - 48) := by
    rw [r12.get (by decide), getReg_writeHash, R710.get (by decide)]; exact x2_7
  obtain ⟨t13, s13, p13, x2_13, x1_13, r13, f13⟩ := rc994_spec t12 p12 (sp - 48) ret (by omega) (by omega) x2_12 hra
  refine (TBSim.steps (s12.trans s13) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  -- the post
  have hE : rcEm [g0, g1, g2] (pfN proof) (l + 1) node used e = e' := by
    rw [rcEm_inner _ _ _ _ _ _ h1]; simp only []; rw [← hnext, ← he1, ← he2]
  have hcurE : e'.cur.length ≤ l + 1 := by
    rw [he']
    by_cases hL : ll = false
    · rw [if_pos hL]
      have hR : rl = true := by
        rcases hlr with h | h
        · rw [hL] at h; exact absurd h (by decide)
        · exact h
      simp only [List.length_append, List.length_singleton]
      have := cntl7 hR; omega
    · rw [if_neg hL]
      have hLt : ll = true := by simpa using hL
      by_cases hR : rl = false
      · rw [if_pos hR]
        simp only [List.length_append, List.length_singleton]
        have he21 : e2 = e1 := by rw [he2]; exact rcEm_empty _ _ _ _ _ _ hR
        rw [he21]; have := cntl5 hLt; omega
      · rw [if_neg hR]; simp [Em.close]
  have hparE : e'.par < 2 := by
    rw [he']
    split_ifs
    · exact par7
    · exact par7
    · simp only [Em.close]; omega
  have rw10 : RegsExcept t10 (writeHash t10 a) [] := fun r _ => getReg_writeHash t10 a r
  have R1013 : RegsExcept t10 t13 ([] ++ [.x10] ++ [.x1, .x2]) := (rw10.trans r12).trans r13
  have Rall := (((((R04.trans R45).trans r6).trans R67).trans R710).trans R1013)
  have hRall : RegsExcept s t13 rcRegs := by
    intro r hr
    by_cases h2 : r = .x2
    · subst h2; rw [x2_13, hpre.x2]; congr 1; omega
    · exact Rall.get (by revert hr h2; cases r <;> decide)
  have hFall : Frame s t13 (RcW sp (l + 1)) :=
    ((((((((F04.trans F45).trans f6).trans F67).trans f8).trans F810).trans fw).trans f12).trans f13).mono
      (fun A _ h => by
        rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
        · unfold RcW; left; rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | omega
        · exact RcW_succ h
        · unfold RcW; left; omega
        · exact RcW_succ h
        · unfold RcW; simp only [NODE, NOUT, FLEAF] at h ⊢; omega
        · unfold RcW; rcases h with h | h
          · right; right; right; right; right; right; right; right; right; right; right; right; exact h
          · exact h.elim
        · unfold RcW; right; right; right; right; right; right; right; left; exact h
        · exact h.elim
        · exact h.elim)
  have F913 : Frame t9 t13 (fun A => ((False ∨ (NOUT ≤ A ∧ A < NOUT + 32)) ∨ False) ∨ False) :=
    ((f10.trans fw).trans f12).trans f13
  have hd := DigAt.writeHash_lo t10 a NOUT x12_10 (by decide)
  have hfr : T3.frontier [g0, g1, g2] (l + 1) node = T3.frontier [g0, g1, g2] l (2 * node) ++
      T3.frontier [g0, g1, g2] l (2 * node + 1) := frontier_succ _ _ _ h1
  simp only [RcPost, hE, h1, Bool.not_true, Bool.and_false, ↓reduceIte, hfr, List.length_append]
  refine ⟨p13, x1_13, by rw [x2_13]; congr 1; omega, by rw [r13.get (by decide)]; exact x10_12,
    ⟨by rw [f13.get (by decide) (by simp), f12.get (by decide) (by simp)]; exact hd.1,
      by rw [f13.get (by decide) (by simp), f12.get (by decide) (by simp)]; exact hd.2⟩, by omega,
    hnext'118, fun h => absurd h (by simp),
    by rw [R1013.get (by decide), R710.get (by decide)]; exact x18_7,
    by rw [R1013.get (by decide), r10.get (by decide)]; exact x22_9,
    fun _ => ⟨by rw [R1013.get (by decide), r10.get (by decide)]; exact x23_9,
      by rw [R1013.get (by decide), r10.get (by decide)]; exact x24_9⟩,
    fun h => absurd h (by simp), fun _ => hcurE, by omega, hparE, ?_, hRall, hFall,
    hpre.ctx.frame hc hRall (by decide) (by decide) (by decide) hFall (fun A hA h => not_RcW_static hsp hsp' hA h)⟩
  exact str9.frame F913 (fun k hk h => by
    rcases h with ((h | h) | h) | h <;> first | exact h.elim | (simp only [NOUT] at h; omega))

/-- **`recover_child` refines Core's `recoverChild`** at every level (`RcPre` → `RcPost`, `rcCost` cycles). -/
theorem rc_tbsim (hc : c < 7) (hi : index < 2 ^ 32) (hg : g0 < g1 ∧ g1 < g2 ∧ g2 < 2 ^ 11) (level : Nat) :
    ∀ node used e fresh ret sp (s : MachineState),
      RcPre c index g0 g1 g2 values proof s level node used e fresh ret sp →
      TBSim image sk s (rcCost [g0, g1, g2] level node) (recoverChild index c [g0, g1, g2] values proof level node used)
        (RcPost c index g0 g1 g2 values proof s level node used e fresh ret sp) := by
  have hg' : g0 < 2 ^ 11 ∧ g1 < 2 ^ 11 ∧ g2 < 2 ^ 11 := ⟨by omega, by omega, by omega⟩
  induction level with
  | zero =>
    intro node used e fresh ret sp s hpre
    by_cases h : hasLeaf [g0, g1, g2] 0 node = true
    · exact rc_leaf hc hi hg hpre h
    · exact rc_empty hc hg' hpre (by simpa using h)
  | succ l ih =>
    intro node used e fresh ret sp s hpre
    by_cases h : hasLeaf [g0, g1, g2] (l + 1) node = true
    · exact rc_inner hc hi hg ih hpre h
    · exact rc_empty hc hg' hpre (by simpa using h)

end inner

end SigGolfCandidate.T3M.Expand
