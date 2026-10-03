import SigGolfCandidate.T3M.Search.CounterSearch
import SigGolfCandidate.T3M.Expand.RcModel

/-!
# `recover_child` refines Core's `recoverChild` (stream E)

`rc_tbsim` : from `recover_child` (word 824) with `RcPre` (level, node, the next proof slot, the stream emission
state), the machine refines `recoverChild index c leaves values proof level node used` within
`rcCost leaves level node` cycles, returning with the value at `NOUT`, the live flag in `a0`, the next proof slot in
`s2` and the stream extended to `img (rcEm leaves (pfN proof) level node used e)` (`RcPost`); out of slots it halts
through `fail`.
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest hasLeaf recoverChild ftsLeaf nodeHash shortHash pad64 header zero16)
open SigGolfCandidate.T3M.Search (NODE NOUT SEL FailedAt kernAt_expand cs0_spec)
open SphincsSecurity (bytesLE bytesLE_length)

set_option autoImplicit false

theorem hasLeaf_three (g0 g1 g2 level node : Nat) :
    hasLeaf [g0, g1, g2] level node = true ↔
      (g0 / 2 ^ level = node ∨ g1 / 2 ^ level = node ∨ g2 / 2 ^ level = node) := by
  rw [hasLeaf_iff]; simp

/-- **The has-loop**: the first row entry `j` with `g_j >> level = node`, or none. -/
theorem rc_hasloop (s : MachineState) (hpc : s.pc = pcOf 835) (c level node g0 g1 g2 : Nat) (hc : c < 7)
    (hl : level < 64) (hn : node < 2 ^ 64) (hg0 : g0 < 2 ^ 64) (hg1 : g1 < 2 ^ 64) (hg2 : g2 < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 0) (h14 : s.getReg .x14 = BitVec.ofNat 64 (SEL + 24 * c))
    (h10 : s.getReg .x10 = BitVec.ofNat 64 level) (h11 : s.getReg .x11 = BitVec.ofNat 64 node)
    (r0 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 0)) = BitVec.ofNat 64 g0)
    (r1 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 1)) = BitVec.ofNat 64 g1)
    (r2 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 2)) = BitVec.ofNat 64 g2) :
    ∃ k t, Steps image s k k t ∧ k ≤ 24 ∧ RegsExcept s t [.x20, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) ∧
      (if hasLeaf [g0, g1, g2] level node then
        t.pc = pcOf 858 ∧ ∃ j < 3, t.getReg .x20 = BitVec.ofNat 64 j ∧
          t.getReg .x29 = BitVec.ofNat 64 ([g0, g1, g2].getD j 0) ∧ [g0, g1, g2].getD j 0 / 2 ^ level = node ∧
          ∀ i < j, [g0, g1, g2].getD i 0 / 2 ^ level ≠ node
      else t.pc = pcOf 843) := by
  obtain ⟨t1, s1, p1, x29_1, ra1, fa1⟩ := rc835_spec s hpc c 0 level node g0 hc (by decide) hl hg0 hn h20 h14 h10 h11 r0
  by_cases e0 : g0 / 2 ^ level = node
  · rw [if_pos e0] at p1
    refine ⟨5, t1, s1, by omega, ra1.mono (by decide), fa1, ?_⟩
    rw [if_pos ((hasLeaf_three _ _ _ _ _).mpr (Or.inl e0))]
    exact ⟨p1, 0, by decide, by rw [ra1.get (by decide), h20], x29_1, e0, fun i hi => absurd hi (by omega)⟩
  rw [if_neg e0] at p1
  obtain ⟨t2, s2, p2, x20_2, ra2, fa2⟩ := rc840_spec t1 p1 0 (by decide) (by rw [ra1.get (by decide), h20])
  rw [if_neg (by decide)] at p2
  have g2' : ∀ r, r ∉ [Reg.x20, .x28, .x29, .x30] → t2.getReg r = s.getReg r := fun r hr => by
    rw [ra2.get (fun h => hr (by simp at h ⊢; tauto)), ra1.get (fun h => hr (by simp at h ⊢; tauto))]
  have f02 : Frame s t2 (fun _ => False) := (fa1.trans fa2).mono (fun _ _ h => by rcases h with h | h <;> exact h)
  obtain ⟨t3, s3, p3, x29_3, ra3, fa3⟩ := rc835_spec t2 p2 c 1 level node g1 hc (by decide) hl hg1 hn x20_2
    (by rw [g2' _ (by decide)]; exact h14) (by rw [g2' _ (by decide)]; exact h10) (by rw [g2' _ (by decide)]; exact h11)
    (by rw [f02.get (by simp only [SEL]; omega) (by simp)]; exact r1)
  by_cases e1 : g1 / 2 ^ level = node
  · rw [if_pos e1] at p3
    refine ⟨5 + 3 + 5, t3, (s1.trans s2).trans s3, by omega, ((ra1.trans ra2).trans ra3).mono (by decide),
      (f02.trans fa3).mono (fun _ _ h => by rcases h with h | h <;> exact h), ?_⟩
    rw [if_pos ((hasLeaf_three _ _ _ _ _).mpr (Or.inr (Or.inl e1)))]
    refine ⟨p3, 1, by decide, by rw [ra3.get (by decide), x20_2], x29_3, e1, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this; exact e0
  rw [if_neg e1] at p3
  obtain ⟨t4, s4, p4, x20_4, ra4, fa4⟩ := rc840_spec t3 p3 1 (by decide) (by rw [ra3.get (by decide), x20_2])
  rw [if_neg (by decide)] at p4
  have g4' : ∀ r, r ∉ [Reg.x20, .x28, .x29, .x30] → t4.getReg r = s.getReg r := fun r hr => by
    rw [ra4.get (fun h => hr (by simp at h ⊢; tauto)), ra3.get (fun h => hr (by simp at h ⊢; tauto)), g2' r hr]
  have f04 : Frame s t4 (fun _ => False) :=
    ((f02.trans fa3).trans fa4).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h)
  obtain ⟨t5, s5, p5, x29_5, ra5, fa5⟩ := rc835_spec t4 p4 c 2 level node g2 hc (by decide) hl hg2 hn x20_4
    (by rw [g4' _ (by decide)]; exact h14) (by rw [g4' _ (by decide)]; exact h10) (by rw [g4' _ (by decide)]; exact h11)
    (by rw [f04.get (by simp only [SEL]; omega) (by simp)]; exact r2)
  by_cases e2 : g2 / 2 ^ level = node
  · rw [if_pos e2] at p5
    refine ⟨5 + 3 + 5 + 3 + 5, t5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega,
      ((((ra1.trans ra2).trans ra3).trans ra4).trans ra5).mono (by decide),
      (f04.trans fa5).mono (fun _ _ h => by rcases h with h | h <;> exact h), ?_⟩
    rw [if_pos ((hasLeaf_three _ _ _ _ _).mpr (Or.inr (Or.inr e2)))]
    refine ⟨p5, 2, by decide, by rw [ra5.get (by decide), x20_4], x29_5, e2, fun i hi => ?_⟩
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · exact e0
    · exact e1
  rw [if_neg e2] at p5
  obtain ⟨t6, s6, p6, x20_6, ra6, fa6⟩ := rc840_spec t5 p5 2 (by decide) (by rw [ra5.get (by decide), x20_4])
  rw [if_pos (by decide)] at p6
  refine ⟨5 + 3 + 5 + 3 + 5 + 3, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6, by omega,
    (((((ra1.trans ra2).trans ra3).trans ra4).trans ra5).trans ra6).mono (by decide),
    ((f04.trans fa5).trans fa6).mono (fun _ _ h => by rcases h with (h | h) | h <;> exact h), ?_⟩
  rw [if_neg (fun h => by
    rcases (hasLeaf_three _ _ _ _ _).mp h with h | h | h <;> contradiction)]
  exact p6

/-! ## The recursion -/

/-- The proof slots, indexed by `Nat` (zero past 115). -/
def pfN (proof : Fin 115 → Digest) (k : Nat) : Digest := if h : k < 115 then proof ⟨k, h⟩ else 0

/-- The static facts of one coordinate's DFS (unchanged by `recover_child`). -/
structure RcCtx (c index g0 g1 g2 : Nat) (values : List Digest) (proof : Fin 115 → Digest) (s : MachineState) :
    Prop where
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 c
  x9 : s.getReg .x9 = BitVec.ofNat 64 index
  r0 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 0)) = BitVec.ofNat 64 g0
  r1 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 1)) = BitVec.ofNat 64 g1
  r2 : s.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * 2)) = BitVec.ofNat 64 g2
  sec : ∀ j < 3, DigAt s (0x7010 + 16 * (3 * c + j)) (values.getD j 0)
  slots : ∀ k < 115, DigAt s (0x7160 + 16 * k) (pfN proof k)
  f0 : s.getMem (BitVec.ofNat 64 FLEAF) = 0
  f8 : s.getMem (BitVec.ofNat 64 (FLEAF + 8)) = 0
  f48 : s.getMem (BitVec.ofNat 64 (FLEAF + 48)) = 0
  f56 : s.getMem (BitVec.ofNat 64 (FLEAF + 56)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0

/-- The doublewords `recover_child` at `level` with stack pointer `sp` changes. -/
def RcW (sp level : Nat) (A : Nat) : Prop :=
  (sp - 48 * (level + 1) ≤ A ∧ A < sp) ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨
    A = NODE + 48 ∨ A = NODE + 56 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = FLEAF + 16 ∨ A = FLEAF + 24 ∨
    A = FLEAF + 32 ∨ A = FLEAF + 40 ∨ (0xC40 ≤ A ∧ A < 0xC40 + 8 * 1275)

/-- The registers `recover_child` changes. -/
def rcRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x18, .x20, .x22, .x23, .x24, .x28, .x29, .x30]

/-! ## Core's `recoverChild`, case by case -/

section core
variable (index c : Nat) (L : List Nat) (values : List Digest) (proof : Fin 115 → Digest)

theorem rc_eq_empty (level node used : Nat) (h : hasLeaf L level node = false) :
    recoverChild index c L values proof level node used =
      if h : used < 115 then pure (some (proof ⟨used, h⟩, used + 1)) else pure none := by
  rw [SigGolfCandidate.T3.recoverChild.eq_def]; simp [h]

theorem rc_eq_leaf (node used : Nat) (h : hasLeaf L 0 node = true) :
    recoverChild index c L values proof 0 node used =
      (ftsLeaf index c node (values.getD (L.idxOf node) 0) >>= fun value => pure (some (value, used))) := by
  rw [SigGolfCandidate.T3.recoverChild.eq_def]; simp [h]

theorem rc_eq_inner (l node used : Nat) (h : hasLeaf L (l + 1) node = true) :
    recoverChild index c L values proof (l + 1) node used =
      (recoverChild index c L values proof l (2 * node) used >>= fun r => match r with
        | some (left, next) => recoverChild index c L values proof l (2 * node + 1) next >>= fun r' => match r' with
          | some (right, next') => nodeHash 10 c index (2 ^ (11 - (l + 1)) + node) left right >>= fun value =>
              pure (some (value, next'))
          | none => pure none
        | none => pure none) := by
  rw [SigGolfCandidate.T3.recoverChild.eq_def]
  simp only [h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  congr 1
  funext r
  rcases r with _ | ⟨left, next⟩
  · rfl
  · simp only []
    congr 1
    funext r'
    rcases r' with _ | ⟨right, next'⟩ <;> rfl

end core

/-! ## Entry and exit -/

section rec
variable (c index g0 g1 g2 : Nat) (values : List Digest) (proof : Fin 115 → Digest)

/-- Entry of `recover_child` (word 824) at `(level, node)`, slot `used`, stream emission state `e`; `fresh` = no leaf
of the coordinate seen yet (then `s7` / `s8` are stale and `e.cur = []`). -/
structure RcPre (s : MachineState) (level node used : Nat) (e : Em) (fresh : Bool) (ret sp : Nat) : Prop where
  pc : s.pc = pcOf 824
  x1 : s.getReg .x1 = pcOf ret
  x2 : s.getReg .x2 = BitVec.ofNat 64 sp
  x10 : s.getReg .x10 = BitVec.ofNat 64 level
  x11 : s.getReg .x11 = BitVec.ofNat 64 node
  x18 : s.getReg .x18 = BitVec.ofNat 64 used
  x22 : s.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e)
  regs : fresh = false → s.getReg .x23 = BitVec.ofNat 64 e.cur.length ∧ s.getReg .x24 = BitVec.ofNat 64 e.par
  hfresh : fresh = true ↔ ∀ g ∈ [g0, g1, g2], node * 2 ^ level ≤ g
  hcur : fresh = true → e.cur = []
  hcnt : e.cur.length ≤ 11
  hpar : e.par < 16
  stream : StreamAt s e
  room : (img (rcEm [g0, g1, g2] (pfN proof) level node used e)).length ≤ 1275
  hsp : 0x22000 - 512 + 48 * (level + 1) ≤ sp
  hsp' : sp ≤ 0x22000
  hsp8 : sp % 8 = 0
  hlev : level ≤ 8
  hnode : node * 2 ^ level < 2 ^ 11
  hused : used ≤ 115
  ctx : RcCtx c index g0 g1 g2 values proof s

/-- Exit of `recover_child`: `fail`, or back at `ret` with the value at `NOUT`, the live flag, the next slot and the
extended stream. -/
def RcPost (s : MachineState) (level node used : Nat) (e : Em) (fresh : Bool) (ret sp : Nat) :
    Option (Digest × Nat) → MachineState → Prop
  | none, t => FailedAt 354 t
  | some (v, u'), t =>
      let e' := rcEm [g0, g1, g2] (pfN proof) level node used e
      let fresh' := fresh && !hasLeaf [g0, g1, g2] level node
      t.pc = pcOf ret ∧ t.getReg .x1 = pcOf ret ∧ t.getReg .x2 = BitVec.ofNat 64 sp ∧
        t.getReg .x10 = BitVec.ofNat 64 (if hasLeaf [g0, g1, g2] level node then 1 else 0) ∧ DigAt t NOUT v ∧
        u' = used + (T3.frontier [g0, g1, g2] level node).length ∧ u' ≤ 115 ∧
        (hasLeaf [g0, g1, g2] level node = false → v = pfN proof used) ∧ t.getReg .x18 = BitVec.ofNat 64 u' ∧
        t.getReg .x22 = BitVec.ofNat 64 (0xC40 + 8 * wl e') ∧
        (fresh' = false → t.getReg .x23 = BitVec.ofNat 64 e'.cur.length ∧ t.getReg .x24 = BitVec.ofNat 64 e'.par) ∧
        (fresh' = true → e'.cur = []) ∧
        (hasLeaf [g0, g1, g2] level node = true → e'.cur.length ≤ level) ∧ e'.cur.length ≤ 11 ∧ e'.par < 16 ∧
        StreamAt t e' ∧ RegsExcept s t rcRegs ∧ Frame s t (RcW sp level) ∧ RcCtx c index g0 g1 g2 values proof t

end rec

/-! ## Frames -/

theorem StreamAt.frame {s t : MachineState} {e : Em} {W : Nat → Prop} (h : StreamAt s e) (hf : Frame s t W)
    (hW : ∀ k < 1275, ¬ W (0xC40 + 8 * k)) : StreamAt t e := fun k hk => by
  rw [hf.get (by omega) (hW k hk)]; exact h k hk

theorem RcCtx.frame {c index g0 g1 g2 : Nat} {values : List Digest} {proof : Fin 115 → Digest} {s t : MachineState}
    {W : Nat → Prop} (h : RcCtx c index g0 g1 g2 values proof s) (hc : c < 7) {L : List Reg}
    (hr : RegsExcept s t L) (h5 : Reg.x5 ∉ L) (h8 : Reg.x8 ∉ L) (h9 : Reg.x9 ∉ L) (hf : Frame s t W)
    (hW : ∀ A, ((SEL ≤ A ∧ A < SEL + 168) ∨ (0x7000 ≤ A ∧ A < 0x7000 + 5616) ∨ A = FLEAF ∨ A = FLEAF + 8 ∨
      A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40) → ¬ W A) :
    RcCtx c index g0 g1 g2 values proof t := by
  refine ⟨by rw [hr.get h5]; exact h.x5, by rw [hr.get h8]; exact h.x8, by rw [hr.get h9]; exact h.x9, ?_, ?_, ?_,
    fun j hj => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.get (by simp only [SEL]; omega) (hW _ (Or.inl (by simp only [SEL]; omega)))]; exact h.r0
  · rw [hf.get (by simp only [SEL]; omega) (hW _ (Or.inl (by simp only [SEL]; omega)))]; exact h.r1
  · rw [hf.get (by simp only [SEL]; omega) (hW _ (Or.inl (by simp only [SEL]; omega)))]; exact h.r2
  · exact (h.sec j hj).frame hf (by omega) (hW _ (Or.inr (Or.inl (by omega)))) (hW _ (Or.inr (Or.inl (by omega))))
  · exact (h.slots k hk).frame hf (by omega) (hW _ (Or.inr (Or.inl (by omega)))) (hW _ (Or.inr (Or.inl (by omega))))
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.f0
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.f8
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.f48
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.f56
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.n32
  · rw [hf.get (by decide) (hW _ (by simp))]; exact h.n40

/-- `RcW` misses the static regions. -/
theorem not_RcW_static {sp level A : Nat} (hsp : 0x22000 - 512 + 48 * (level + 1) ≤ sp) (hsp' : sp ≤ 0x22000)
    (hA : (SEL ≤ A ∧ A < SEL + 168) ∨ (0x7000 ≤ A ∧ A < 0x7000 + 5616) ∨ A = FLEAF ∨ A = FLEAF + 8 ∨
      A = FLEAF + 48 ∨ A = FLEAF + 56 ∨ A = NODE + 32 ∨ A = NODE + 40) : ¬ RcW sp level A := by
  unfold RcW
  simp only [SEL, FLEAF, NODE, NOUT] at hA ⊢
  omega

theorem not_RcW_stream {sp level k : Nat} (hsp : 0x22000 - 512 + 48 * (level + 1) ≤ sp) (hsp' : sp ≤ 0x22000)
    (hk : k < 1275) (W : Nat → Prop) (hW : W = fun A => (sp - 48 * (level + 1) ≤ A ∧ A < sp) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) :
    ¬ W (0xC40 + 8 * k) := by
  subst hW; simp only [NOUT]; omega

/-! ## The recursion -/

section main
variable {sk : BitVec 256} {c index g0 g1 g2 : Nat} {values : List Digest} {proof : Fin 115 → Digest}

/-- The common prefix: the frame, the has-loop. -/
theorem rc_prefix (hc : c < 7) {s : MachineState} {level node used : Nat} {e : Em} {fresh : Bool} {ret sp : Nat}
    (hpre : RcPre c index g0 g1 g2 values proof s level node used e fresh ret sp)
    (hg : g0 < 2 ^ 11 ∧ g1 < 2 ^ 11 ∧ g2 < 2 ^ 11) :
    ∃ k t, Steps image s k k t ∧ k ≤ 35 ∧ t.getReg .x2 = BitVec.ofNat 64 (sp - 48) ∧
      t.getMem (BitVec.ofNat 64 (sp - 48)) = pcOf ret ∧ t.getMem (BitVec.ofNat 64 (sp - 40)) = BitVec.ofNat 64 level ∧
      t.getMem (BitVec.ofNat 64 (sp - 32)) = BitVec.ofNat 64 node ∧
      RegsExcept s t [.x2, .x14, .x20, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) ∧
      (if hasLeaf [g0, g1, g2] level node then
        t.pc = pcOf 858 ∧ ∃ j < 3, t.getReg .x20 = BitVec.ofNat 64 j ∧
          t.getReg .x29 = BitVec.ofNat 64 ([g0, g1, g2].getD j 0) ∧ [g0, g1, g2].getD j 0 / 2 ^ level = node ∧
          ∀ i < j, [g0, g1, g2].getD i 0 / 2 ^ level ≠ node
      else t.pc = pcOf 843) := by
  have hsp := hpre.hsp; have hsp' := hpre.hsp'; have hlev := hpre.hlev; have hnode := hpre.hnode
  obtain ⟨t1, s1, p1, x2_1, m48, m40, m32, x14_1, x20_1, r1, f1⟩ := rc824_spec s hpre.pc sp (by omega) (by omega)
    hpre.hsp8 hpre.x2 c hc hpre.ctx.x8
  have g1' : ∀ A, A < 2 ^ 64 → ¬ (A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) →
      t1.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h => f1.get hA h
  have hnode' : node < 2 ^ 64 := by
    have : 1 ≤ 2 ^ level := Nat.one_le_two_pow
    have : node ≤ node * 2 ^ level := Nat.le_mul_of_pos_right _ this
    omega
  obtain ⟨k, t2, s2, hk, r2, f2, hif⟩ := rc_hasloop t1 p1 c level node g0 g1 g2 hc (by omega) hnode'
    (by omega) (by omega) (by omega) x20_1 x14_1 (by rw [r1.get (by decide)]; exact hpre.x10)
    (by rw [r1.get (by decide)]; exact hpre.x11)
    (by rw [g1' _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)]; exact hpre.ctx.r0)
    (by rw [g1' _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)]; exact hpre.ctx.r1)
    (by rw [g1' _ (by simp only [SEL]; omega) (by simp only [SEL]; omega)]; exact hpre.ctx.r2)
  refine ⟨11 + k, t2, s1.trans s2, by omega, by rw [r2.get (by decide)]; exact x2_1, ?_, ?_, ?_,
    (r1.trans r2).mono (by decide), (f1.trans f2).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim), hif⟩
  · rw [f2.get (by omega) (by simp), m48, hpre.x1]
  · rw [f2.get (by omega) (by simp), m40, hpre.x10]
  · rw [f2.get (by omega) (by simp), m32, hpre.x11]

theorem rcCost_empty (L : List Nat) (level node : Nat) (h : hasLeaf L level node = false) :
    rcCost L level node = 53 := by
  unfold rcCost; simp [h]

theorem rcEm_empty (L : List Nat) (pf : Nat → Digest) (level node used : Nat) (e : Em)
    (h : hasLeaf L level node = false) : rcEm L pf level node used e = e := by
  unfold rcEm; simp [h]

theorem pfN_lt (proof : Fin 115 → Digest) (k : Nat) (h : k < 115) : pfN proof k = proof ⟨k, h⟩ := by
  unfold pfN; rw [dif_pos h]

/-- **The empty subtree**: the next proof slot, or `fail` out of slots. -/
theorem rc_empty (hc : c < 7) (hg : g0 < 2 ^ 11 ∧ g1 < 2 ^ 11 ∧ g2 < 2 ^ 11) {s : MachineState}
    {level node used : Nat} {e : Em} {fresh : Bool} {ret sp : Nat}
    (hpre : RcPre c index g0 g1 g2 values proof s level node used e fresh ret sp)
    (h0 : hasLeaf [g0, g1, g2] level node = false) :
    TBSim image sk s (rcCost [g0, g1, g2] level node) (recoverChild index c [g0, g1, g2] values proof level node used)
      (RcPost c index g0 g1 g2 values proof s level node used e fresh ret sp) := by
  have hsp := hpre.hsp; have hsp' := hpre.hsp'; have hsp8 := hpre.hsp8; have hu124 := hpre.hused
  obtain ⟨k, t2, s2, hk, x2_2, m48, m40, m32, r2, f2, hif⟩ := rc_prefix hc hpre hg
  rw [if_neg (by simp [h0])] at hif
  rw [rc_eq_empty index c _ values proof level node used h0, rcCost_empty _ _ _ h0]
  obtain ⟨t3, s3, p3, r3, f3⟩ := rc843_spec t2 hif used (by omega)
    (by rw [r2.get (by decide)]; exact hpre.x18)
  by_cases hu : 115 ≤ used
  · rw [if_pos hu] at p3
    obtain ⟨t4, s4, p4, x5_4, x10_4, _⟩ := cs0_spec kernAt_expand t3 p3
    rw [dif_neg (by omega)]
    exact (TBSim.steps (s2.trans (s3.trans s4)) (TBSim.pure (Q := RcPost c index g0 g1 g2 values proof s level node
      used e fresh ret sp) (a := none) ⟨p4, x5_4, x10_4⟩)).mono (by omega) (fun _ _ h => h)
  rw [if_neg hu] at p3
  rw [dif_pos (by omega)]
  obtain ⟨t4, s4, p4, n0, n8, x18_4, x10_4, r4, f4⟩ := rc845_spec t3 p3 used (by omega)
    (by rw [r3.get (by decide), r2.get (by decide)]; exact hpre.x18)
  have hra : t4.getMem (BitVec.ofNat 64 (sp - 48)) = pcOf ret := by
    rw [f4.get (by omega) (by simp only [NOUT]; omega), f3.get (by omega) (by simp)]; exact m48
  obtain ⟨t5, s5, p5, x2_5, x1_5, r5, f5⟩ := rc994_spec t4 p4 (sp - 48) ret (by omega) (by omega)
    (by rw [r4.get (by decide), r3.get (by decide)]; exact x2_2) hra
  have R25 : RegsExcept s t5 ([.x2, .x14, .x20, .x28, .x29, .x30] ++ [.x28] ++
      [.x6, .x7, .x10, .x18, .x28, .x29, .x30] ++ [.x1, .x2]) := ((r2.trans r3).trans r4).trans r5
  have F25 : Frame s t5 (fun A => (((A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) ∨ False) ∨
      (A = NOUT ∨ A = NOUT + 8)) ∨ False) := ((f2.trans f3).trans f4).trans f5
  have hW : ∀ A, ((((A = sp - 48 ∨ A = sp - 40 ∨ A = sp - 32) ∨ False) ∨ (A = NOUT ∨ A = NOUT + 8)) ∨ False) →
      RcW sp level A := by
    intro A h
    unfold RcW
    rcases h with (((h | h | h) | h) | h | h) | h
    · left; omega
    · left; omega
    · left; omega
    · exact h.elim
    · right; right; right; right; right; right; right; left; simp only [NOUT] at h ⊢; omega
    · right; right; right; right; right; right; right; left; simp only [NOUT] at h ⊢; omega
    · exact h.elim
  have hslot := hpre.ctx.slots used (by omega)
  rw [pfN_lt proof used (by omega)] at hslot
  refine (TBSim.steps (s2.trans (s3.trans (s4.trans s5))) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
  simp only [RcPost, rcEm_empty _ _ _ _ _ _ h0, h0, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
    frontier_empty _ _ _ h0, List.length_singleton]
  refine ⟨p5, x1_5, by rw [x2_5]; congr 1; omega, by rw [r5.get (by decide)]; exact x10_4, ?_, trivial,
    by omega, fun _ => (pfN_lt proof used (by omega)).symm,
    by rw [r5.get (by decide)]; exact x18_4, ?_, ?_, hpre.hcur, fun h => absurd h (by simp), hpre.hcnt, hpre.hpar,
    ?_, ?_, F25.mono (fun A _ h => hW A h), ?_⟩
  · constructor
    · rw [f5.get (by decide) (by simp), n0, f3.get (by omega) (by simp), f2.get (by omega) (by omega)]; exact hslot.1
    · rw [f5.get (by decide) (by simp), n8, f3.get (by omega) (by simp), f2.get (by omega) (by omega)]; exact hslot.2
  · rw [R25.get (by decide)]; exact hpre.x22
  · intro hf
    obtain ⟨a, b⟩ := hpre.regs hf
    exact ⟨by rw [R25.get (by decide)]; exact a, by rw [R25.get (by decide)]; exact b⟩
  · exact hpre.stream.frame F25 (fun k hk h => by
      rcases h with (((h | h | h) | h) | h | h) | h <;> first | omega | exact h.elim | (simp only [NOUT] at h; omega))
  · intro r hr
    by_cases h2 : r = .x2
    · subst h2; rw [x2_5, hpre.x2]; congr 1; omega
    · have key : ∀ r : Reg, r ∉ rcRegs → r ≠ .x2 → r ∉ ([.x2, .x14, .x20, .x28, .x29, .x30] ++ [.x28] ++
          [.x6, .x7, .x10, .x18, .x28, .x29, .x30] ++ [.x1, .x2] : List Reg) := by
        intro r; cases r <;> decide
      exact R25.get (key r hr h2)
  · exact hpre.ctx.frame hc R25 (by decide) (by decide) (by decide) F25 (fun A hA h => by
      have := not_RcW_static hsp hsp' hA; exact this (hW A h))

end main

end SigGolfCandidate.T3M.Expand
