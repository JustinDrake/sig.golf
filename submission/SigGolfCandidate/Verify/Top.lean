import SigGolfCandidate.Verify.PorsGood
import SigGolfCandidate.Verify.PorsStart
import SigGolfCandidate.Verify.LayerGood

/-! # The whole verify program -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option Elab.async false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-! ## The root tail (into the layers) -/

theorem tailFCheck_at (c : Nat) (hc : c < 3) : tailFCheck c = true :=
  List.all_eq_true.mp tailFCheck_all c (List.mem_range.mpr hc)

theorem f4Pc_pre (c : Nat) (hc : c < 3) : ∃ t, t < nCopy 4 ∧ f4Pc c = preStart 4 t := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨0, by decide, rfl⟩

/-- The root tail: the fold limit `FR ≤ FLIM` (with an empty stack exactly `folds ≤ 117`), `E = 1`,
empty stack (else HALT(1)); the layer constants; the precode of layer 4 with the PORS root as its
message. -/
theorem tailF_step (P : PCtx) (_hP : P.ok) (s0 : MachineState) (x c ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (h : TailIn P s0 14 x 2 c ptr E folds node stk m) :
    ((folds > porsM ∨ E ≠ 1 ∨ stk ≠ []) → ∃ u k, k ≤ 9 ∧ Steps image m k k u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (¬ (folds > porsM ∨ E ≠ 1 ∨ stk ≠ []) → ∃ u, Steps image m 12 12 u ∧
        LayerIn ⟨P.wl, P.pk, 4, P.idx⟩ node u) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb, heq⟩ := h.bnd
  have hE := h.hE
  have hc := h.hc
  have cF := tailFCheck_at c hc
  simp only [tailFCheck, Bool.and_eq_true] at cF
  obtain ⟨⟨⟨cAcc, cR1⟩, cR2⟩, cR3⟩ := cF
  have hK : KnownOK tailFKnown m := by
    intro q hq
    simp only [tailFKnown, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · exact h.pb.reg hq
    · subst hq
      have := h.a2; simp only [destOf, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
        if_false] at this
      exact this
  have b1 : ∀ d, Br.holds m (fBr1 d) ↔ d = decide (14336 < ptr + 960) := by
    intro d
    simp only [fBr1, Br.holds, CmpOp.eval, Rv.E.eval, cw, h.fr, BitVec.ult,
      ofNat_toNat_lt _ (show 14336 < 2 ^ 64 by decide), ofNat_toNat_lt _ (show ptr + 960 < 2 ^ 64 by omega)]
    exact eq_comm
  have heq : (Rev.revWord E != BitVec.ofNat 64 sgn31) = decide (E ≠ 1) := by
    by_cases h1 : E = 1
    · have e : Rev.revWord E = BitVec.ofNat 64 sgn31 := (Rev.revWord_eq_one E (by omega)).mpr h1
      rw [e, bne_self_eq_false]; simp [h1]
    · have e : Rev.revWord E ≠ BitVec.ofNat 64 sgn31 := fun e => h1 ((Rev.revWord_eq_one E (by omega)).mp e)
      rw [bne_iff_ne.mpr e]; simp [h1]
  have b2 : ∀ d, Br.holds m (fBr2 d) ↔ d = decide (E ≠ 1) := by
    intro d
    show CmpOp.eval .ne (m.getReg .x23) (BitVec.ofNat 64 sgn31) = d ↔ _
    rw [h.rE]
    show (Rev.revWord E != BitVec.ofNat 64 sgn31) = d ↔ _
    rw [heq]; exact eq_comm
  have b3 : ∀ d, Br.holds m (fBr3 d) ↔ d = decide (stk ≠ []) := by
    intro d
    simp only [fBr3, Br.holds, CmpOp.eval, Rv.E.eval, cw, h.rS]
    have : (BitVec.ofNat 64 (stkReg stk.length) != BitVec.ofNat 64 0) = decide (stk ≠ []) := by
      cases stk with
      | nil => simp [stkReg]
      | cons e r =>
        have hne : BitVec.ofNat 64 (stkReg (e :: r).length) ≠ BitVec.ofNat 64 0 :=
          ofNat_ne (by simp only [stkReg, EMPTY, List.length_cons] at hd ⊢; omega) (by decide) (by simp [stkReg, EMPTY])
        rw [show (BitVec.ofNat 64 (stkReg (e :: r).length) != BitVec.ofNat 64 0) = true from bne_iff_ne.mpr hne]
        simp
    rw [this]; exact eq_comm
  have hpM : porsM = 117 := rfl
  have hfl : (14336 : Nat) = 14336 := rfl
  constructor
  · intro hrej
    by_cases h1 : 14336 < ptr + 960
    · obtain ⟨u, hu⟩ := pspec_run cR1 m h.pc hK (by
        intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
        exact (b1 true).mpr (by simp [h1])) (by simp)
      exact ⟨u, 4, by omega, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
        hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
    · by_cases h2 : E ≠ 1
      · obtain ⟨u, hu⟩ := pspec_run cR2 m h.pc hK (by
          intro b hb; simp only [rejSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact (b2 true).mpr (by simp [h2])
          · exact (b1 false).mpr (by simp [h1])) (by simp)
        exact ⟨u, 5, by omega, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
          hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
      · have h3 : stk ≠ [] := by
          rcases hrej with h' | h' | h'
          · intro hnil
            have hl0 : stk.length = 0 := by rw [hnil]; rfl
            rw [hpM] at h'; omega
          · exact absurd h' h2
          · exact h'
        obtain ⟨u, hu⟩ := pspec_run cR3 m h.pc hK (by
          intro b hb; simp only [rejSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact (b3 true).mpr (by simp [h3])
          · exact (b2 false).mpr (by simp [h2])
          · exact (b1 false).mpr (by simp [h1])) (by simp)
        exact ⟨u, 6, by omega, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
          hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hacc
    have h2 : ¬ E ≠ 1 := fun e => hacc (Or.inr (Or.inl e))
    have h3 : ¬ stk ≠ [] := fun e => hacc (Or.inr (Or.inr e))
    have h1 : ¬ 14336 < ptr + 960 := by
      have hf : ¬ folds > porsM := fun e => hacc (Or.inl e)
      have hnil : stk = [] := by by_contra hc; exact h3 hc
      have hl0 : stk.length = 0 := by rw [hnil]; rfl
      rw [hpM] at hf; omega
    obtain ⟨u, hu⟩ := pspec_run cAcc m h.pc hK (by
      intro b hb; simp only [tailFSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (b3 false).mpr (by simp [h3])
      · exact (b2 false).mpr (by simp [h2])
      · exact (b1 false).mpr (by simp [h1])) (by simp)
    have hg0 := hu.glob _ _ h.pb.glob
    -- the masks: loaded from the image's data words, which the PORS phase never writes
    have hm1 : u.getReg .x20 = M1w := by
      rw [hu.regs (.x20, ldE 0xFDFFD0) (by simp [tailFSpec])]
      change m.getMem (BitVec.ofNat 64 0xFDFFD0) = M1w
      rw [h.pb.prot (by simp [protP])]
      exact h.pb.s0ok.masks.2.2.2.2.1
    have hm2 : u.getReg .x21 = M2w := by
      rw [hu.regs (.x21, ldE 0xFDFFD8) (by simp [tailFSpec])]
      change m.getMem (BitVec.ofNat 64 0xFDFFD8) = M2w
      rw [h.pb.prot (by simp [protP])]
      exact h.pb.s0ok.masks.2.2.2.2.2
    have htag : u.getReg .x27 = 0x40401#64 := by
      rw [hu.regs (.x27, ldE 0xFDFFC0) (by simp [tailFSpec])]
      change m.getMem (BitVec.ofNat 64 0xFDFFC0) = 0x40401#64
      rw [h.pb.prot (by simp [protP])]
      exact h.pb.s0ok.masks.2.2.1
    have htmask : u.getReg .x2 = TMASK := by
      rw [hu.regs (.x2, ldE 0xFDFFC8) (by simp [tailFSpec])]
      change m.getMem (BitVec.ofNat 64 0xFDFFC8) = TMASK
      rw [h.pb.prot (by simp [protP])]
      exact h.pb.s0ok.masks.2.2.2.1
    have hregs : KnownOK gkL0 u := by
      intro p hp
      simp only [gkL0, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with hp | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hg0.1 p (by simp [rootK, hp])
      · exact hm1
      · exact hm2
      all_goals first | exact htmask | exact hu.known _ (by simp [rootPost, rootK])
    have hg : GlobP gkL0 s0 u := ⟨hregs, hg0.2⟩
    have hknown : KnownOK l4K u := by
      intro p hp
      simp only [l4K, List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with hp | rfl | rfl | rfl | rfl
      · exact hregs p hp
      all_goals first | exact htag | exact hu.known _ (by simp [rootPost, rootK])
    have hmem : ∀ A, u.getMem A = m.getMem A := fun A => by rw [hu.mem]; rfl
    have n0 := h.node0; have n1 := h.node1
    simp only [destOf, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false] at n0 n1
    obtain ⟨t, ht, hpt⟩ := f4Pc_pre c hc
    -- W1a: the chain array is untouched by the PORS phase (`Fresh` at layer 4, chain 0).
    have hWA := PB.witAll_layers hg h.pb.s0ok
    refine ⟨u, hu.steps, PB.glob_layers hg h.pb.s0ok, hknown, ?_, by rw [hmem]; exact n0,
      by rw [hmem]; exact n1, h.nodeLen, fun h => absurd h (lt_irrefl 4), ?_, (fun h => absurd h (lt_irrefl 4)), Fresh_of_all hWA 4 0,
      fun _ => ⟨?_, ?_⟩, fun h => absurd rfl h, t, ht, by rw [hu.pc rfl, ← hpt]; rfl,
      fun h => absurd rfl h⟩
    · show u.getReg .x22 = BitVec.ofNat 64 (routeIn P.idx 4)
      rw [hu.keep .x22 (by simp), h.pb.idx]; rfl
    · simp [CB0]
    · rw [hmem, h.pb.prot (by decide)]; exact h.pb.s0ok.zero _ (by decide)
    · rw [hmem, h.pb.prot (by decide)]; exact h.pb.s0ok.zero _ (by decide)


/-- Universal accepting-run bound. Scaled PIND byte offsets remove one instruction from
all fifteen leaf headers. The tag-9 address-field rotation is an injective query relabel;
Final.Discharge supplies the additional universal structural credit. Sparse initialization and leaf-header carry are included. -/
def cycleBound : Nat := 10263

/-- A cycle bound of every run (`256` per segment instead of the precise segment costs). -/
def cycleBoundAll : Nat := 16834


/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 45000

def Kb : Bool → OracleComp HashSpec Obs := fun b => pure (b, 0)

theorem layersCost_val : layersCost 5 = 7469 := by decide
theorem layC_val : layC = 7469 := by unfold layC; rfl

theorem tail_eq (pk : List Byte) (w : List Byte) (idx : Nat) (M : Val) :
    cc (do
      let o ← verifyLayers w idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == pk)) Kb = cc (verifyLayers w idx 5 M) (Kfin pk) := by
  rw [cc_bind]
  congr 1; funext o
  cases o <;> simp [Kfin, Kb]

/-- After the PORS root: the layers and the comparison. -/
def Klay (P : PCtx) : Option Val → OracleComp HashSpec Obs := fun r =>
  cc (match r with
    | none => pure false
    | some M => do
      let o ← verifyLayers P.wl P.idx nLayers (Ref.P ++ M)
      match o with
      | none => pure false
      | some root => pure (root == P.pk)) Kb

/-- After the leaves: the root checks, then `Klay`. -/
def Kr (P : PCtx) : Option PorsState → OracleComp HashSpec Obs := fun r =>
  cc (match r with
    | none => pure none
    | some st => if st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ [] then pure none else pure (some st.node))
    (Klay P)

theorem Kr_none (P : PCtx) : Kr P none = pure (false, 0) := by
  simp [Kr, Klay, Kb]

theorem root_good (P : PCtx) (hP : P.ok) (s0 : MachineState) (x c : Nat) (st : PorsState)
    (u : MachineState) (hT : TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u) :
    GoodQ u (12 + layC + layN) (12 + layC) (st.folds ≤ 117) (12 + layC) (Kr P (some st)) := by
  obtain ⟨hrej, hacc⟩ := tailF_step P hP s0 x c st.ptr st.E st.folds st.node st.stack u hT
  have hL : layC = layersCost 5 := layC_val.trans layersCost_val.symm
  by_cases hc : st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ []
  · simp only [Kr, if_pos hc, cc_pure, Klay, Kb]
    obtain ⟨v, k, hk, hst, hf, h5, h10⟩ := hrej hc
    exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 117) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · simp only [Kr, if_neg hc, cc_pure, Klay]
    obtain ⟨v, hst, hL4⟩ := hacc hc
    rw [tail_eq]
    have hg : Good v (5000 * 5 + 9) (layersCost 5)
        (cc (verifyLayers P.wl P.idx 5 (Ref.P ++ st.node)) (Kfin P.pk)) :=
      layers_good P.wl P.pk hP.2 P.idx P.idx_lt hP.1 5 (le_refl _) st.node v hL4
    have hfolds : st.folds ≤ 117 := by simp only [porsM] at hc; omega
    exact GoodQ.steps' hst hg.toQ (by unfold layN; omega) (by rw [hL]; omega) (fun _ => ⟨hfolds, by rw [hL]; omega⟩)

/-- The PORS part: from the leaf-0 state after the setup to the verdict. -/
theorem pors_good (P : PCtx) (hP : P.ok) (s0 : MachineState)
    (h : LeafIn P s0 0 ⟨wStream, 0, 0, 0, [], []⟩ s0) :
    GoodQ s0 (leafCost 0 + Nseg 0 0) (leafCost 0 + Cseg 0 0) True (leafCost 0 + Aseg 0 0 0)
      (cc (porsRoot P.idx P.v P.wl) (Klay P)) := by
  have hr : ∀ (x c : Nat) (st : PorsState) (u : MachineState),
      TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u →
      GoodQ u (12 + layC + layN) (12 + layC) (st.folds ≤ 117) (12 + layC) (Kr P (some st)) :=
    fun x c st u hT => root_good P hP s0 x c st u hT
  have hg0 := leaves_good P hP s0 (Kr P) (Kr_none P) hr
  have hg := hg0 15 0 ⟨wStream, 0, 0, 0, [], []⟩ s0 (by rfl) h
  have e : cc (porsRoot P.idx P.v P.wl) (Klay P) =
      cc (porsLeaves P.idx P.v P.wl (List.range' 0 15) ⟨wStream, 0, 0, 0, [], []⟩) (Kr P) := by
    unfold porsRoot
    rw [cc_bind, List.range_eq_range']
    rfl
  rw [e]
  have l0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).stack.length = 0 := rfl
  have f0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).folds = 0 := rfl
  rw [l0, f0] at hg
  exact hg.mono (le_refl _) (le_refl _) (fun _ => ⟨trivial, le_refl _⟩)

theorem blocks_qT (n : Nat) (ws : List Word) : (queryOfWords n ws).blocks = n + 1 := rfl

theorem lrest_0 : lrest 0 = 171 := by decide

theorem cost_vals : leafCost 0 + Cseg 0 0 = 7758 + layC ∧ leafCost 0 + Aseg 0 0 0 = 2670 + layC ∧
    leafCost 0 + Nseg 0 0 = 7758 + layC + layN := by
  have h0 : leafCost 0 = 11 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Cseg, Aseg, Nseg, segR, lrest_0, h0] <;> omega

theorem main_good (ml pkl wl : List Byte) (hml : ml.length = 32) (hpk : pkl.length = 16)
    (hwl : wl.length = 16384) (s : MachineState) (hs : InitOK ml pkl wl s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (cc (verifyList ml pkl wl) Kb) := by
  unfold verifyList
  obtain ⟨hrej, hacc⟩ := start_step ml pkl wl hml hwl s hs
  have hL := layC_val
  obtain ⟨c1, c2, c3⟩ := cost_vals
  cases hc : countersOk wl
  · simp only [Bool.not_false, if_true, cc_pure, Kb]
    obtain ⟨t, hst, hf, h5, h10⟩ := hrej hc
    exact GoodQ.steps' hst (GoodQ.reject (Q := True) (A := 0) hf h5 h10)
      (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega) (fun q => ⟨q, by unfold cycleBound; omega⟩)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := hacc hc
    unfold digest
    rw [cc_bind, cc_bind]
    simp only [cc_pure]
    have H : ∀ a, GoodQ (writeHash t a) (92 + (leafCost 0 + Nseg 0 0)) (92 + (leafCost 0 + Cseg 0 0)) True
        (92 + (leafCost 0 + Aseg 0 0 0))
        (cc (do
          let r ← porsRoot (idxOf a.toNat) (leavesOf a.toNat) wl
          match r with
          | none => pure false
          | some M => do
            let o ← verifyLayers wl (idxOf a.toNat) nLayers (Ref.P ++ M)
            match o with
            | none => pure false
            | some root => pure (root == pkl)) Kb) := by
      intro a
      rw [cc_bind]
      set P : PCtx := ⟨wl, pkl, a⟩
      obtain ⟨u, hsu, hS0, hLI⟩ := setup_step P ⟨hwl, hpk⟩ _ (hpost a)
      have := pors_good P ⟨hwl, hpk⟩ u hLI
      exact (GoodQ.steps hsu this).mono (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; rw [wRho_eq]; omega
    have h3 := GoodQ.hashH (x := digestInput (witRho wl) ml) hf h5 hv hin H
    rw [fmt_digestInput_words _ _ hrho hml, blocks_qT] at h3
    have hN : layN = 25009 := rfl
    exact GoodQ.steps' hst h3 (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega)
      (fun q => ⟨q, by unfold cycleBound; omega⟩)

end SigGolfCandidate.Verify
