import SigGolfCandidate.Verify.LayArith
import SigGolfCandidate.Verify.LayerCheck
import SigGolfCandidate.Verify.ChainSem
import SigGolfCandidate.Sign.Enc

/-! # Hypertree layers (W1a): route + encoding, the encoding check and the entry of the chain code

A layer starts at one of the copies of its transition (`preStart lay t`): route and encoding hash,
the check of the encoding, then `li s6, base; sub s9, s11, t3`, the extraction of triple 0 and the
`jalr ra` into the layer-shared chain code (`ChainIn c 0 []`, with the return pc of the copy's leaf
block in `ra`). -/

set_option Elab.async false
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
vacuous; the separate leaf-header conjunct carries the previous layer node header. -/
def CBZ (_s : MachineState) : Prop := True

/-- The layer below `L`. -/
def LCtx.sub (L : LCtx) : LCtx := ⟨L.wl, L.pk, L.lay + 1, L.idx⟩

/-- The message of layer `L.lay`, given the 16-byte value `X` in EB+32 at the start of its transition:
`P ++` the PORS root (layer 4); else the two children of the root of the tree of layer `L.lay + 1` in
order, `X` the one on the path and the other one the top sibling of that path in the witness. -/
def LCtx.msg (L : LCtx) (X : Val) : Val :=
  if L.lay = 4 then P ++ X
  else topPair L.sub.e (heightL (L.lay + 1)) X (witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1))

/-- At the start of layer `lay` (`preStart`), with `X` in EB+32 (the PORS root, or the node under the root
of the tree below, in the block of that tree's leaf index): the chain array of the layers `≤ lay` is
still the witness (`Fresh L.wl L.lay 0`), and so is the top sibling of the path of the tree below (in a
tweak slot of this layer's chain region, which its chains have not reached yet). -/
def LayerIn (L : LCtx) (X : Val) (s : MachineState) : Prop :=
  Glob L.gk L.wl L.pk s ∧ KnownOK (preK L.lay L.sub.e) s ∧
  s.getReg (routeReg L.lay) = BitVec.ofNat 64 (routeIn L.idx L.lay) ∧
  s.getMem (BitVec.ofNat 64 (encD L.lay L.sub.e)) = vw0 X ∧ s.getMem (BitVec.ofNat 64 (encD L.lay L.sub.e + 8)) = vw1 X ∧
  X.length = 16 ∧ (L.lay < 4 → CBZ s) ∧ CB0 L.lay s ∧
  (L.lay < 4 → EncHeader (L.lay + 1) s) ∧
  Fresh L.wl L.lay 0 s ∧
  (L.lay = 4 → s.getMem (BitVec.ofNat 64 0x120) = 0 ∧ s.getMem (BitVec.ofNat 64 0x128) = 0) ∧
  (L.lay ≠ 4 →
    s.getMem (BitVec.ofNat 64 (topSib L.lay)) =
      vw0 (witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1)) ∧
    s.getMem (BitVec.ofNat 64 (topSib L.lay + 8)) =
      vw1 (witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1)) ∧
    (witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1)).length = 16) ∧
  ∃ t, t < nCopy L.lay ∧ s.pc = pcOf (preStart L.lay t) ∧ (L.lay ≠ 4 → t = L.sub.e)

/-- After the encoding hash of transition copy `t` (answer `a` in EO). -/
def EncOut (L : LCtx) (t : Nat) (a : BitVec 256) (s : MachineState) : Prop :=
  Glob gkL L.wl L.pk s ∧ KnownOK (bK L.lay t) s ∧
  s.getReg .x23 = BitVec.ofNat 64 (heapU L.lay L.e) ∧ s.getReg .x30 = BitVec.ofNat 64 (if L.lay = 0 then L.e else L.tau) ∧
  s.getReg .x31 = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) ∧
  s.getMem (BitVec.ofNat 64 (encD L.lay t + 0)) = a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 (encD L.lay t + 8)) = a.extractLsb' 64 64 ∧
  s.getMem (BitVec.ofNat 64 (encD L.lay t + 16)) = a.extractLsb' 128 64 ∧
  s.getMem (BitVec.ofNat 64 (encD L.lay t + 24)) = a.extractLsb' 192 64 ∧
  CB0 L.lay s ∧ EncHeader L.lay s ∧ Fresh L.wl L.lay 0 s ∧
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
    specB gkL (runAt (preK lay t) [] (preStart lay t) []) (specA lay t) (bK lay t) [] = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  exact h.1.1

theorem lc_enc (hi : Nat) (hhi : hi < 4) (hne : hi ≠ 1) {t : Nat} (ht : t < nCopy lay) :
    specOB gkL (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi false ++ [.br false, .jmp])) (specBok (encD lay t) hi lay) encObligs
      (chKa lay t) [.x23, .x30, .x31] = true ∧
    (hi ≠ 0 → specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi true)) (specRej1 (encD lay t) hi) encObligs [] [] = true) ∧
    specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs hi ++ padDirs hi false ++ [.br true])) (specRej2 (encD lay t) hi lay) encObligs [] [] = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1.2 hi (List.mem_range.mpr hhi)
  simp only [halfCheck, if_neg hne, Bool.and_eq_true] at hh
  refine ⟨hh.1.1, ?_, hh.2⟩
  intro hn0
  simpa [hn0] using hh.1.2

theorem lc_gate_reject {t : Nat} (ht : t < nCopy lay) :
    specOB [] (runAt (bK lay t) [] (encPc lay t + 1) (selDirs 1)) (specRej1 (encD lay t) 1) encObligs [] [] = true := by
  have h := lc_copy hl ht
  simp only [copyCheck, Bool.and_eq_true] at h
  have hh := List.all_eq_true.mp h.1.2 1 (List.mem_range.mpr (by decide))
  simpa [halfCheck] using hh

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
  · rw [show ctrA L.lay = 0x800 + 2320 by simp [ctrA, h4]]
    exact wit_word hW 2320 (by decide) (by decide)
  · have e : ctrA L.lay = blkN 0 0 + 8 * (L.lay / 2) := by
      rw [blkN_eq]; simp only [ctrA, if_neg h4] <;> omega
    have e2 : ctrA L.lay - 0x800 = blockOff 0 0 + 8 * (L.lay / 2) := by
      rw [blockOff_eq]; simp only [ctrA, if_neg h4] <;> omega
    rw [e2, e]
    exact hF 0 0 _ (FreshW_ctr hlay (by omega))

/-- The symbolic memory of the transition: the four writes of the encoding block. -/
theorem encMem (s : MachineState) (B : Nat) (hB : B < 0x200) (e2 e1 e0 : Rv.E) (tl : SymMem) (A : Nat)
    (hA : A < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 (B + 16)⟩, e2) ::
        (⟨none, BitVec.ofNat 64 (B + 8)⟩, e1) :: (⟨none, BitVec.ofNat 64 B⟩, e0) :: tl) (BitVec.ofNat 64 A) =
      if A = B + 16 then e2.eval s else if A = B + 8 then e1.eval s
      else if A = B then e0.eval s else memEval s tl (BitVec.ofNat 64 A) := by
  by_cases h2 : A = B + 16
  · rw [if_pos h2, h2, memEval_cons_eq _ _ _ _ _ rfl]
  rw [if_neg h2, memEval_cons_ne _ _ _ _ _ (by bvne)]
  by_cases h1 : A = B + 8
  · rw [if_pos h1, h1, memEval_cons_eq _ _ _ _ _ rfl]
  rw [if_neg h1, memEval_cons_ne _ _ _ _ _ (by bvne)]
  by_cases h0 : A = B
  · rw [if_pos h0, h0, memEval_cons_eq _ _ _ _ _ rfl]
  rw [if_neg h0, memEval_cons_ne _ _ _ _ _ (by bvne)]


theorem sibMem (s : MachineState) (S : Nat) (hS : S < 0x200) (e1 e0 : Rv.E) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s [(⟨none, BitVec.ofNat 64 (S + 8)⟩, e1), (⟨none, BitVec.ofNat 64 S⟩, e0)] (BitVec.ofNat 64 A) =
      if A = S + 8 then e1.eval s else if A = S then e0.eval s else s.getMem (BitVec.ofNat 64 A) := by
  by_cases h1 : A = S + 8
  · rw [if_pos h1, h1, memEval_cons_eq _ _ _ _ _ rfl]
  rw [if_neg h1, memEval_cons_ne _ _ _ _ _ (by bvne)]
  by_cases h0 : A = S
  · rw [if_pos h0, h0, memEval_cons_eq _ _ _ _ _ rfl]
  rw [if_neg h0, memEval_cons_ne _ _ _ _ _ (by bvne)]
  exact memEval_frame s _ _ (by simp)

theorem vw_P : vw0 P = 0 ∧ vw1 P = 0 := by decide

theorem enc_step (L : LCtx) (hL : L.ok) (X : Val) (s : MachineState) (hs : LayerIn L X s) :
    ∃ t, t < nCopy L.lay ∧ ∃ u, Steps image s (stepsA L.lay) (stepsA L.lay) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = addrFmt (encInput L.lay L.tau L.e (L.msg X) (witCounter L.wl L.lay)) ∧
      (addrFmt (encInput L.lay L.tau L.e (L.msg X) (witCounter L.wl L.lay))).blocks = 1 ∧
      ∀ a, EncOut L t a (writeHash u a) := by
  have hL' := hL
  obtain ⟨hlay, hidx, hwl⟩ := hL'
  obtain ⟨hG, hK, hR, hM0, hM1, hMl, -, hC0, hEH, hF, hZ, hSib, t, ht, hpc, htE⟩ := hs
  have hK0 : KnownOK (preK L.lay t) s := by
    by_cases h4 : L.lay = 4
    · simpa only [preK, if_pos h4] using hK
    · simpa only [htE h4] using hK
  have hDc : encD L.lay L.sub.e = encD L.lay t := by
    by_cases h4 : L.lay = 4
    · simp [encD, xLeft, h4]
    · rw [htE h4]
  rw [hDc] at hM0 hM1
  obtain ⟨u, hu⟩ := spec_run (lc_pre hlay ht) s hpc hK0 (by simp [specA])
  have hK' := hu.known
  have gk : ∀ p ∈ gkL, p ∈ bK L.lay t := fun p hp => by simp [bK, hp]
  have hBv : encB L.lay t = 0x100 := rfl
  have hDv : encD L.lay t = 0x120 ∨ encD L.lay t = 0x130 := by unfold encD; split <;> simp
  have hSv : sibSlot L.lay t = 0x120 ∨ sibSlot L.lay t = 0x130 := by unfold sibSlot; split <;> simp
  have h10 : u.getReg .x10 = BitVec.ofNat 64 (encB L.lay t) :=
    hK' (.x10, BitVec.ofNat 64 (encB L.lay t))
      (by simp [bK])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [bK])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (encD L.lay t) := hK' (.x12, BitVec.ofNat 64 (encD L.lay t)) (by simp [bK])
  have hx31 : (x31Er L.lay).eval s = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) :=
    x31Er_eval L.idx L.lay hlay hidx s hR
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have hctr := ctrA_word L ⟨hlay, hidx, hwl⟩ s hG.2.1 hF
  -- the memory after the run: the four writes of the block, then (below layer 4) the sibling copy
  obtain ⟨tl, htl⟩ : ∃ tl : SymMem, tl = (if L.lay = 4 then [] else
      [(⟨none, BitVec.ofNat 64 (sibSlot L.lay t + 8)⟩, ldE (topSib L.lay + 8)),
       (⟨none, BitVec.ofNat 64 (sibSlot L.lay t)⟩, ldE (topSib L.lay))]) := ⟨_, rfl⟩
  have hmem : ∀ A, u.getMem A = memEval s ((⟨none, BitVec.ofNat 64 (encB L.lay t + 16)⟩, ctrE L.lay) ::
      (⟨none, BitVec.ofNat 64 (encB L.lay t + 8)⟩, x31Er L.lay) ::
      (⟨none, BitVec.ofNat 64 (encB L.lay t)⟩, encHeaderE L.lay) :: tl) A := by
    rw [htl]; exact hu.mem
  have hE := fun A (hA : A < 2 ^ 64) =>
    (hmem (BitVec.ofNat 64 A)).trans (encMem s (encB L.lay t) (by omega) _ _ _ tl A hA)
  have hheader : (encHeaderE L.lay).eval s = BitVec.ofNat 64 (hWord L.lay + 768) := by
    by_cases hlt : L.lay < 4
    · simp only [encHeaderE, if_pos hlt, E.eval, BinOp.eval, ldE, cw]
      rw [hEH hlt]
      exact encoding_header_byte L.lay hlt
    · simp only [encHeaderE, if_neg hlt, E.eval, cw]
  have ma : u.getMem (BitVec.ofNat 64 (encB L.lay t)) = BitVec.ofNat 64 (hWord L.lay + 768) := by
    rw [hE _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    exact hheader
  have mb : u.getMem (BitVec.ofNat 64 (encB L.lay t + 8)) = (x31Er L.lay).eval s := by
    rw [hE _ (by omega), if_neg (by omega), if_pos rfl]
  have mc : u.getMem (BitVec.ofNat 64 (encB L.lay t + 16)) = (ctrE L.lay).eval s := by
    rw [hE _ (by omega), if_pos rfl]
  have md : u.getMem (BitVec.ofNat 64 (encB L.lay t + 24)) = 0 :=
    (hu.glob _ _ _ hG).2.2.2 0x118 (by simp [pSlots])
  have mo : ∀ A, A < 2 ^ 64 → A ≠ encB L.lay t → A ≠ encB L.lay t + 8 → A ≠ encB L.lay t + 16 →
      u.getMem (BitVec.ofNat 64 A) = memEval s tl (BitVec.ofNat 64 A) :=
    fun A hA h0 h1 h2 => by rw [hE A hA, if_neg h2, if_neg h1, if_neg h0]
  have mtl : ∀ A, A < 2 ^ 64 → (L.lay = 4 ∨ (A ≠ sibSlot L.lay t ∧ A ≠ sibSlot L.lay t + 8)) →
      memEval s tl (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h
    by_cases h4 : L.lay = 4
    · rw [htl, if_pos h4]; exact memEval_frame s _ _ (by simp)
    · rcases h with h | h
      · exact absurd h h4
      · rw [htl, if_neg h4, sibMem s _ (by omega) _ _ A hA, if_neg h.2, if_neg h.1]
  have msb : L.lay ≠ 4 →
      memEval s tl (BitVec.ofNat 64 (sibSlot L.lay t)) = s.getMem (BitVec.ofNat 64 (topSib L.lay)) ∧
      memEval s tl (BitVec.ofNat 64 (sibSlot L.lay t + 8)) =
        s.getMem (BitVec.ofNat 64 (topSib L.lay + 8)) := by
    intro h4
    constructor
    · rw [htl, if_neg h4, sibMem s _ (by omega) _ _ _ (by omega), if_neg (by omega), if_pos rfl]; rfl
    · rw [htl, if_neg h4, sibMem s _ (by omega) _ _ _ (by omega), if_pos rfl]; rfl
  have mfr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ 0x100 ∨ 0x150 ≤ A) →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hA'
    rw [mo A hA (by omega) (by omega) (by omega)]
    exact mtl A hA (Or.inr ⟨by omega, by omega⟩)
  -- the message words of the block
  have hM : ∃ Lv Rv : Val, L.msg X = Lv ++ Rv ∧ Lv.length = 16 ∧ Rv.length = 16 ∧
      u.getMem (BitVec.ofNat 64 (encB L.lay t + 32)) = vw0 Lv ∧
      u.getMem (BitVec.ofNat 64 (encB L.lay t + 40)) = vw1 Lv ∧
      u.getMem (BitVec.ofNat 64 (encB L.lay t + 48)) = vw0 Rv ∧
      u.getMem (BitVec.ofNat 64 (encB L.lay t + 56)) = vw1 Rv := by
    by_cases h4 : L.lay = 4
    · have hB : encB L.lay t = 0x100 := by simp [encB, xLeft, h4]
      obtain ⟨z0, z1⟩ := hZ h4
      have hD : encD L.lay t = 0x130 := by simp [encD, xLeft, h4]
      rw [hD] at hM0 hM1
      refine ⟨P, X, by simp [LCtx.msg, h4], rfl, hMl, ?_, ?_, ?_, ?_⟩
      · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), mtl _ (by omega) (Or.inl h4),
          vw_P.1]; exact z0
      · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), mtl _ (by omega) (Or.inl h4),
          vw_P.2]; exact z1
      · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), mtl _ (by omega) (Or.inl h4)]
        exact hM0
      · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), mtl _ (by omega) (Or.inl h4)]
        exact hM1
    · have ht' := htE h4
      obtain ⟨hs0, hs1, hsl⟩ := hSib h4
      obtain ⟨ms0, ms1⟩ := msb h4
      by_cases hbit : t / 2 ^ (heightL (L.lay + 1) - 1) % 2 = 1
      · have hB : encB L.lay t = 0x100 := by simp [encB, xLeft, h4, hbit]
        have hS : sibSlot L.lay t = 0x120 := by simp [sibSlot, xLeft, h4, hbit]
        rw [hS] at ms0 ms1
        have hD : encD L.lay t = 0x130 := by simp [encD, xLeft, h4, hbit]
        rw [hD] at hM0 hM1
        refine ⟨witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1), X, ?_, hsl, hMl, ?_, ?_, ?_, ?_⟩
        · unfold LCtx.msg topPair
          rw [if_neg h4, ← ht', if_pos hbit]
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), ms0]; exact hs0
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), ms1]; exact hs1
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega),
            mtl _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
          exact hM0
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega),
            mtl _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
          exact hM1
      · have hbit0 : t / 2 ^ (heightL (L.lay + 1) - 1) % 2 = 0 := by omega
        have hB : encB L.lay t = 0x100 := rfl
        have hS : sibSlot L.lay t = 0x130 := by simp [sibSlot, xLeft, h4, hbit0]
        rw [hS] at ms0 ms1
        have hD : encD L.lay t = 0x120 := by simp [encD, xLeft, h4, hbit0]
        rw [hD] at hM0 hM1
        refine ⟨X, witSib L.wl (L.lay + 1) (heightL (L.lay + 1) - 1), ?_, hMl, hsl, ?_, ?_, ?_, ?_⟩
        · unfold LCtx.msg topPair
          rw [if_neg h4, ← ht', if_neg hbit]
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega),
            mtl _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
          exact hM0
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega),
            mtl _ (by omega) (Or.inr ⟨by omega, by omega⟩)]
          exact hM1
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), ms0]; exact hs0
        · rw [hB, mo _ (by omega) (by omega) (by omega) (by omega), ms1]; exact hs1
  obtain ⟨Lv, Rv, hmsg, hLl, hRl, w2, w3, w4, w5⟩ := hM
  refine ⟨t, ht, u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (gk _ (by simp [gkL, gkL0, baseK])),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by rcases hDv with h | h <;> rw [h, hBv] <;> decide), ?_, ?_, ?_⟩
  · rw [hashInput_ofNat _ (encB L.lay t) 0 h10 h11 (by omega) (by omega), hmsg,
      addrFmt_encInput_words _ _ _ _ _ hLl hRl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, w2, w3, w4, w5, trivial⟩
    · rw [ma]
      congr 1; unfold twLo hWord; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
    · rw [mb, hx31]
      congr 1; unfold twHi; omega
    · rw [mc]
      apply BitVec.eq_of_toNat_eq
      rw [ctrE_eval L.lay hlay L.wl hwl s hctr, BitVec.toNat_ofNat]
      have := witCounter_lt L.wl L.lay
      omega
    · exact md
  · rw [hmsg, addrFmt_encInput_words _ _ _ _ _ hLl hRl]; rfl
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ encD L.lay t ∨ encD L.lay t + 32 ≤ A) =>
      writeHash_frame _ a (encD L.lay t) A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hu.glob _ _ _ hG) a _ h12 (by rcases hDv with h | h <;> rw [h] <;> decide), Known_writeHash hK' a, ?_, ?_, ?_,
      by simpa using writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega),
      by simpa using writeHash_getMem_ofNat u a (encD L.lay t) (encD L.lay t + 16) h12 (by omega) (by omega),
      by simpa using writeHash_getMem_ofNat u a (encD L.lay t) (encD L.lay t + 24) h12 (by omega) (by omega), ?_, ?_, ?_, ?_⟩
    · rw [writeHash_getReg, hu.regs (.x23, uHE L.lay) (by simp [specA]), uHE_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x30, carryEr L.lay) (by simp [specA]), carryEr_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x31, x31Er L.lay) (by simp [specA]), hx31]
    · unfold CB0
      rw [wf 0x340 (by omega) (by omega), mfr 0x340 (by omega) (Or.inr (by omega))]
      exact hC0
    · unfold EncHeader
      rw [wf 0x100 (by omega) (Or.inl (by omega))]
      exact ma
    · refine Fresh_frame hF (fun A hA hA' => ?_)
      rw [wf A hA (Or.inr (by omega)), mfr A hA (Or.inr (by omega))]
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
theorem tgt0_eval (out hi : Nat) (c : CCtx) (s : MachineState) (hD : (d0E out hi).eval s = c.d0) :
    (tgt0 out hi).eval s = pcOf (entW 0 (kOf c 0)) := by
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

theorem encoding_gateThreshold (a : BitVec 256) :
    CmpOp.geu.eval (a.extractLsb' 0 64) (BitVec.ofNat 64 (2^60)) = encodingGate a := by
  simp only [CmpOp.eval, encodingGate, BitVec.ult_eq_decide, BitVec.toNat_ofNat]
  norm_num
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem selection_branches (a : BitVec 256) (s : MachineState) (out : Nat)
    (w0 : s.getMem (BitVec.ofNat 64 out) = a.extractLsb' 0 64)
    (w1 : s.getMem (BitVec.ofNat 64 (out + 8)) = a.extractLsb' 64 64) :
    ∀ b ∈ selBrs out (selOf a), b.holds s := by
  intro b hb
  simp only [selBrs, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  all_goals
    cases h127 : a[127] <;> cases h63 : a[63] <;> cases hg : encodingGate a <;>
      simp [selOf, selLow, selSecond, h127, h63, hg, Br.holds,
        ldE, cw, E.eval, BinOp.eval, w0, w1, encoding_gateThreshold,
        CmpOp.eval, BitVec.slt_zero_eq_msb, BitVec.msb,
        BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_extractLsb']
  all_goals
    have ht := encoding_gateThreshold a
    simpa [CmpOp.eval, hg] using ht

theorem selected_msb_facts (a : BitVec 256) :
    (selOf a = 0 → (encodingAnswer a).getLsbD 63 = false ∧ (encodingAnswer a).getLsbD 127 = false) ∧
    (selOf a = 1 → (encodingAnswer a).getLsbD 127 = true) ∧
    (selOf a = 2 → (encodingAnswer a).getLsbD 63 = false) := by
  cases h127 : a[127] <;> cases h63 : a[63] <;> cases hg : encodingGate a <;>
    simp [selOf, encodingAnswer, h127, h63, hg, BitVec.getLsbD_ushiftRight]


theorem selected_nat_facts (a : BitVec 256) :
    (selOf a = 0 → ((encodingAnswer a).extractLsb' 0 64).toNat < 2^63 ∧
      ((encodingAnswer a).extractLsb' 64 64).toNat < 2^63) ∧
    (selOf a = 1 → 2^63 ≤ ((encodingAnswer a).extractLsb' 64 64).toNat) ∧
    (selOf a = 2 → ((encodingAnswer a).extractLsb' 0 64).toNat < 2^63) := by
  have h0 : ((encodingAnswer a).extractLsb' 0 64).msb = (encodingAnswer a).getLsbD 63 := by
    simp [BitVec.msb, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_extractLsb']
  have h1 : ((encodingAnswer a).extractLsb' 64 64).msb = (encodingAnswer a).getLsbD 127 := by
    simp [BitVec.msb, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_extractLsb']
  have hf := selected_msb_facts a
  rw [← h0, ← h1, BitVec.msb_eq_decide, BitVec.msb_eq_decide] at hf
  simpa using hf

theorem padding_branches (out hi : Nat) (s : MachineState) (A B : Word) (bad : Bool)
    (ha : (d0E out hi).eval s = A) (hb : (d1E out hi).eval s = B)
    (hfirst : hi = 2 → A.toNat < 2^63)
    (hbad : decide (2^63 ≤ A.toNat ∨ 2^63 ≤ B.toNat) = bad) :
    ∀ b ∈ padBrs out hi bad, b.holds s := by
  intro b hbmem
  by_cases h : hi = 0 ∨ hi = 1
  · simp [padBrs, h] at hbmem
  · simp only [padBrs, if_neg h, List.mem_singleton] at hbmem
    subst b
    by_cases h2 : hi = 2
    · have he : (2^63 ≤ A.toNat ∨ 2^63 ≤ B.toNat) ↔ 2^63 ≤ B.toNat := by have := hfirst h2; omega
      have hB : decide (2^63 ≤ B.toNat) = bad := by simpa only [he] using hbad
      simp only [if_pos h2, Br.holds, CmpOp.eval, E.eval, cw]
      rw [hb, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide, hB]
    · simp only [if_neg h2, Br.holds]
      have hor : (orE out hi).eval s = A ||| B := by simp only [orE, E.eval, BinOp.eval, ha, hb]
      rw [hor]
      change (A ||| B).slt 0#64 = bad
      rw [BitVec.slt_zero_eq_msb, BitVec.msb_or, BitVec.msb_eq_decide, BitVec.msb_eq_decide]
      simpa using hbad



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
  obtain ⟨hG, hK, h23, h30, h31, w0, w1, w2, w3, hCB, hEH, hF, hpc⟩ := hs
  simp only [Nat.add_zero] at w0
  have hD0 : (d0E (encD L.lay t) hi).eval s = (encodingAnswer a).extractLsb' 0 64 := by
    have hw := Sign.encoding_word a 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at hw
    rw [hw]
    cases h127 : a[127] <;> cases h63 : a[63] <;> cases hg : encodingGate a <;>
      simp [hi, selOf, d0E, h127, h63, hg, ldE, cw, E.eval, w0, w1, w2]
  have hD1 : (d1E (encD L.lay t) hi).eval s = (encodingAnswer a).extractLsb' 64 64 := by
    have hw := Sign.encoding_word a 1 (by decide)
    simp only [Nat.mul_one, Nat.reduceAdd] at hw
    rw [hw]
    cases h127 : a[127] <;> cases h63 : a[63] <;> cases hg : encodingGate a <;>
      simp [hi, selOf, d1E, h127, h63, hg, ldE, cw, E.eval, w1, w2, w3]
  have hsel : ∀ b ∈ selBrs (encD L.lay t) hi, b.holds s := selection_branches a s (encD L.lay t) w0 w1
  have hpad (bad : Bool)
      (hbad : decide (2^63 ≤ ((encodingAnswer a).extractLsb' 0 64).toNat ∨
        2^63 ≤ ((encodingAnswer a).extractLsb' 64 64).toNat) = bad) :
      ∀ b ∈ padBrs (encD L.lay t) hi bad, b.holds s :=
    padding_branches (encD L.lay t) hi s _ _ bad hD0 hD1 (selected_nat_facts a).2.2 hbad
  have hor : CmpOp.lt.eval ((orE (encD L.lay t) hi).eval s) ((E.c 0).eval s) =
      decide (2 ^ 63 ≤ ((encodingAnswer a).extractLsb' 0 64).toNat ∨ 2 ^ 63 ≤ ((encodingAnswer a).extractLsb' 64 64).toNat) := by
    rw [show (orE (encD L.lay t) hi).eval s = (d0E (encD L.lay t) hi).eval s ||| (d1E (encD L.lay t) hi).eval s from rfl,
      hD0, hD1]
    exact lt_or_eval _ _
  have hdA : dA (encD L.lay t) hi s = ((encodingAnswer a).extractLsb' 0 64).toNat := by simp only [dA, hD0]
  have hdB : dB (encD L.lay t) hi s = ((encodingAnswer a).extractLsb' 64 64).toNat := by simp only [dB, hD1]
  have hT : targetFor L.lay < 2 ^ 64 := by have := targetFor_le L.lay; omega
  by_cases hgate : hi = 1
  · have hdnone : decodeDigits L.lay (encodingBytes a) = none := by
      have hg := (selected_nat_facts a).2.1 hgate
      unfold encodingBytes decodeDigits
      simp only [slice0_answer, slice8_answer]
      rw [if_neg (by omega)]
    constructor
    · intro _
      obtain ⟨u, hu⟩ := specO_run (lc_gate_reject hlay ht) s hpc hK (encObligs_holds s) (by
        simpa only [specRej1, padBrs, show (1:Nat)=1 from rfl, or_true, if_true, List.nil_append, ← hgate] using hsel)
      exact ⟨8, by omega, 8, by omega, u, hu.steps, hu.ecall rfl,
        hu.regs (.x5, cw 1) (by simp [specRej1, rejK]),
        hu.regs (.x10, cw 1) (by simp [specRej1, rejK])⟩
    · intro xs hx; rw [hdnone] at hx; cases hx
  · obtain ⟨hBok, hR1, hR2⟩ := lc_enc hlay hi hhi hgate ht
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
          rcases hb with (rfl | hb) | hb
          · simp only [Br.holds, CmpOp.eval, bne_iff_ne, ne_eq]
            intro h
            apply hsum
            have := (swS_eq (encD L.lay t) hi s L.lay (by omega) (by omega)).mp h
            rwa [hdA, hdB] at this
          · exact hpad false (decide_eq_false (by omega)) _ hb
          · exact hsel _ hb)
        exact ⟨17 + selSteps hi, by omega,
          20 + selSteps hi, by omega, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej2, rejK]),
          hu.regs (.x10, cw 1) (by simp [specRej2, rejK])⟩
      · have hn0 : hi ≠ 0 := by intro he; exact hlt ((selected_nat_facts a).1 he)
        obtain ⟨u, hu⟩ := specO_run (hR1 hn0) s hpc hK (encObligs_holds s) (by
          intro b hb
          simp only [specRej1, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with hb | hb
          · exact hpad true (decide_eq_true (by omega)) _ hb
          · exact hsel _ hb)
        exact ⟨rej1Steps hi, by unfold rej1Steps; split_ifs <;> omega, rej1Steps hi, by unfold rej1Steps; split_ifs <;> omega, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej1, rejK]),
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
            rcases hb with (rfl | hb) | hb
            · simp only [Br.holds, CmpOp.eval, bne_eq_false_iff_eq]
              apply (swS_eq (encD L.lay t) hi s L.lay (by omega) (by omega)).mpr
              rw [hdA, hdB]; exact hsum
            · exact hpad false (decide_eq_false (by omega)) _ hb
            · exact hsel _ hb)
          have hcok : (L.cctx t a).ok :=
            ⟨hlay, by have := tau_lt L.lay L.idx hlay hidx; simp only [LCtx.cctx, LCtx.tau] at this ⊢; omega,
              by have := e_lt L ⟨hlay, hidx, hwl⟩; simp only [LCtx.cctx] at this ⊢; omega, hwl, hlt.1, hlt.2⟩
          have hmem : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
          have hK' := hu.known
          have hK0 : KnownOK chK0 u := fun p hp => hK' p (List.mem_append_left _ hp)
          refine ⟨u, hu.steps, ⟨⟨hu.glob _ _ _ hG, hK0, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_,
            fun j hj => by simp at hj, rfl, by simp, ?_, ?_⟩, ?_, ?_, ?_⟩, hcok, ?_, hsum, by simp [digitsOfWord]⟩
          · rw [hu.regs (.x16, d0E (encD L.lay t) hi) (by simp [specBok])]; exact hD0
          · rw [hu.regs (.x17, d1E (encD L.lay t) hi) (by simp [specBok])]; exact hD1
          · rw [hu.keep .x23 (by simp)]; exact h23
          · rw [hu.keep .x30 (by simp)]; exact h30
          · rw [hu.keep .x31 (by simp)]; exact h31
          · exact hK' (.x22, BitVec.ofNat 64 (s6N L.lay)) (by simp [chKa])
          · exact hK' (.x27, 0x40401#64) (by simp [chKa])
          · exact hK' (.x1, pcOf (retPc L.lay t)) (by simp [chKa])
          · unfold CB0; rw [hmem]; exact hCB
          · unfold EncHeader; rw [hmem]; exact hEH
          · trivial
          · exact Fresh_frame hF (fun A _ _ => hmem _)
          · rw [hu.spc _ rfl, tgt0_eval (encD L.lay t) hi (L.cctx t a) s hD0]
            simp [startPc]
          · intro i hi
            rw [digits_getD _ _ i hi]; unfold dig; simp only [LCtx.cctx]; split <;> rfl
        · rw [if_neg hsum] at hxs; cases hxs
      · rw [if_neg hlt] at hxs; cases hxs


end SigGolfCandidate.Verify
