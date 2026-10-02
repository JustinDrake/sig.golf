import SigGolfCandidate.Expand.P2Base

/-!
# `expand`, phase 2: the PORS context

Scratch `X = 0x30000`: the leaf block `LB = X` (`tw(9) | 0 | secret | 0`), the node block
`PB = X + 64` (`tw(10) | 0 | l | r`), the current node `OUT = X + 128`, the stack
`STK = X + 1344` (32-byte entries: node, heap index).

`PCtx w idx K t` : the registers and words that stay constant during the PORS phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- The constant part of the PORS phase: `tp = idx`, `t0 = 0`, `s6 = STK`, `s9 = X`,
`s10 = idx mod 2^32`, `s11 = 0x800` (the witness); the first word and the zero words of `LB` and
`PB`; the witness buffer; the sorted keys `K` at `0x6E0`. -/
structure PCtx (w : List Byte) (idx : Nat) (K : Nat → Nat) (t : MachineState) : Prop where
  hidx : idx < 2 ^ 34
  x4 : t.getReg .x4 = BitVec.ofNat 64 idx
  x5 : t.getReg .x5 = 0
  x22 : t.getReg .x22 = BitVec.ofNat 64 0x30540
  x25 : t.getReg .x25 = BitVec.ofNat 64 0x30000
  x26 : t.getReg .x26 = BitVec.ofNat 64 (idx % 2 ^ 32)
  x27 : t.getReg .x27 = BitVec.ofNat 64 0x800
  lb0 : t.getMem (BitVec.ofNat 64 0x30000) = BitVec.ofNat 64 (1 + 256 * 9 + 2 ^ 24 * (idx / 2 ^ 32))
  lb16 : t.getMem (BitVec.ofNat 64 0x30010) = 0
  lb24 : t.getMem (BitVec.ofNat 64 0x30018) = 0
  lb48 : t.getMem (BitVec.ofNat 64 0x30030) = 0
  lb56 : t.getMem (BitVec.ofNat 64 0x30038) = 0
  pb0 : t.getMem (BitVec.ofNat 64 0x30040) = BitVec.ofNat 64 (1 + 256 * 10 + 2 ^ 24 * (idx / 2 ^ 32))
  pb16 : t.getMem (BitVec.ofNat 64 0x30050) = 0
  pb24 : t.getMem (BitVec.ofNat 64 0x30058) = 0
  wit : WitMem w t
  keys : ∀ p < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (K p)
  klt : ∀ p < 15, K p < 2 ^ 22

/-- Addresses `PCtx` reads. -/
def pctxA (a : Nat) : Prop :=
  a = 0x30000 ∨ a = 0x30010 ∨ a = 0x30018 ∨ a = 0x30030 ∨ a = 0x30038 ∨ a = 0x30040 ∨
    a = 0x30050 ∨ a = 0x30058 ∨ (0x6E0 ≤ a ∧ a < 0x758) ∨ witA a

/-- Registers `PCtx` reads. -/
def pctxRegs : List Reg := [.x4, .x5, .x22, .x25, .x26, .x27]

theorem PCtx.frame {w : List Byte} {idx : Nat} {K : Nat → Nat} {s t : MachineState} {W : Nat → Prop}
    {l : List Reg} (h : PCtx w idx K s) (hf : Frame s t W) (hr : RegsEq s t l)
    (hW : ∀ a, pctxA a → ¬ W a) (hl : ∀ r ∈ pctxRegs, r ∉ l := by decide) : PCtx w idx K t := by
  have g : ∀ a, a < 2 ^ 64 → pctxA a → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) :=
    fun a ha hp => hf a ha (hW a hp)
  refine ⟨h.hidx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.klt⟩
  · rw [hr.get .x4 (hl _ (by decide)), h.x4]
  · rw [hr.get .x5 (hl _ (by decide)), h.x5]
  · rw [hr.get .x22 (hl _ (by decide)), h.x22]
  · rw [hr.get .x25 (hl _ (by decide)), h.x25]
  · rw [hr.get .x26 (hl _ (by decide)), h.x26]
  · rw [hr.get .x27 (hl _ (by decide)), h.x27]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.lb0]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.lb16]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.lb24]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.lb48]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.lb56]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.pb0]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.pb16]
  · rw [g _ (by norm_num) (by unfold pctxA; omega), h.pb24]
  · exact h.wit.frame hf (fun a ha => hW a (by unfold pctxA; simp only [ha, or_true]))
  · intro p hp; rw [g _ (by omega) (by unfold pctxA; omega), h.keys p hp]

/-- The PB words for a node hash with heap index `H` and children `l`, `r`. -/
theorem pb_words (w : List Byte) (idx : Nat) (K : Nat → Nat) (t : MachineState) (h : PCtx w idx K t)
    (H : Nat) (hH : H < 2 ^ 32) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (h72 : t.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * H))
    (hlw : t.readWords (BitVec.ofNat 64 0x30060) 2 = wordsOf l)
    (hrw : t.readWords (BitVec.ofNat 64 0x30070) 2 = wordsOf r) :
    t.readWords (BitVec.ofNat 64 0x30040) 8 = wordsOf (padTo64 (porsNodeInput idx H l r)) := by
  rw [porsNodeInput, (words_th32 10 0 idx 0 H l r hl hr).2, twWords_pors 10 idx H (by norm_num) h.hidx hH,
    ← hlw, ← hrw, readWords8, readWords_ofNat_two, readWords_ofNat_two, h.pb0, h72, h.pb16, h.pb24]
  rfl

/-- The LB words for the leaf hash of leaf `x` with secret `s`. -/
theorem lb_words (w : List Byte) (idx : Nat) (K : Nat → Nat) (t : MachineState) (h : PCtx w idx K t)
    (x : Nat) (hx : x < 2 ^ 32) (s : Val) (hs : s.length = 16)
    (h8 : t.getMem (BitVec.ofNat 64 0x30008) = BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * x))
    (hsw : t.readWords (BitVec.ofNat 64 0x30020) 2 = wordsOf s) :
    t.readWords (BitVec.ofNat 64 0x30000) 8 = wordsOf (padTo64 (porsLeafInput idx x s)) := by
  rw [porsLeafInput, (words_th16 9 0 idx 0 x s hs).2, twWords_pors 9 idx x (by norm_num) h.hidx hx,
    ← hsw, readWords8, readWords_ofNat_two, h.lb0, h8, h.lb16, h.lb24, h.lb48, h.lb56]
  rfl

theorem fmt_porsNode (idx H : Nat) (l r : Val) : addrFmt (porsNodeInput idx H l r) = pad64 (porsNodeInput idx H l r) :=
  addrFmt_thInput _ _ _ _ _ _ (by decide)

theorem fmt_porsLeaf (idx j : Nat) (s : Val) : addrFmt (porsLeafInput idx j s) = pad64 (porsLeafInput idx j s) :=
  addrFmt_thInput _ _ _ _ _ _ (by decide)

theorem blocks_porsNode (idx H : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    (pad64 (porsNodeInput idx H l r)).blocks = 1 :=
  congrArg (· + 1) (words_th32 10 0 idx 0 H l r hl hr).1

theorem blocks_porsLeaf (idx j : Nat) (s : Val) (hs : s.length = 16) :
    (pad64 (porsLeafInput idx j s)).blocks = 1 :=
  congrArg (· + 1) (words_th16 9 0 idx 0 j s hs).1

end SigGolfCandidate.ExP
