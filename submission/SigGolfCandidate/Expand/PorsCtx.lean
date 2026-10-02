import SigGolfCandidate.Expand.P2Base
import SigGolfCandidate.Verify.Words
import SigGolfCandidate.Ref.AddressFormat

/-!
# `expand`, phase 2: the rev16 network of the fold trampolines (804 .. 831, 832 .. 859)

`netN v` is the `Nat` model of the 24-instruction swap network on `v < 2^16` (before the final
`slli 48`): it reverses the low 16 bits, so `netN v * 2^16 = Rev.efield v` for heap indices
`v < 2^14` (checked by `decide +kernel`, `Nat` bitwise ops are kernel-accelerated).
-/

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Ref

/-- `Nat` model of the rev16 swap network (bytes, nibbles, pairs, bits). -/
def netN (v : Nat) : Nat :=
  let r := v / 256 ||| (v &&& 255) * 256
  let r := (r / 16 &&& 3855) ||| (r &&& 3855) * 16
  let r := (r / 4 &&& 13107) ||| (r &&& 13107) * 4
  (r / 2 &&& 21845) ||| (r &&& 21845) * 2

/-- `P i ∧ P (i+1) ∧ … ∧ P (i+k-1)`, evaluated by the kernel. -/
def chkFrom (P : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, i => P i && chkFrom P k (i + 1)

theorem chkFrom_spec (P : Nat → Bool) :
    ∀ k i, chkFrom P k i = true → ∀ j, i ≤ j → j < i + k → P j = true
  | 0, i, _, j, h1, h2 => absurd h2 (by omega)
  | k + 1, i, h, j, h1, h2 => by
    simp only [chkFrom, Bool.and_eq_true] at h
    by_cases hj : j = i
    · subst hj; exact h.1
    · exact chkFrom_spec P k (i + 1) h.2 j (by omega) (by omega)

theorem netN_chk : chkFrom (fun v => netN v * 65536 == Rev.efield v) 16384 0 = true := by
  decide +kernel

/-- The network computes the relabelled header field of every PORS heap index `v < 2^14`. -/
theorem netN_efield (v : Nat) (hv : v < 2 ^ 14) : netN v * 65536 = Rev.efield v := by
  have := chkFrom_spec _ _ _ netN_chk v (Nat.zero_le _) (by omega)
  simpa using this

end SigGolfCandidate.ExP

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
`s10 = idx mod 2^32`, `s11 = 0x1000` (W1: the secrets at `s11 + 1024 + 64 s`); the first word and the zero words of `LB` and
`PB`; the witness buffer; the sorted keys `K` at `0x6E0`. -/
structure PCtx (w : List Byte) (idx : Nat) (K : Nat → Nat) (t : MachineState) : Prop where
  hidx : idx < 2 ^ 34
  x4 : t.getReg .x4 = BitVec.ofNat 64 idx
  x5 : t.getReg .x5 = 0
  x22 : t.getReg .x22 = BitVec.ofNat 64 0x30540
  x25 : t.getReg .x25 = BitVec.ofNat 64 0x30000
  x26 : t.getReg .x26 = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32)
  x27 : t.getReg .x27 = BitVec.ofNat 64 0x1000
  lb0 : t.getMem (BitVec.ofNat 64 0x30000) = BitVec.ofNat 64 (1 + 256 * 9 + 2 ^ 24 * (idx / 2 ^ 32) + 2 ^ 32 * (idx % 2 ^ 32))
  lb16 : t.getMem (BitVec.ofNat 64 0x30010) = 0
  lb24 : t.getMem (BitVec.ofNat 64 0x30018) = 0
  lb48 : t.getMem (BitVec.ofNat 64 0x30030) = 0
  lb56 : t.getMem (BitVec.ofNat 64 0x30038) = 0
  pb0 : t.getMem (BitVec.ofNat 64 0x30040) = BitVec.ofNat 64 (1 + 256 * 10 + 2 ^ 24 * (idx / 2 ^ 32) + 2 ^ 32 * (idx % 2 ^ 32))
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
    (h72 : t.getMem (BitVec.ofNat 64 0x30048) = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32 + 2 ^ 32 * H))
    (hlw : t.readWords (BitVec.ofNat 64 0x30060) 2 = wordsOf l)
    (hrw : t.readWords (BitVec.ofNat 64 0x30070) 2 = wordsOf r) :
    t.readWords (BitVec.ofNat 64 0x30040) 8 = wordsOf (padTo64 (Verify.pNode idx H l r)) := by
  rw [Verify.pNode, (words_th32 10 0 (Ref.tauH idx) idx H l r hl hr).2, twWords_pors 10 idx H (by norm_num) h.hidx hH,
    ← hlw, ← hrw, readWords8, readWords_ofNat_two, readWords_ofNat_two, h.pb0, h72, h.pb16, h.pb24]
  rfl

/-- The LB words for the leaf hash of leaf `x` with secret `s`. -/
theorem lb_words (w : List Byte) (idx : Nat) (K : Nat → Nat) (t : MachineState) (h : PCtx w idx K t)
    (x : Nat) (hx : x < 2 ^ 32) (s : Val) (hs : s.length = 16)
    (h8 : t.getMem (BitVec.ofNat 64 0x30008) = BitVec.ofNat 64 (Ref.tauH idx % 2 ^ 32 + 2 ^ 32 * x))
    (hsw : t.readWords (BitVec.ofNat 64 0x30020) 2 = wordsOf s) :
    t.readWords (BitVec.ofNat 64 0x30000) 8 = wordsOf (padTo64 (Verify.pLeaf idx x s)) := by
  rw [Verify.pLeaf, (words_th16 9 0 (Ref.tauH idx) idx x s hs).2, twWords_pors 9 idx x (by norm_num) h.hidx hx,
    ← hsw, readWords8, readWords_ofNat_two, h.lb0, h8, h.lb16, h.lb24, h.lb48, h.lb56]
  rfl

/-- The PORS node query relabels the header field: `Rev.efield H`. -/
theorem fmt_porsNode (idx H : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    addrFmt (porsNodeInput idx H l r) = pad64 (Verify.pNode idx (Rev.efield H) l r) :=
  Verify.addrFmt_porsNodeInput_pad idx H l r hl hr

theorem fmt_porsLeaf (idx j : Nat) (s : Val) (hs : s.length = 16) (hj : j ≤ 2^14) :
    addrFmt (porsLeafInput idx j s) = pad64 (Verify.pLeaf idx (8*j) s) :=
  Verify.addrFmt_porsLeafInput_pad idx j s hs hj

theorem blocks_porsNode (idx H : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    (pad64 (Verify.pNode idx H l r)).blocks = 1 :=
  congrArg (· + 1) (words_th32 10 0 (Ref.tauH idx) idx H l r hl hr).1

theorem blocks_porsLeaf (idx j : Nat) (s : Val) (hs : s.length = 16) :
    (pad64 (Verify.pLeaf idx j s)).blocks = 1 :=
  congrArg (· + 1) (words_th16 9 0 (Ref.tauH idx) idx j s hs).1

end SigGolfCandidate.ExP
