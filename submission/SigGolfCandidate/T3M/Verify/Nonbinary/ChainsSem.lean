import SigGolfCandidate.T3M.Verify.ChainSem
import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout

/-! Machine semantics of one mixed-radix top chain, with exact immutable image checks supplied separately. -/
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

structure NCtx where
  w : WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  digits : Nat → Nat
  ret : Nat

namespace NCtx

def blk (c : NCtx) (i : Nat) : Nat := c.S3 - 1664 + 64 * (53 - i)
def dig (c : NCtx) (i : Nat) : Nat := c.digits i
def topMax (i : Nat) : Nat := mx (i / 3)
def last (i : Nat) : Nat := topMax i - 1

def w0 (i : Nat) : Nat := 0x101 + 2 ^ 40 * i
def w1 (c : NCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
def val (c : NCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)
def ok (c : NCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.S3 % 8 = 0 ∧ 0x800 + 10568 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x7000 ∧
    c.ret < 209920

/-- T3Z (BIG3): `x28` is the midpoint of the WOTS header table's bank 0 (set by the lower layers' leaf-pk restore
`lui t3, 0xff4`); every head reads its header word from the table. -/
def known (c : NCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (Verify.headerBank 0 0)), (.x19, BitVec.ofNat 64 c.S3),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 0x401), (.x1, pcOf c.ret)]

def kOf (c : NCtx) (q : Nat) : Nat :=
  c.dig (3*q) + (mx q+1)*c.dig (3*q+1) + (mx q+1)^2*c.dig (3*q+2)
def qb (c : NCtx) (i : Nat) : Nat := base (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qB (c : NCtx) (i : Nat) : Nat := pcB (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qC (c : NCtx) (i : Nat) : Nat := pcC (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def qX (c : NCtx) (i : Nat) : Nat := pcX (i/3) (c.dig (3*(i/3)+1)) (c.dig (3*(i/3)+2))
def startPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then entW (i/3) (c.kOf (i/3)) else if i%3=1 then c.qB i else c.qC i

def rungPc (c : NCtx) (i m : Nat) : Nat :=
  if i%3=0 then c.qb i+2*m
  else c.startPc i + (if c.dig i = last i then 3 else 4) + 2*(m-c.dig i)
def endPc (c : NCtx) (i : Nat) : Nat :=
  if i%3=0 then c.qB i else if i%3=1 then c.qC i else c.qX i

/-- The memory written by the chains `0 .. i - 1`. -/
def Wr (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  (0x200 ≤ A ∧ A < 0x5D0) ∨ (c.S3 - 1664 + 64 * (54 - i) ≤ A ∧ A < c.blk 0 + 80)
def WrIn (c : NCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)

/-- The chain blocks hold the witness at the start `s0`, and (T3Z) the image data (the WOTS header table) is in
place. -/
def Orig0 (c : NCtx) (s0 : MachineState) : Prop :=
  (∀ i, i < 54 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)) ∧ Verify.DataOK s0

def Base (c : NCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))

/-- Before chain `i`'s code (T3Z: no running `x25`; the heads read the header table). -/
def ChainIn (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ s.pc = pcOf (c.startPc i)

def HdrOk (c : NCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1

def StepInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    (m < last i → s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48)) ∧ s.pc = pcOf (c.rungPc i m)

def PreHash (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = last i then slot i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = last i then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)

def EndInv (c : NCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.pc = pcOf (c.endPc i)

/-! ## Geometry -/

theorem blk_props (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    c.blk i % 8 = 0 ∧ 0x800 + 10568 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem blk_le (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) : c.blk i + 64 * i = c.blk 0 := by
  obtain ⟨-, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem slot_props (i : Nat) (hi : i < 54) : slot i % 16 = 0 ∧ 512 ≤ slot i ∧ slot i + 32 ≤ 0x580 := by
  unfold slot; split <;> omega

theorem base_off (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (off i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem base_off0 (c : NCtx) (hc : c.ok) (i : Nat) (hi : i < 54) :
    BitVec.ofNat 64 c.S3 + off i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold off blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + 64 * (53 - i) - 1664 = c.S3 - 1664 + 64 * (53 - i) by
    omega]

theorem w0_hdr0 (c : NCtx) (i m : Nat) (hi : i < 54) (hm : m < 256) (ht : c.tree < 2 ^ 32) :
    w0 i + 2 ^ 32 * m = hdr0 1 (0 : Layer).val c.tree (m + 256 * i) := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by norm_num) ht (by omega)]
  unfold w0; simp; ring

theorem w0_lt (i m : Nat) (hi : i < 54) (hm : m < 256) : w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  unfold w0; omega

/-- The machine's hash input at a step of chain `i`. -/
theorem chain_hashInput (c : NCtx) (hc : c.ok) (i m : Nat) (hi : i < 54) (hm : m < 256) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.blk i) (c.pad0 i)) (hp1 : DigAt t (c.blk i + 32) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1)
    (hv : DigAt t (c.blk i + 48) v) :
    hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputP_length _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputP, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two, hp0.1, hp0.2,
    show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
    show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
    show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
    show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c i m hi hm hc.1]
  rfl

theorem orig_frame {c : NCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i < 54) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0.1 i hi k hk

theorem pads_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i < 54) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.blk i) (c.pad0 i) ∧ DigAt t (c.blk i + 32) (c.pad1 i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5 → ¬ c.WrIn i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold WrIn Wr blk at *
    omega
  have o0 := orig_frame hF h0 hc hi (k := 0) (by omega) (nW 0 (by omega))
  have o1 := orig_frame hF h0 hc hi (k := 1) (by omega) (nW 1 (by omega))
  have o4 := orig_frame hF h0 hc hi (k := 4) (by omega) (nW 4 (by omega))
  have o5 := orig_frame hF h0 hc hi (k := 5) (by omega) (nW 5 (by omega))
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at o0 o1
  rw [show 8 * 4 = 32 by rfl] at o4
  rw [show c.blk i + 8 * 5 = c.blk i + 32 + 8 by ring] at o5
  refine ⟨DigAt_origW o0 o1 (by omega), ?_⟩
  have := DigAt_origW o4 o5 (by omega)
  rwa [show c.blk i + 32 - 0x800 = c.blk i - 0x800 + 32 by omega] at this

theorem val_at {c : NCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i < 54)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.blk i + 48) (c.val i) := by
  have hb := c.blk_props hc i hi
  have nW : ∀ k, k = 6 ∨ k = 7 → ¬ c.Wr i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    unfold Wr blk at *
    omega
  have o6 := orig_frame hF h0 hc hi (k := 6) (by omega) (nW 6 (by omega))
  have o7 := orig_frame hF h0 hc hi (k := 7) (by omega) (nW 7 (by omega))
  rw [show c.blk i + 8 * 6 = c.blk i + 48 by ring] at o6
  rw [show c.blk i + 8 * 7 = c.blk i + 48 + 8 by ring] at o7
  have := DigAt_origW o6 o7 (by omega)
  rwa [show c.blk i + 48 - 0x800 = c.blk i - 0x800 + 48 by omega] at this

theorem topMax_bounds (i : Nat) : 3 ≤ topMax i ∧ topMax i ≤ 4 := by
  unfold topMax mx; split <;> omega

theorem last_bounds (i : Nat) : 2 ≤ last i ∧ last i ≤ 3 := by
  have := topMax_bounds i; unfold last; omega

theorem rungPc_succ (c : NCtx) (i m : Nat) (hd : c.dig i ≤ m) :
    c.rungPc i (m+1) = c.rungPc i m+2 := by
  unfold rungPc; split_ifs <;> omega

theorem rungPc_end (c : NCtx) (i : Nat) (hi : i < 54) (hd : c.dig i < topMax i) :
    c.rungPc i (last i) + 3 = c.endPc i := by
  have hm := topMax_bounds i
  have e1 : i%3=1 → c.dig (3*(i/3)+1)=c.dig i := fun h => by rw [show 3*(i/3)+1=i by omega]
  have e2 : i%3=2 → c.dig (3*(i/3)+2)=c.dig i := fun h => by rw [show 3*(i/3)+2=i by omega]
  unfold rungPc endPc startPc qb qB qC qX pcX pcC pcB partLen
  unfold last topMax at *
  split_ifs <;> omega

/-- The step registers hold the steps. -/
theorem posE_eval (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i m : Nat) (hm : m ≤ last i) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hm3 : m ≤ 3 := by have := last_bounds i; omega
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)
  · exact kr .x8 3 (by simp [known]) (by decide)

theorem w0_low (i m : Nat) (hi : i < 54) (hm : m < 256) :
    (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 ∧
      (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi hm)]
  unfold w0; constructor <;> omega

theorem w0_low0 (i : Nat) (hi : i < 54) :
    (BitVec.ofNat 64 (w0 i)).toNat % 2 ^ 32 = 0x101 ∧ (BitVec.ofNat 64 (w0 i)).toNat / 2 ^ 40 = i := by
  have := w0_low i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this

end NCtx
end SigGolfCandidate.T3M.Nonbinary
