import SigGolfCandidate.T3M.Verify.ChainSem

/-! # V1 top chains: semantics of the quad code (`Steps` level)

The top layer's chains `0 .. 48` (width 2) run through `qtab` (quads `(4q .. 4q+3)`, `q < 12`) and the shared blocks
`tq_q_dB_dC_dD`, chain 48 through `q48tab`; `q48_done` then dispatches into the lower code's triple 11 (the top's
chains `49 .. 57` run as the lower code chains `33 .. 41`, `LCtx` with `i0 = 33`, `koff = 16`, `ck = 8`).

`QCtx` mirrors `LCtx`: the chain blocks are addressed from `s3 = x19` (`blk i = s3 - 1664 + 64 (57 - i)`), the ends
go to the top leaf-pk slots `slotT i`, the digits are the radix-4 digits of `a6` (`i < 32`) and of `a7 = v1 << 2`
(`32 ≤ i ≤ 48`, at bit `2 (i - 32) + 2`). -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

/-- A run of the top quad code over the chains `0 .. 48`: the witness, the header fields (tree, leaf), `s3`, `s6`
(kept for the lower code), the digit words `a6`, `a7`, and the return pc (the transition copy's leaf-pk block). -/
structure QCtx where
  w : WBytes
  tree : Nat
  leaf : Nat
  S3 : Nat
  S6 : Nat
  d0 : Word
  d1 : Word
  ret : Nat

namespace QCtx

/-- The machine address of chain `i`'s block. -/
def blk (c : QCtx) (i : Nat) : Nat := c.S3 - 1664 + 64 * (57 - i)
/-- The radix-4 digit of chain `i < 49`. -/
def dig (c : QCtx) (i : Nat) : Nat :=
  if i < 32 then c.d0.toNat / 4 ^ i % 4 else c.d1.toNat / 4 ^ (i - 31) % 4
/-- Header word 0 of chain `i` with step byte 0 (layer 0). -/
def w0 (i : Nat) : Nat := 0x101 + 2 ^ 40 * i
def w1 (c : QCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : QCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : QCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
def val (c : QCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)

def ok (c : QCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.S3 % 8 = 0 ∧ 0x800 + 11288 + 1664 ≤ c.S3 ∧ c.S3 + 2064 ≤ 0x7000 ∧
    c.ret < 209920

/-- The registers the quad code reads (and the lower code after it). -/
def known (c : QCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (2 ^ 40)), (.x2, 0x3fe00), (.x15, 0xae000), (.x22, BitVec.ofNat 64 c.S6),
   (.x19, BitVec.ofNat 64 c.S3), (.x24, 0x1fe00),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 0x101),
   (.x16, c.d0), (.x17, c.d1), (.x29, BitVec.ofNat 64 8), (.x1, pcOf c.ret)]

/-- The table row of quad `q`. -/
def kOf (c : QCtx) (q : Nat) : Nat :=
  c.dig (4 * q) + 4 * c.dig (4 * q + 1) + 16 * c.dig (4 * q + 2) + 64 * c.dig (4 * q + 3)
/-- The shared block of chain `i`'s quad and its parts. -/
def qb (c : QCtx) (i : Nat) : Nat :=
  quadBase (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
def qB (c : QCtx) (i : Nat) : Nat :=
  qpcB (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
def qC (c : QCtx) (i : Nat) : Nat :=
  qpcC (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
def qD (c : QCtx) (i : Nat) : Nat :=
  qpcD (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))
def qX (c : QCtx) (i : Nat) : Nat :=
  qpcX (i / 4) (c.dig (4 * (i / 4) + 1)) (c.dig (4 * (i / 4) + 2)) (c.dig (4 * (i / 4) + 3))

def startPc (c : QCtx) (i : Nat) : Nat :=
  if i = 48 then q48tabIdx + 8 * c.dig 48
  else if i % 4 = 0 then qentW (i / 4) (c.kOf (i / 4)) else if i % 4 = 1 then c.qB i
  else if i % 4 = 2 then c.qC i else c.qD i
def rungPc (c : QCtx) (i m : Nat) : Nat :=
  if i = 48 then q48R0 + 2 * m
  else if i % 4 = 0 then c.qb i + 2 * m
  else (if i % 4 = 1 then c.qB i else if i % 4 = 2 then c.qC i else c.qD i) + 5 + 2 * (m - c.dig i)
def endPc (c : QCtx) (i : Nat) : Nat :=
  if i = 48 then q48Done else if i % 4 = 0 then c.qB i else if i % 4 = 1 then c.qC i
  else if i % 4 = 2 then c.qD i else c.qX i

/-- The memory written by the chains `0 .. i - 1`. -/
def Wr (c : QCtx) (i : Nat) (A : Nat) : Prop :=
  (0x200 ≤ A ∧ A < 0x5D0) ∨ (c.S3 - 1664 + 64 * (58 - i) ≤ A ∧ A < c.blk 0 + 80)
def WrIn (c : QCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)

def Orig0 (c : QCtx) (s0 : MachineState) : Prop :=
  ∀ i, i ≤ 48 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)

def Base (c : QCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slotT j) (acc.getD j 0))

def ChainIn (c : QCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i ∧ (i ≠ 0 → s.getReg .x25 = BitVec.ofNat 64 (w0 (i - 1))) ∧
    s.pc = pcOf (c.startPc i)

def HdrOk (c : QCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1

def StepInv (c : QCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i ∧ s.getReg .x25 = BitVec.ofNat 64 (w0 i) ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) ∧ s.pc = pcOf (c.rungPc i m)

def PreHash (c : QCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i ∧ t.getReg .x25 = BitVec.ofNat 64 (w0 i) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = 2 then slotT i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = 2 then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)

def EndInv (c : QCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 ∧ s.getReg .x25 = BitVec.ofNat 64 (w0 i) ∧
    s.pc = pcOf (c.endPc i)

/-! ## Geometry -/

theorem blk_props (c : QCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 48) :
    c.blk i % 8 = 0 ∧ 0x800 + 11288 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega

theorem blk_le (c : QCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 48) : c.blk i + 64 * i = c.blk 0 := by
  obtain ⟨-, -, -, hlo, -⟩ := hc
  unfold blk; omega

theorem slotT_props (i : Nat) (hi : i ≤ 48) : slotT i % 16 = 0 ∧ 512 ≤ slotT i ∧ slotT i + 32 ≤ 0x530 := by
  unfold slotT; split <;> omega

theorem base_off (c : QCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 48) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S3 + (offT i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold offT blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S3 + 64 * (57 - i) - 1664 = c.S3 - 1664 + 64 * (57 - i) by
    omega]

theorem base_off0 (c : QCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 48) :
    BitVec.ofNat 64 c.S3 + offT i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, hlo, hhi, -⟩ := hc
  unfold offT blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S3 + 64 * (57 - i) - 1664 = c.S3 - 1664 + 64 * (57 - i) by
    omega]

theorem w0_hdr0 (c : QCtx) (i m : Nat) (hi : i ≤ 48) (hm : m < 256) (ht : c.tree < 2 ^ 32) :
    w0 i + 2 ^ 32 * m = hdr0 1 (0 : Layer).val c.tree (m + 256 * i) := by
  rw [hdr0_eq _ _ _ _ (by norm_num) (by norm_num) ht (by omega)]
  unfold w0; simp; ring

theorem w0_lt (i m : Nat) (hi : i ≤ 48) (hm : m < 256) : w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  unfold w0; omega

/-- The machine's hash input at a step of chain `i`. -/
theorem chain_hashInput (c : QCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 48) (hm : m < 256) (v : Digest)
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

theorem orig_frame {c : QCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : i ≤ 48) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := c.blk_props hc i hi
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0 i hi k hk

theorem pads_at {c : QCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : i ≤ 48) (hF : Frame s0 t (c.WrIn i)) :
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

theorem val_at {c : QCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : i ≤ 48)
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

theorem dig_lt4 (c : QCtx) (i : Nat) : c.dig i < 4 := by unfold dig; split_ifs <;> omega

theorem rungPc_succ (c : QCtx) (i m : Nat) (hd : c.dig i ≤ m) : c.rungPc i (m + 1) = c.rungPc i m + 2 := by
  unfold rungPc; split_ifs <;> omega

theorem rungPc_end (c : QCtx) (i : Nat) (hi : i ≤ 48) (hd : c.dig i < 3) : c.rungPc i 2 + 3 = c.endPc i := by
  by_cases h48 : i = 48
  · subst h48; unfold rungPc endPc; simp [q48R0, q48Done]
  · have e1 : i % 4 = 1 → c.dig (4 * (i / 4) + 1) = c.dig i := fun h => by rw [show 4 * (i / 4) + 1 = i by omega]
    have e2 : i % 4 = 2 → c.dig (4 * (i / 4) + 2) = c.dig i := fun h => by rw [show 4 * (i / 4) + 2 = i by omega]
    have e3 : i % 4 = 3 → c.dig (4 * (i / 4) + 3) = c.dig i := fun h => by rw [show 4 * (i / 4) + 3 = i by omega]
    unfold rungPc endPc qb qB qC qD qX qpcX qpcD qpcC qpcB partLen2
    simp only [if_neg h48]
    split_ifs <;> omega

/-- The step registers hold the steps. -/
theorem posE_eval (c : QCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (m : Nat) (hm : m ≤ 2) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)

theorem w0_low (i m : Nat) (hi : i ≤ 48) (hm : m < 256) :
    (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 ∧
      (BitVec.ofNat 64 (w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi hm)]
  unfold w0; constructor <;> omega

theorem w0_low0 (i : Nat) (hi : i ≤ 48) :
    (BitVec.ofNat 64 (w0 i)).toNat % 2 ^ 32 = 0x101 ∧ (BitVec.ofNat 64 (w0 i)).toNat / 2 ^ 40 = i := by
  have := w0_low i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace QCtx

/-- **The HASH of step `m` of chain `i`.** -/
theorem prehash_step (c : QCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i ≤ 48) (hm : m ≤ 2) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < 2 → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = 2 → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have hs := slotT_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 2 then slotT i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        by rw [getReg_writeHash]; exact h25, ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slotT_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slotT i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc i hi
        have hlo := hc.2.2.2.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen],
        by rw [getReg_writeHash]; exact h25, ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slotT_props j (by omega)
          have hmono : slotT j + 16 ≤ slotT i := by unfold slotT; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < 3 := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1

/-- **One rung**: `sb POS_m, 20(a0)` (and `li a2, slot` for the last step), up to the `ecall`. -/
theorem rung_piece (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 48) (hm : m ≤ 2) (hp : p < 209920)
    (hrun : vrun p 3 = some (rungR m (if m = 2 then some (slotT i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = 2 then 2 else 1) (if m = 2 then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 2 → t.getReg .x12 = BitVec.ofNat 64 (slotT i)) ∧ (m < 2 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 2 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungR m (if m = 2 then some (slotT i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 20⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (20 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp s hpc hobl
  have hec := piece_ecall hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = 2 then 2 else 1) ∧ r.cycles = (if m = 2 then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = 2 then some (slotT i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 4 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ 2 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = 2 <;> simp [h2, E.eval]

/-- **A rung after a step's hash.** -/
theorem rung_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i ≤ 48) (hm : m ≤ 2) (hp : c.rungPc i m < 209920)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = 2 then some (slotT i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = 2 then 2 else 1) (if m = 2 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slotT_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h2 : m = 2
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12, if_neg h2]
  · rw [hpc']

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace QCtx

theorem kAt_eval (c : QCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i ≤ 48) (k : Nat) (hk : k ≤ 80) : (kAt .x19 (offT i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk

theorem lAt_eval (c : QCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i ≤ 48) (k : Nat) (hk : k ≤ 80) :
    (lAt .x19 (offT i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]

/-- `s9` of a head or copy in a table slot: `mv s9, s11` (chain 0) or the bump. -/
theorem s9v (c : QCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i : Nat) (hi : i ≤ 48) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (h25 : i ≠ 0 → s.getReg .x25 = BitVec.ofNat 64 (w0 (i - 1))) :
    (s9E first).eval s = BitVec.ofNat 64 (w0 i) := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  cases first
  · simp only [s9E, bumpE, Bool.false_eq_true, if_false, E.eval, BinOp.eval]
    have hne := hfirst' rfl
    rw [h25 hne, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  · obtain rfl := hfirst rfl
    simp only [s9E, if_true, E.eval]
    rw [kr .x27 (BitVec.ofNat 64 0x101) (by simp [known]) (by decide)]
    rfl

/-- **The head of a table-slot chain** (`A = 4q`, or chain 48 in `q48tab`) with its first rung. -/
theorem headJ_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48) (hd : c.dig i < 3) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 209920) (hp1 : c.rungPc i (c.dig i) < 209920)
    (hrun1 : vrun (c.startPc i) 7 = some (headJ .x19 (offT i) first (c.rungPc i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i)) 3 =
      some (rungR (c.dig i) (if c.dig i = 2 then some (slotT i) else none) (c.rungPc i (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (6 + (if c.dig i = 2 then 2 else 1)) (6 + (if c.dig i = 2 then 2 else 1)) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headJ .x19 (offT i) first (c.rungPc i (c.dig i)) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJ, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show accessValid ((kAt .x19 (offT i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (offT i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJ_keeps .x19 (offT i) first (c.rungPc i (c.dig i))
  have a0e : (addC (E.reg .x19) (offT i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  have s9 := c.s9v hk hR i hi first hfirst hfirst' h25
  have t25 : t1.getReg .x25 = BitVec.ofNat 64 (w0 i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_self _ _ (by decide), s9]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJ]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), s9]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hH : c.HdrOk i t1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).1
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).2
    · rw [tmem _ (by omega), if_pos rfl]
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i)) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, h12b, h16, hfr2, hpc2⟩ :=
    c.rung_piece hc hk i (c.dig i) (c.rungPc i (c.dig i)) hi (by omega) hp1 hrun2 t1 hpc1 hR1 t10 hH
  have hsteps : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, hst1.trans hst2, ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · right; left; omega
  · have hsj := slotT_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t25
  · rw [hfr2 _ (by omega) (by omega), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t10
  · by_cases h2 : c.dig i = 2
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), t12, if_neg h2]
  · rw [hpc2]

theorem copy_mem (c : QCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i ≤ 48) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x19 (offT i) (slotT i)) (BitVec.ofNat 64 A) =
      if A = slotT i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotT i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slotT_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slotT i + 8) (slotT i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi 56 (by omega), c.lAt_eval hc h19 i hi 48 (by omega)]

theorem copy_obl (c : QCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i ≤ 48) : ∀ o ∈ copyObl .x19 (offT i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x19 (offT i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x19 (offT i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)

theorem copy_post (c : QCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i ≤ 48) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slotT j) (acc.getD j 0))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x19 (offT i) (slotT i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slotT j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slotT_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slotT i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotT i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 i hi A hA)
  have hfr : Frame s t (fun A => A = slotT i + 8 ∨ A = slotT i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slotT_props j (by omega)
      have hmono : slotT j + 16 ≤ slotT i := by unfold slotT; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2

/-- **The max-digit copy of a table-slot chain** (`A = 4q`, chain 48). -/
theorem copyJ_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 209920)
    (hrun : vrun (c.startPc i) 7 = some (copyJ .x19 (offT i) (slotT i) first (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyJ .x19 (offT i) (slotT i) first (c.endPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyJ] using c.copy_obl hc h19 i hi)
  have hkeep := copyJ_keeps .x19 (offT i) (slotT i) first (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  have s9 := c.s9v hk hR i hi first hfirst hfirst' h25
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_, ?_⟩⟩
  · rw [Result.toState_getReg]; simp only [hr, copyJ]
    rw [RegFile.get_set_self _ _ (by decide), s9]
  · rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`, `D`). -/
theorem copyF_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48) (hi0 : i ≠ 0) (hp0 : c.startPc i < 209920)
    (hend : c.startPc i + 5 = c.endPc i)
    (hrun : vrun (c.startPc i) 5 = some (copyF .x19 (offT i) (slotT i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyF .x19 (offT i) (slotT i) (c.startPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyF] using c.copy_obl hc h19 i hi)
  have hkeep := copyF_keeps .x19 (offT i) (slotT i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_, ?_⟩⟩
  · rw [Result.toState_getReg]; simp only [hr, copyF]
    rw [RegFile.get_set_self _ _ (by decide)]
    simp only [bumpE, E.eval, BinOp.eval]
    rw [h25 hi0, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  · rw [Result.toState_pc]; simp only [hr, copyF, E.eval]; rw [hend]

/-- **The head of an inline chain** (`B`, `C`, `D`) with its first rung. -/
theorem headR_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i ≤ 48) (hi0 : i ≠ 0) (hd : c.dig i < 3)
    (hp0 : c.startPc i < 209920) (hrp : c.rungPc i (c.dig i) = c.startPc i + 5)
    (hrun : vrun (c.startPc i) 8 =
      some (headR .x19 (offT i) (c.dig i) (if c.dig i = 2 then some (slotT i) else none) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (if c.dig i = 2 then 7 else 6) (if c.dig i = 2 then 7 else 6) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hs := slotT_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headR .x19 (offT i) (c.dig i) (if c.dig i = 2 then some (slotT i) else none) (c.startPc i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl | rfl)
    · show ((E.reg .x19).eval s).toNat % 8 = 0
      simp only [E.eval, h19, BitVec.toNat_ofNat]; have := hc.2.2.1; omega
    · show accessValid ((kAt .x19 (offT i) 20).eval s) 1 = true
      rw [keyE 20 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (offT i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (offT i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps hrun hp0 s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headR])
  have hn : r.steps = (if c.dig i = 2 then 7 else 6) ∧ r.cycles = (if c.dig i = 2 then 7 else 6) := by
    simp only [hr, headR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := headR_keeps .x19 (offT i) (c.dig i) (if c.dig i = 2 then some (slotT i) else none) (c.startPc i)
  have a0e : (addC (E.reg .x19) (offT i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have bumpv : bumpE.eval s = BitVec.ofNat 64 (w0 i) := by
    simp only [bumpE, E.eval, BinOp.eval]
    rw [h25 hi0, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headR]
    rw [memEval_two s _ _ _ _ (c.blk i + 16) (c.blk i + 24) A (keyE 16 (by omega)) (keyE 24 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval, BinOp.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), bumpv, c.posE_eval hk hR _ (by omega)]
    split
    · obtain ⟨hl, hj⟩ := w0_low0 i hi
      rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
      congr 1; unfold w0; ring
    · rfl
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotT_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_self _ _ (by decide), bumpv]
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h2 : c.dig i = 2
    · simp only [h2, if_true, E.eval]
    · simp only [h2, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [Result.toState_pc]; simp only [hr, headR, hrp]
    by_cases h2 : c.dig i = 2 <;> simp [h2, E.eval]

/-- `A` and `B`, `C` of a quad fall through to the next chain's code. -/
theorem next_inline (c : QCtx) (s0 : MachineState) (i : Nat) (hi : i < 48) (h3 : i % 4 ≠ 3)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) : c.ChainIn s0 (i + 1) acc s := by
  obtain ⟨hB, hlen, h25, hpc⟩ := hs
  refine ⟨hB, hlen, fun _ => by rw [h25]; rfl, ?_⟩
  rw [hpc]
  simp only [endPc, startPc, show i ≠ 48 by omega, show i + 1 ≠ 48 by omega, if_false]
  have e : (i + 1) / 4 = i / 4 := by omega
  by_cases h0 : i % 4 = 0
  · rw [if_pos h0, if_neg (show (i + 1) % 4 ≠ 0 by omega), if_pos (show (i + 1) % 4 = 1 by omega)]
    unfold qB; rw [e]
  · by_cases h1 : i % 4 = 1
    · rw [if_neg h0, if_pos h1, if_neg (show (i + 1) % 4 ≠ 0 by omega), if_neg (show (i + 1) % 4 ≠ 1 by omega),
        if_pos (show (i + 1) % 4 = 2 by omega)]
      unfold qC; rw [e]
    · rw [if_neg h0, if_neg h1, if_pos (show i % 4 = 2 by omega), if_neg (show (i + 1) % 4 ≠ 0 by omega),
        if_neg (show (i + 1) % 4 ≠ 1 by omega), if_neg (show (i + 1) % 4 ≠ 2 by omega)]
      unfold qD; rw [e]

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace QCtx

/-- The bit position of quad `q`'s digits in its digit word. -/
def qpos (q : Nat) : Nat := if q < 8 then 8 * q else 2 + 8 * (q - 8)

theorem dig4_shift (X b m : Nat) : X / 2 ^ (b + 2 * m) % 4 = X / 2 ^ b / 4 ^ m % 4 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add, show (4 : Nat) ^ m = 2 ^ (2 * m) by
    rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]]

theorem dig_q (c : QCtx) (q m : Nat) (hq : q < 12) (hm : m < 4) :
    c.dig (4 * q + m) = (if q < 8 then c.d0 else c.d1).toNat / 2 ^ (qpos q) / 4 ^ m % 4 := by
  unfold dig qpos
  by_cases h8 : q < 8
  · simp only [h8, if_true, show 4 * q + m < 32 by omega]
    rw [← dig4_shift, show (4 : Nat) ^ (4 * q + m) = 2 ^ (8 * q + 2 * m) by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]; congr 1; ring]
  · simp only [h8, if_false, show ¬ 4 * q + m < 32 by omega]
    rw [← dig4_shift, show (4 : Nat) ^ (4 * q + m - 31) = 2 ^ (2 + 8 * (q - 8) + 2 * m) by
      rw [show (4 : Nat) = 2 ^ 2 by rfl, ← Nat.pow_mul]; congr 1; omega]

/-- The table row of quad `q` from its digit word. -/
theorem kOf_eq (c : QCtx) (q : Nat) (hq : q < 12) :
    c.kOf q = (if q < 8 then c.d0 else c.d1).toNat / 2 ^ (qpos q) % 256 := by
  unfold kOf
  rw [show 4 * q = 4 * q + 0 by rfl, c.dig_q q 0 hq (by omega), c.dig_q q 1 hq (by omega), c.dig_q q 2 hq (by omega),
    c.dig_q q 3 hq (by omega)]
  generalize (if q < 8 then c.d0 else c.d1).toNat / 2 ^ (qpos q) = Y
  norm_num
  omega

theorem kOf_lt (c : QCtx) (q : Nat) (hq : q < 12) : c.kOf q < 256 := by
  rw [c.kOf_eq q hq]; exact Nat.mod_lt _ (by norm_num)

theorem kOf_digits (c : QCtx) (q : Nat) :
    c.kOf q % 4 = c.dig (4 * q) ∧ c.kOf q / 4 % 4 = c.dig (4 * q + 1) ∧ c.kOf q / 16 % 4 = c.dig (4 * q + 2) ∧
      c.kOf q / 64 = c.dig (4 * q + 3) := by
  unfold kOf
  have h0 := c.dig_lt4 (4 * q); have h1 := c.dig_lt4 (4 * q + 1)
  have h2 := c.dig_lt4 (4 * q + 2); have h3 := c.dig_lt4 (4 * q + 3)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **The dispatch after a quad's `D`** (`q < 11`): `jalr` into slot `q + 1` of `qtab` row `kOf (q + 1)`. -/
theorem x_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (q : Nat) (hq : q < 11) (hp : c.qX (4 * q + 3) < 209920)
    (hrun : vrun (c.qX (4 * q + 3)) 5 = some (xJ (if q + 1 < 8 then .x16 else .x17)
      (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) .x24
      (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632)))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (4 * q + 3) acc s) :
    ∃ u, Steps vimage s 4 4 u ∧ c.ChainIn s0 (4 * q + 4) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.qX (4 * q + 3)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hb9 : (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) ≠ 9 := by
    split <;> omega
  set r := xJ (if q + 1 < 8 then .x16 else .x17) (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) .x24
    (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xJ, hb9])
  have hsc : r.steps = 4 ∧ r.cycles = 4 := by
    refine ⟨?_, ?_⟩ <;> first
      | exact if_neg hb9
      | (simp only [hr, xJ]; exact if_neg hb9)
      | simp [hr, xJ, hb9]
  rw [hsc.1, hsc.2] at hst
  have hkeep := xJ_keeps (if q + 1 < 8 then .x16 else .x17) (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8))
    .x24 (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632)
  have hW : s.getReg (if q + 1 < 8 then .x16 else .x17) = (if q + 1 < 8 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide)
    · exact kr .x17 c.d1 (by simp [known]) (by decide)
  have h24 : s.getReg .x24 = BitVec.ofNat 64 (512 * (2 ^ 8 - 1)) := kr .x24 0x1fe00 (by simp [known]) (by decide)
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0xae000 := kr .x15 0xae000 (by simp [known]) (by decide)
  have hb : (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) = qpos (q + 1) := by unfold qpos; rfl
  have hm := shE_mask s _ _ hW (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8)) 8 (by split <;> omega)
    (by omega)
  have hk1 := c.kOf_lt (q + 1) (by omega)
  have hrow : ((if q + 1 < 8 then c.d0 else c.d1).toNat / 2 ^ (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8))
      % 2 ^ 8) = c.kOf (q + 1) := by
    rw [c.kOf_eq (q + 1) (by omega), hb]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, fun _ => ?_, ?_⟩⟩
  · rw [hkeep.reg s (by decide), h25, show 4 * q + 4 - 1 = 4 * q + 3 by omega]
  · rw [Result.toState_pc]
    simp only [hr, xJ, E.eval, BinOp.eval]
    rw [h24, h15]
    have e : ((shE (if q + 1 < 8 then Reg.x16 else Reg.x17) (if q + 1 < 8 then 8 * (q + 1) else 2 + 8 * (q + 1 - 8))).eval s &&&
        BitVec.ofNat 64 (512 * (2 ^ 8 - 1))) = BitVec.ofNat 64 (512 * c.kOf (q + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [hm, hrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have e2 : BitVec.ofNat 64 (512 * c.kOf (q + 1)) + BitVec.ofNat 64 0xae000 +
        (BitVec.ofNat 64 (32 * (q + 1)) - BitVec.ofNat 64 1632) =
        BitVec.ofNat 64 (0x1000 + 4 * qentW (q + 1) (c.kOf (q + 1))) := by
      rw [tab_target _ _ _ _ (by omega) (by omega)]
      congr 1
      unfold qentW qtabIdx; omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc
    rw [if_neg (by omega), if_pos (by omega), show (4 * q + 4) / 4 = q + 1 by omega]

theorem land96 (n : Nat) : n &&& 96 = 32 * (n / 32 % 4) := by

  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (96 : Nat) = 2 ^ 5 * 3 by norm_num, show (32 : Nat) = 2 ^ 5 by norm_num,
    Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow (n / 2 ^ 5) 2, Nat.testBit_div_two_pow]
  by_cases h5 : 5 ≤ j
  · simp only [h5, decide_true, Bool.true_and, show j - 5 + 5 = j by omega]
    by_cases hj : j - 5 < 2
    · have : Nat.testBit 3 (j - 5) = true := by interval_cases (j - 5) <;> decide
      simp [hj, this]
    · have : Nat.testBit 3 (j - 5) = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le (show 3 < 2 ^ 2 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hj, this]
  · simp [h5]

theorem q48_field (W : Word) : (((W >>> ((29 : Word).toNat % 64)) &&& (0x60 : Word))).toNat =
    32 * (W.toNat / 2 ^ 34 % 4) := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, show (29 : Word).toNat % 64 = 29 from rfl,
    show (0x60 : Word).toNat = 96 by rfl, Nat.shiftRight_eq_div_pow, land96, Nat.div_div_eq_div_mul,
    show (2 : Nat) ^ 29 * 32 = 2 ^ 34 by norm_num]

/-- **After quad 11's `D`**: the dispatch into `q48tab[d48]`. -/
theorem x11_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hp : c.qX 47 < 209920) (hrun : vrun (c.qX 47) 5 = some q48X)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 47 acc s) :
    ∃ u, Steps vimage s 4 4 u ∧ c.ChainIn s0 48 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.qX 47) := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun hp s hpc' (by simp [q48X])
  have hkeep : Keeps q48X [.x14] := by
    intro x hx; simp only [q48X]; rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0xae000 := kr .x15 0xae000 (by simp [known]) (by decide)
  have h17 : s.getReg .x17 = c.d1 := kr .x17 c.d1 (by simp [known]) (by decide)
  refine ⟨q48X.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, fun _ => ?_, ?_⟩⟩
  · rw [hkeep.reg s (by decide), h25]
  · rw [Result.toState_pc]
    simp only [q48X, E.eval, BinOp.eval, h15, h17]
    have e : (c.d1 >>> ((29 : Word).toNat % 64) &&& (0x60 : Word)) = BitVec.ofNat 64 (32 * c.dig 48) := by
      apply BitVec.eq_of_toNat_eq
      rw [q48_field, BitVec.toNat_ofNat]
      have : c.dig 48 = c.d1.toNat / 2 ^ 34 % 4 := by
        unfold dig; simp only [show ¬ 48 < 32 by omega, if_false]
        rw [show (4 : Nat) ^ (48 - 31) = 2 ^ 34 by norm_num]
      rw [this]
      have : c.d1.toNat / 2 ^ 34 % 4 < 4 := Nat.mod_lt _ (by norm_num)
      omega
    rw [e, show (-1760 : Word) = BitVec.ofNat 64 0 - BitVec.ofNat 64 1760 from rfl]
    have e2 : BitVec.ofNat 64 (32 * c.dig 48) + BitVec.ofNat 64 0xae000 + (BitVec.ofNat 64 0 - BitVec.ofNat 64 1760) =
        BitVec.ofNat 64 (0x1000 + 4 * (q48tabIdx + 8 * c.dig 48)) := by
      have := c.dig_lt4 48
      rw [tab_target _ _ _ _ (by omega) (by omega)]
      congr 1; unfold q48tabIdx; omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp

end QCtx

end SigGolfCandidate.T3M

namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3

namespace QCtx

/-- The lower-code run of the top's chains `49 .. 57` (code chains `33 .. 41`, no checksum chain). -/
def lctx (c : QCtx) : LCtx := ⟨c.w, 0, 33, 16, c.tree, c.leaf, c.S6, c.d0, c.d1, 8, c.ret⟩

theorem lctx_w0 (c : QCtx) (i : Nat) : c.lctx.w0 i = w0 (i + 16) := by
  unfold LCtx.w0 w0 lctx; simp

/-- **`q48_done`**: `lui a5, ttab window`, the dispatch of the lower triple 11 (`kOf 11 = a7 >> 36`), into the
lower code's `ChainIn 33` with a fresh base state. -/
theorem q48d_step (c : QCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hrun : vrun q48Done 6 = some q48D) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 48 acc s) :
    ∃ u, Steps vimage s 5 5 u ∧ c.lctx.ChainIn u 33 [] u ∧ (∀ x, x ≠ .x14 → x ≠ .x15 → u.getReg x = s.getReg x) ∧
      u.getReg .x15 = BitVec.ofNat 64 0x6e000 ∧ (∀ A, u.getMem A = s.getMem A) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf q48Done := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun (by decide) s hpc' (by simp [q48D])
  have h2 : s.getReg .x2 = BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) := kr .x2 0x3fe00 (by simp [known]) (by decide)
  have h17 : s.getReg .x17 = c.d1 := kr .x17 c.d1 (by simp [known]) (by decide)
  have hregs : ∀ x, x ≠ .x14 → x ≠ .x15 → (q48D.toState s).getReg x = s.getReg x := by
    intro x h14 h15
    rw [Result.toState_getReg]; simp only [q48D]
    rw [RegFile.get_set_ne _ _ h14, RegFile.get_set_ne _ _ h15, RegFile.init_get_eval]
  have hm := shE_mask s .x17 c.d1 h17 36 9 (by omega) (le_refl _)
  have hk11 := c.lctx.kOf_lt 11 (by omega)
  have hrow : c.d1.toNat / 2 ^ 36 % 2 ^ 9 = c.lctx.kOf 11 := by
    rw [c.lctx.kOf_eq 11 (by omega)]; rfl
  refine ⟨q48D.toState s, hst, ⟨⟨fun _ _ => rfl, Frame.refl _ _, fun j hj => by simp at hj⟩, rfl, fun _ => ?_, ?_⟩,
    hregs, ?_, fun A => rfl⟩
  · rw [hregs _ (by decide) (by decide), h25, lctx_w0]
  · rw [Result.toState_pc]
    simp only [q48D, E.eval, BinOp.eval]
    rw [h2]
    have e : (BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) &&& (s.getReg .x17 >>> ((27 : Word).toNat % 64))) =
        BitVec.ofNat 64 (512 * c.lctx.kOf 11) := by
      rw [BitVec.and_comm]
      apply BitVec.eq_of_toNat_eq
      have := hm
      simp only [shE, show ¬ 36 < 9 by omega, show 9 < 36 by omega, if_false, if_true, E.eval, BinOp.eval] at this
      rw [show (BitVec.ofNat 64 (36 - 9)).toNat % 64 = (27 : Word).toNat % 64 from rfl] at this
      rw [this, hrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [show (s.getReg .x17 >>> ((27 : Word).toNat % 64) &&& BitVec.ofNat 64 (512 * (2 ^ 9 - 1))) =
      (BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) &&& (s.getReg .x17 >>> ((27 : Word).toNat % 64))) from BitVec.and_comm _ _,
      e]
    have e2 : BitVec.ofNat 64 (512 * c.lctx.kOf 11) + ((0x6e000 : Word) - 1408) =
        BitVec.ofNat 64 (0x1000 + 4 * entW 11 (c.lctx.kOf 11)) := by
      rw [show ((0x6e000 : Word) - 1408) = BitVec.ofNat 64 449152 by decide, ofNat_add_ofNat]
      apply congrArg
      unfold entW ttabIdx
      omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold LCtx.startPc; simp [lctx]
  · rw [Result.toState_getReg]; simp only [q48D]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]; rfl

/-- The lower code's known registers after `q48_done`. -/
theorem lctx_known (c : QCtx) {s0 u : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hu : ∀ x, x ∉ chainRegs → x ≠ .x14 → x ≠ .x15 → u.getReg x = s0.getReg x)
    (h15 : u.getReg .x15 = BitVec.ofNat 64 0x6e000) :
    ∀ p ∈ c.lctx.known, u.getReg p.1 = p.2 := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → r ≠ .x14 → r ≠ .x15 → u.getReg r = v :=
    fun r v hm hn h14 h15 => (hu r hn h14 h15).trans (hk _ hm)
  intro p hp
  simp only [LCtx.known, lctx, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only
  all_goals first
    | exact h15
    | (rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide) (by decide) (by decide)]; rfl)
    | (rw [kr .x27 (BitVec.ofNat 64 0x101) (by simp [known]) (by decide) (by decide) (by decide)]; rfl)
    | exact kr _ _ (by simp [known]) (by decide) (by decide) (by decide)

end QCtx

end SigGolfCandidate.T3M
