import SigGolfCandidate.T3M.Verify.ChainRuns
import SigGolfCandidate.T3M.Witness.VerifyP
import SigGolfCandidate.T3M.Verify.Mem

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
abbrev vimage : Image := Images.verifyImage
theorem piece_steps {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 209920) (s : MachineState)
    (hpc : s.pc = pcOf p) (ho : ∀ o ∈ r.st.obl, o.holds s) :
    Steps vimage s r.steps r.cycles (r.toState s) :=
  symRun_sound h (lcodeAt p (by omega)) s hpc ((Oblig.all_iff _ _).mpr ho)
theorem piece_ecall {p f : Nat} {r : Result} (h : vrun p f = some r) (hp : p < 209920) (s : MachineState)
    (ho : ∀ o ∈ r.st.obl, o.holds s) (hst : r.stop = .ecall) :
    fetch vimage (r.toState s) = some (.base .ECALL) :=
  symRun_ecall h (lcodeAt p (by omega)) s ((Oblig.all_iff _ _).mpr ho) hst
theorem ofNat_add_off (x a b k : Nat) (h : b ≤ x + a) (h2 : x + a + k < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b + BitVec.ofNat 64 k) =
      BitVec.ofNat 64 (x + a - b + k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off0 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) = BitVec.ofNat 64 (x + a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem ofNat_add_off48 (x a b : Nat) (h : b ≤ x + a) (h2 : x + a + 48 < 2 ^ 64) :
    BitVec.ofNat 64 x + (BitVec.ofNat 64 a - BitVec.ofNat 64 b) + 48 = BitVec.ofNat 64 (x + a - b + 48) := by
  rw [ofNat_add_off0 x a b h (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (48 : Word).toNat = 48 from rfl]
  omega
theorem valid_ofNat (A w : Nat) (hA : A + w ≤ 2 ^ 24) (ha : A % w = 0) :
    accessValid (BitVec.ofNat 64 A) w = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by simp only [MEMORY_BYTES]; omega, ha⟩
def OrigW (w : WBytes) (s : MachineState) (A : Nat) : Prop :=
  s.getMem (BitVec.ofNat 64 A) = w.extractLsb' (8 * (A - 0x800)) 64
theorem wdig_lo (w : WBytes) (off : Nat) : (wdig w off).extractLsb' 0 64 = w.extractLsb' (8 * off) 64 := by
  unfold wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd _ (by norm_num)]
theorem wdig_hi (w : WBytes) (off : Nat) :
    (wdig w off).extractLsb' 64 64 = w.extractLsb' (8 * (off + 8)) 64 := by
  unfold wdig
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (off + 8) = 8 * off + 64 by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize w.toNat / 2 ^ (8 * off) = X
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self, Nat.mod_mod]
theorem DigAt_origW {w : WBytes} {s : MachineState} {A : Nat} (h0 : OrigW w s A) (h1 : OrigW w s (A + 8))
    (hA : 0x800 ≤ A) : DigAt s A (wdig w (A - 0x800)) := by
  refine ⟨?_, ?_⟩
  · rw [h0, wdig_lo]
  · rw [h1, wdig_hi, show A + 8 - 0x800 = A - 0x800 + 8 by omega]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
def chainRegs : List Reg := [.x10, .x12, .x25, .x3, .x14]
def Keeps (r : Result) (ws : List Reg) : Prop := ∀ x, x ∉ ws → r.st.regs.get x = RegFile.init.get x
theorem Keeps.reg {r : Result} {ws : List Reg} (h : Keeps r ws) (s : MachineState) {x : Reg} (hx : x ∉ ws) :
    (r.toState s).getReg x = s.getReg x := by
  rw [Result.toState_getReg, h x hx, RegFile.init_get_eval]
theorem ne_of_not_mem {x r : Reg} {ws : List Reg} (hx : x ∉ ws) (hr : r ∈ ws) : x ≠ r := by
  rintro rfl; exact hx hr
theorem headJ_keeps (rb : Reg) (off : Word) (first : Bool) (tgt : Nat) :
    Keeps (headJ rb off first tgt) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headR_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p : Nat) :
    Keeps (headR rb off d slot p) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headR]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem rungR_keeps (d : Nat) (slot : Option Nat) (p : Nat) : Keeps (rungR d slot p) [.x12] := by
  intro x hx
  simp only [rungR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl
theorem copyJ_keeps (rb : Reg) (off : Word) (slot : Nat) (first : Bool) (tgt : Nat) :
    Keeps (copyJ rb off slot first tgt) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyJ, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyF_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyF rb off slot p) [.x3, .x14, .x25] := by
  intro x hx
  simp only [copyF, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyN_keeps (rb : Reg) (off : Word) (slot tgt : Nat) : Keeps (copyN rb off slot tgt) [.x3, .x14] := by
  intro x hx
  simp only [copyN, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headJH_keeps (rb : Reg) (off : Word) (tgt i d : Nat) (slot : Option Nat) :
    Keeps (headJH rb off tgt i d slot) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem headRH_keeps (rb : Reg) (off : Word) (d : Nat) (slot : Option Nat) (p i : Nat) :
    Keeps (headRH rb off d slot p i) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headRH]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem copyFH_keeps (rb : Reg) (off : Word) (slot p : Nat) : Keeps (copyFH rb off slot p) [.x3, .x14] := by
  intro x hx
  simp only [copyFH, copyRegs]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem xJ_keeps (w : Reg) (b : Nat) (mreg : Reg) (imm : Word) : Keeps (xJ w b mreg imm) [.x14] := by
  intro x hx
  simp only [xJ]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem ctabX_keeps : Keeps ctabX [.x14] := by
  intro x hx
  simp only [ctabX]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
theorem retR_keeps : Keeps retR [] := fun _ _ => rfl
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
structure LCtx where
  w : WBytes
  lay : Layer
  i0 : Nat
  koff : Nat
  tree : Nat
  leaf : Nat
  S6 : Nat
  d0 : Word
  d1 : Word
  ck : Nat
  ret : Nat
namespace LCtx
def blk (c : LCtx) (i : Nat) : Nat := c.S6 - 1024 + 64 * (42 - i)
def dig (c : LCtx) (i : Nat) : Nat :=
  if i < 21 then c.d0.toNat / 8 ^ i % 8 else if i < 42 then c.d1.toNat / 8 ^ (i - 21) % 8 else c.ck
def w0 (c : LCtx) (i : Nat) : Nat := 0x101 + 65536 * c.lay.val + 2 ^ 40 * (i + c.koff)
def w1 (c : LCtx) : Nat := hdr1 c.tree c.leaf
def pad0 (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800)
def pad1 (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 32)
def val (c : LCtx) (i : Nat) : Digest := wdig c.w (c.blk i - 0x800 + 48)
def ok (c : LCtx) : Prop :=
  c.tree < 2 ^ 32 ∧ c.leaf < 2 ^ 32 ∧ c.koff ≤ 16 ∧ c.S6 % 8 = 0 ∧ 0x800 + 11288 + 1024 ≤ c.S6 ∧
    c.S6 + 2688 + 80 ≤ 0x7000 ∧ c.ck ≤ 8 ∧ c.ret < 209920 ∧ c.i0 ≤ 42
def known (c : LCtx) : List (Reg × Word) :=
  [(.x5, 0), (.x11, 64), (.x6, 1), (.x7, 2), (.x8, 3), (.x9, 4), (.x13, 5), (.x26, 6),
   (.x28, BitVec.ofNat 64 (Verify.headerBank c.lay.val c.koff)), (.x2, 0x3fe00), (.x15, 0x6e000),
   (.x22, BitVec.ofNat 64 c.S6),
   (.x4, BitVec.ofNat 64 c.w1), (.x27, BitVec.ofNat 64 (0x401 + 65536 * c.lay.val)),
   (.x16, c.d0), (.x17, c.d1), (.x29, 7#64 - BitVec.ofNat 64 c.ck), (.x1, pcOf c.ret)]
def kOf (c : LCtx) (t : Nat) : Nat := c.dig (3 * t) + 8 * c.dig (3 * t + 1) + 64 * c.dig (3 * t + 2)
def tb (c : LCtx) (i : Nat) : Nat := triBase (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tB (c : LCtx) (i : Nat) : Nat := pcB (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tC (c : LCtx) (i : Nat) : Nat := pcC (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def tX (c : LCtx) (i : Nat) : Nat := pcX (i / 3) (c.dig (3 * (i / 3) + 1)) (c.dig (3 * (i / 3) + 2))
def startPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ctabIdx + 8 * c.ck
  else if i % 3 = 0 then entW (i / 3) (c.kOf (i / 3)) else if i % 3 = 1 then c.tB i else c.tC i
def rungPc (c : LCtx) (i m : Nat) : Nat :=
  if i = 42 then ckR0 + 2 * m
  else if i % 3 = 0 then c.tb i + 2 * m
  else (if i % 3 = 1 then c.tB i else c.tC i) + 4 + 2 * (m - c.dig i)
def endPc (c : LCtx) (i : Nat) : Nat :=
  if i = 42 then ckDone else if i % 3 = 0 then c.tB i else if i % 3 = 1 then c.tC i else c.tX i
def Wr (c : LCtx) (i : Nat) (A : Nat) : Prop :=
  (slotL c.i0 ≤ A ∧ A < 0x5D0) ∨ (c.S6 - 1024 + 64 * (43 - i) ≤ A ∧ A < c.blk c.i0 + 80)
def WrIn (c : LCtx) (i : Nat) (A : Nat) : Prop :=
  c.Wr i A ∨ (c.blk i + 16 ≤ A ∧ A < c.blk i + 32) ∨ (c.blk i + 48 ≤ A ∧ A < c.blk i + 80)
def Orig0 (c : LCtx) (s0 : MachineState) : Prop :=
  ∀ i, c.i0 ≤ i → i ≤ 42 → ∀ k < 8, OrigW c.w s0 (c.blk i + 8 * k)
def Base (c : LCtx) (s0 : MachineState) (W : Nat → Prop) (acc : List Digest) (s : MachineState) : Prop :=
  (∀ x, x ∉ chainRegs → s.getReg x = s0.getReg x) ∧ Frame s0 s W ∧
    (∀ j < acc.length, DigAt s (slotL (c.i0 + j)) (acc.getD j 0))
def ChainIn (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    s.pc = pcOf (c.startPc i)
def HdrOk (c : LCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
    (s.getMem (BitVec.ofNat 64 (c.blk i + 16))).toNat / 2 ^ 40 = i + c.koff ∧
    s.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1
def StepInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (s : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc s ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    c.HdrOk i s ∧ DigAt s (c.blk i + 48) v ∧ s.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    s.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) ∧ s.pc = pcOf (c.rungPc i m)
def PreHash (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (m : Nat) (v : Digest)
    (t : MachineState) : Prop :=
  c.Base s0 (c.WrIn i) acc t ∧ acc.length = i - c.i0 ∧ Verify.DataOK s0 ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m) ∧
    t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1 ∧ DigAt t (c.blk i + 48) v ∧
    t.getReg .x10 = BitVec.ofNat 64 (c.blk i) ∧
    t.getReg .x12 = BitVec.ofNat 64 (if m = 6 then slotL i else c.blk i + 48) ∧
    t.pc = pcOf (c.rungPc i m + (if m = 6 then 2 else 1)) ∧ fetch vimage t = some (.base .ECALL)
def EndInv (c : LCtx) (s0 : MachineState) (i : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr (i + 1)) acc s ∧ acc.length = i + 1 - c.i0 ∧
    Verify.DataOK s0 ∧ s.pc = pcOf (c.endPc i)
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem memEval_one (s : MachineState) (k : Addr) (v : E) (a A : Nat) (h : k.eval s = BitVec.ofNat 64 a)
    (ha : a < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k, v)] (BitVec.ofNat 64 A) = if A = a then v.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h, memEval_nil]
  by_cases e : A = a
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha).mp h')), if_neg e]
theorem memEval_two (s : MachineState) (k1 k2 : Addr) (v1 v2 : E) (a1 a2 A : Nat)
    (h1 : k1.eval s = BitVec.ofNat 64 a1) (h2 : k2.eval s = BitVec.ofNat 64 a2) (ha1 : a1 < 2 ^ 64)
    (ha2 : a2 < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(k1, v1), (k2, v2)] (BitVec.ofNat 64 A) =
      if A = a1 then v1.eval s else if A = a2 then v2.eval s else s.getMem (BitVec.ofNat 64 A) := by
  rw [memEval_cons, h1, memEval_one s k2 v2 a2 A h2 ha2 hA]
  by_cases e : A = a1
  · subst e; simp
  · rw [if_neg (fun h' => e ((ofNat_inj hA ha1).mp h')), if_neg e]
theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem stepByte (w : Word) (L J m : Nat) (hL : L < 2 ^ 32) (hm : m < 256) (hJ : J < 2 ^ 24)
    (h1 : w.toNat % 2 ^ 32 = L) (h2 : w.toNat / 2 ^ 40 = J) :
    StoreKind.merge .b w 4 (BitVec.ofNat 64 m) = BitVec.ofNat 64 (L + 2 ^ 32 * m + 2 ^ 40 * J) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show L + 2 ^ 32 * m + 2 ^ 40 * J < 2 ^ 64 by omega)]
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega
theorem wordsOf_chainInputP (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    wordsOf (chainInputP lay tree leaf i step p0 p1 v) =
      [p0.extractLsb' 0 64, p0.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 1 lay.val tree (step + 256 * i)),
        BitVec.ofNat 64 (hdr1 tree leaf), p1.extractLsb' 0 64, p1.extractLsb' 64 64, v.extractLsb' 0 64,
        v.extractLsb' 64 64] := by
  unfold chainInputP
  rw [wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp [SphincsSecurity.bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_header, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl
theorem chainInputP_length (lay : Layer) (tree leaf i step : Nat) (p0 p1 v : Digest) :
    (chainInputP lay tree leaf i step p0 p1 v).length = 64 * (0 + 1) := by
  simp [chainInputP, SphincsSecurity.bytesLE_length]
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem blk_props (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    c.blk i % 8 = 0 ∧ 0x800 + 11288 ≤ c.blk i ∧ c.blk i + 80 ≤ 0x7000 := by
  obtain ⟨-, -, -, h64, hlo, hhi, -⟩ := hc
  unfold blk; refine ⟨?_, ?_, ?_⟩ <;> omega
theorem blk_succ (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.blk (i + 1) + 64 = c.blk i := by
  obtain ⟨-, -, -, -, hlo, -⟩ := hc
  unfold blk; omega
theorem blk_le (c : LCtx) (hc : c.ok) (i j : Nat) (hij : i ≤ j) (hj : j ≤ 42) : c.blk j + 64 * (j - i) = c.blk i := by
  obtain ⟨-, -, -, -, hlo, -⟩ := hc
  unfold blk; omega
theorem slotL_mono (i j : Nat) (h : i ≤ j) : slotL i ≤ slotL j := by unfold slotL; split_ifs <;> omega
theorem slotL_props (i : Nat) (hi : i ≤ 42) : slotL i % 16 = 0 ∧ 768 ≤ slotL i ∧ slotL i + 32 ≤ 0x5D0 := by
  unfold slotL; split <;> omega
theorem base_off (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) :
    BitVec.ofNat 64 c.S6 + (offL i + BitVec.ofNat 64 k) = BitVec.ofNat 64 (c.blk i + k) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  unfold offL blk
  rw [ofNat_add_off _ _ _ _ (by omega) (by omega), show c.S6 + 64 * (42 - i) - 1024 = c.S6 - 1024 + 64 * (42 - i) by
    omega]
theorem base_off0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    BitVec.ofNat 64 c.S6 + offL i = BitVec.ofNat 64 (c.blk i) := by
  obtain ⟨-, -, -, -, hlo, hhi, -⟩ := hc
  unfold offL blk
  rw [ofNat_add_off0 _ _ _ (by omega) (by omega), show c.S6 + 64 * (42 - i) - 1024 = c.S6 - 1024 + 64 * (42 - i) by
    omega]
theorem known_get (c : LCtx) {s : MachineState} (h : ∀ p ∈ c.known, s.getReg p.1 = p.2) {r : Reg} {v : Word}
    (hm : (r, v) ∈ c.known) : s.getReg r = v := h _ hm
theorem w0_hdr0 (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    c.w0 i + 2 ^ 32 * m = hdr0 1 c.lay.val c.tree (m + 256 * (i + c.koff)) := by
  obtain ⟨htr, -, hk, -⟩ := hc
  have hl := c.lay.isLt
  rw [hdr0_eq _ _ _ _ (by norm_num) (by omega) htr (by omega)]
  unfold w0; ring
theorem w0_lt (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) : c.w0 i + 2 ^ 32 * m < 2 ^ 64 := by
  obtain ⟨-, -, hk, -⟩ := hc
  have hl := c.lay.isLt
  unfold w0; omega
theorem w1_lt (c : LCtx) : c.w1 < 2 ^ 64 := hdr1_lt _ _
theorem chain_hashInput (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) (v : Digest)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 (c.blk i))
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (hp0 : DigAt t (c.blk i) (c.pad0 i)) (hp1 : DigAt t (c.blk i + 32) (c.pad1 i))
    (h16 : t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m))
    (h24 : t.getMem (BitVec.ofNat 64 (c.blk i + 24)) = BitVec.ofNat 64 c.w1)
    (hv : DigAt t (c.blk i + 48) v) :
    hashInput t = toQ (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) := by
  obtain ⟨h64, hlo, hhi⟩ := c.blk_props hc i hi
  apply hashInput_toQ t _ 0 (c.blk i) (chainInputP_length _ _ _ _ _ _ _ _) h10 (by omega) (by omega) h11
    (by norm_num)
  rw [wordsOf_chainInputP, show 8 * (0 + 1) = 2 + (2 + (2 + 2)) from rfl, readWords_add, readWords_add,
    readWords_add, readWords_two, readWords_two, readWords_two, readWords_two, hp0.1, hp0.2,
    show c.blk i + 8 * 2 = c.blk i + 16 by ring, h16,
    show c.blk i + 16 + 8 = c.blk i + 24 by ring, h24,
    show c.blk i + 16 + 8 * 2 = c.blk i + 32 by ring, hp1.1, hp1.2,
    show c.blk i + 32 + 8 * 2 = c.blk i + 48 by ring, hv.1, hv.2, w0_hdr0 c hc i m hi hm]
  rfl
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem orig_frame {c : LCtx} {s0 t : MachineState} {W : Nat → Prop} (hF : Frame s0 t W) (h0 : c.Orig0 s0)
    (hc : c.ok) {i k : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42) (hk : k < 8) (hW : ¬ W (c.blk i + 8 * k)) :
    OrigW c.w t (c.blk i + 8 * k) := by
  have := (c.blk_props hc i hi.2)
  unfold OrigW
  rw [hF _ (by omega) hW]
  exact h0 i hi.1 hi.2 k hk
theorem pads_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat}
    (hi : c.i0 ≤ i ∧ i ≤ 42) (hF : Frame s0 t (c.WrIn i)) :
    DigAt t (c.blk i) (c.pad0 i) ∧ DigAt t (c.blk i + 32) (c.pad1 i) := by
  have hb := c.blk_props hc i hi.2
  have nW : ∀ k, k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 5 → ¬ c.WrIn i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
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
theorem rungPc_succ (c : LCtx) (i m : Nat) (hd : c.dig i ≤ m) : c.rungPc i (m + 1) = c.rungPc i m + 2 := by
  unfold rungPc; split_ifs <;> omega
theorem dig_lt (c : LCtx) (hc : c.ok) (i : Nat) (hi : i < 42) : c.dig i < 8 := by
  unfold dig; split_ifs <;> omega
theorem rungPc_end (c : LCtx) (i : Nat) (hi : i ≤ 42) (hd : c.dig i < 7) : c.rungPc i 6 + 3 = c.endPc i := by
  by_cases h42 : i = 42
  · subst h42; unfold rungPc endPc; simp [ckR0, ckDone]
  · have e1 : i % 3 = 1 → c.dig (3 * (i / 3) + 1) = c.dig i := fun h => by rw [show 3 * (i / 3) + 1 = i by omega]
    have e2 : i % 3 = 2 → c.dig (3 * (i / 3) + 2) = c.dig i := fun h => by rw [show 3 * (i / 3) + 2 = i by omega]
    unfold rungPc endPc tb tB tC tX pcX pcC pcB partLen
    simp only [if_neg h42]
    split_ifs <;> omega
theorem prehash_step (c : LCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP c.lay c.tree c.leaf (i + c.koff) m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < 6 → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = 6 → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = 6 then slotL i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi.2 (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm6 => ?_, fun hm6 => ?_⟩
    ·
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        h25, ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slotL_props (c.i0 + j) (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0; have := c.lay.isLt; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi.2 (by omega))]
        unfold w0; have := c.lay.isLt; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    ·
      subst hm6
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slotL i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc c.i0 i hi.1 hi.2
        have hlo := hc.2.2.2.2.1
        have hsm := slotL_mono c.i0 i hi.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen]; omega,
        h25, ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slotL_props (c.i0 + j) (by omega)
          have hmono : slotL (c.i0 + j) + 16 ≤ slotL i := by unfold slotL; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
            show c.i0 + acc.length = i by omega]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd7 : c.dig i < 7 := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi.2 hd7, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem posE_eval (c : LCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (m : Nat) (hm : m ≤ 6) :
    (posE m).eval s = BitVec.ofNat 64 m := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  interval_cases m
  · rfl
  · exact kr .x6 1 (by simp [known]) (by decide)
  · exact kr .x7 2 (by simp [known]) (by decide)
  · exact kr .x8 3 (by simp [known]) (by decide)
  · exact kr .x9 4 (by simp [known]) (by decide)
  · exact kr .x13 5 (by simp [known]) (by decide)
  · exact kr .x26 6 (by simp [known]) (by decide)
theorem w0_low (c : LCtx) (hc : c.ok) (i m : Nat) (hi : i ≤ 42) (hm : m < 256) :
    (BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
      (BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m)).toNat / 2 ^ 40 = i + c.koff := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (c.w0_lt hc i m hi hm)]
  have := c.lay.isLt
  unfold w0; constructor <;> omega
theorem rung_piece (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i ≤ 42) (hm : m ≤ 6) (hp : p < 209920)
    (hrun : vrun p 3 = some (rungR m (if m = 6 then some (slotL i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = 6 → t.getReg .x12 = BitVec.ofNat 64 (slotL i)) ∧ (m < 6 → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = 6 then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  set r := rungR m (if m = 6 then some (slotL i) else none) p with hr
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
  have hn : r.steps = (if m = 6 then 2 else 1) ∧ r.cycles = (if m = 6 then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = 6 then some (slotL i) else none) p
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
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h6 => ?_, fun h6 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h6]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ 6 by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    have := c.lay.isLt
    have hkoff := hc.2.2.1
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h6 : m = 6 <;> simp [h6, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem not_mem_sub {x : Reg} {ws : List Reg} (hx : x ∉ chainRegs) (h : ws ⊆ chainRegs) : x ∉ ws :=
  fun hm => hx (h hm)
theorem w0_low0 (c : LCtx) (hc : c.ok) (i : Nat) (hi : i ≤ 42) :
    (BitVec.ofNat 64 (c.w0 i)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay.val ∧
      (BitVec.ofNat 64 (c.w0 i)).toNat / 2 ^ 40 = i + c.koff := by
  have := c.w0_low hc i 0 hi (by omega)
  rwa [Nat.mul_zero, Nat.add_zero] at this
theorem rung_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hm : m ≤ 6) (hp : c.rungPc i m < 209920)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = 6 then some (slotL i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = 6 then 2 else 1) (if m = 6 then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi.2 hm hp hrun s hpc hR h10 hH
  have hs := slotL_props i hi.2
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h6 : m = 6
    · rw [h12a h6, if_pos h6]
    · rw [h12b (by omega), h12, if_neg h6]
  · rw [hpc']
theorem val_at {c : LCtx} {s0 t : MachineState} (hc : c.ok) (h0 : c.Orig0 s0) {i : Nat} (hi : c.i0 ≤ i ∧ i ≤ 42)
    (hF : Frame s0 t (c.Wr i)) : DigAt t (c.blk i + 48) (c.val i) := by
  have hb := c.blk_props hc i hi.2
  have nW : ∀ k, k = 6 ∨ k = 7 → ¬ c.Wr i (c.blk i + 8 * k) := by
    intro k hk hw
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
    unfold Wr blk at *
    omega
  have o6 := orig_frame hF h0 hc hi (k := 6) (by omega) (nW 6 (by omega))
  have o7 := orig_frame hF h0 hc hi (k := 7) (by omega) (nW 7 (by omega))
  rw [show c.blk i + 8 * 6 = c.blk i + 48 by ring] at o6
  rw [show c.blk i + 8 * 7 = c.blk i + 48 + 8 by ring] at o7
  have := DigAt_origW o6 o7 (by omega)
  rwa [show c.blk i + 48 - 0x800 = c.blk i - 0x800 + 48 by omega] at this
theorem Wr_mono (c : LCtx) (i : Nat) (A : Nat) (h : c.Wr i A) : c.WrIn i A := Or.inl h
theorem header_load (c : LCtx) (hc : c.ok) {s0 s : MachineState}
    (hD : Verify.DataOK s0) (i d : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : d < 8)
    (hF : Frame s0 s (c.Wr i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (Verify.headerBank c.lay.val c.koff)) :
    (Oblig.valid (hKey i d) 8).holds s ∧
      (hLoad i d).eval s = BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * d) := by
  have hl := c.lay.isLt
  have hko := hc.2.2.1
  have hib : i + c.koff < 64 := by omega
  have hb := c.blk_props hc c.i0 (by omega)
  let A := Verify.HDATA + 4096 * c.lay.val + 64 * (i + c.koff) + 8 * d
  have hA : 2 ^ 23 + 4096 ≤ A ∧ A + 8 ≤ 2 ^ 24 := by dsimp [A, Verify.HDATA]; omega
  have key : (hKey i d).eval s = BitVec.ofNat 64 A := by
    simp only [hKey, Addr.eval, E.eval, h28, hOff]
    change BitVec.ofNat 64 (Verify.headerBank c.lay.val c.koff) +
      (BitVec.ofNat 64 (64 * i + 8 * d) - BitVec.ofNat 64 2048) = BitVec.ofNat 64 A
    rw [ofNat_add_off0 (Verify.headerBank c.lay.val c.koff) (64 * i + 8 * d) 2048
      (by unfold Verify.headerBank Verify.HDATA; omega)
      (by unfold Verify.headerBank Verify.HDATA; omega)]
    apply congrArg (BitVec.ofNat 64)
    dsimp [A, Verify.headerBank, Verify.HDATA]
    omega
  have fr : s.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    apply hF A (by omega)
    unfold Wr
    intro h
    rcases h with h | h <;> omega
  refine ⟨?_, ?_⟩
  · show accessValid ((hKey i d).eval s) 8 = true
    rw [key]; exact valid_ofNat A 8 (by dsimp [A, Verify.HDATA]; omega) (by dsimp [A, Verify.HDATA]; omega)
  · have he : (addC (.reg .x28) (hOff i d)).eval s = BitVec.ofNat 64 A := by
      simpa only [hKey, Addr.eval, addC_eval, E.eval] using key
    change s.getMem ((addC (.reg .x28) (hOff i d)).eval s) = _
    rw [he, fr]
    have H := hD.header c.lay.val (i + c.koff) d hl hib hd
    simpa only [A, w0] using H
theorem fetch_pc_congr {u v : MachineState} (h : u.pc = v.pc) : fetch vimage u = fetch vimage v := by
  unfold fetch; rw [h]
theorem headJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i ≤ 42) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hp1 : c.rungPc i (c.dig i) + landOff (c.dig i) < 209920)
    (hrun1 : vrun (c.startPc i) 7 = some (headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i
      (c.dig i) (hSlot i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i) + landOff (c.dig i)) 1 =
      some (ecallR (c.rungPc i (c.dig i) + landOff (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE : ∀ k, k ≤ 80 → (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
    intro k hk'
    simp only [kAt, Addr.eval, E.eval, h22]
    exact c.base_off hc i hi.2 k hk'
  set r := headJH .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i)) with hr
  have htable := c.header_load hc h25 i (c.dig i) hi (by omega) hF
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x22 (offL i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps hrun1 hp0 s hpc hobl
  have hn : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headJH_keeps .x22 (offL i) (c.rungPc i (c.dig i) + landOff (c.dig i)) i (c.dig i) (hSlot i (c.dig i))
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i hi.2
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headJH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  have hpcT : (r.toState s).pc = pcOf (c.rungPc i (c.dig i) + landOff (c.dig i)) := by
    rw [Result.toState_pc]; simp only [hr, headJH, E.eval]
  have hec : fetch vimage (r.toState s) = some (.base .ECALL) := by
    have hE := piece_ecall hrun2 hp1 (r.toState s) (by simp [ecallR, SymState.init]) rfl
    rw [← hE]
    apply fetch_pc_congr
    rw [hpcT, Result.toState_pc]; simp only [ecallR, E.eval]
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headJH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [hSlot, h6, if_true, E.eval]
    · simp only [hSlot, h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [hpcT]; simp only [landOff]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem kAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (kAt .x22 (offL i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h22]
  exact c.base_off hc i hi k hk
theorem lAt_eval (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (k : Nat) (hk : k ≤ 80) : (lAt .x22 (offL i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h22]
  rw [c.base_off hc i hi k hk]
theorem copy_mem (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x22 (offL i) (slotL i)) (BitVec.ofNat 64 A) =
      if A = slotL i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotL i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slotL_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slotL i + 8) (slotL i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h22 i hi 56 (by omega), c.lAt_eval hc h22 i hi 48 (by omega)]
theorem copy_obl (c : LCtx) (hc : c.ok) {s : MachineState} (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6) (i : Nat)
    (hi : i ≤ 42) : ∀ o ∈ copyObl .x22 (offL i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x22 (offL i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x22 (offL i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h22 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
theorem copy_post (c : LCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : c.i0 ≤ i ∧ i ≤ 42) (acc : List Digest) (hlen : acc.length = i - c.i0) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slotL (c.i0 + j)) (acc.getD j 0))
    (h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x22 (offL i) (slotL i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slotL (c.i0 + j)) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi.2
  have hs := slotL_props i hi.2
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slotL i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slotL i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h22 i hi.2 A hA)
  have hfr : Frame s t (fun A => A = slotL i + 8 ∨ A = slotL i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc c.i0 i hi.1 hi.2
    have hlo := hc.2.2.2.2.1
    have hsm := slotL_mono c.i0 i hi.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slotL_props (c.i0 + j) (by omega)
      have hmono : slotL (c.i0 + j) + 16 ≤ slotL i := by unfold slotL; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        show c.i0 + acc.length = i by omega]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2
theorem copyJ_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (first : Bool)
    (hfirst : first = true → i = 0 ∧ c.koff = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 209920)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x22 (offL i) (slotL i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL i) (slotL i) (c.endPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyN_keeps .x22 (offL i) (slotL i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl
theorem copyF_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hp0 : c.startPc i < 209920)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x22 (offL i) (slotL i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x22 (offL i) (slotL i) (c.startPc i) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyFH] using c.copy_obl hc h22 i (by omega))
  have hkeep := copyFH_keeps .x22 (offL i) (slotL i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i ⟨hi.1, by omega⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]
theorem copyN_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (hi : c.i0 ≤ 42) (hp0 : c.startPc 42 < 209920)
    (hrun : vrun (c.startPc 42) 6 = some (copyN .x22 (offL 42) (slotL 42) (c.endPc 42)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 42 acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 42 (acc ++ [c.val 42]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x22 (offL 42) (slotL 42) (c.endPc 42) with hr
  have hst := piece_steps hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h22 42 (by omega))
  have hkeep := copyN_keeps .x22 (offL 42) (slotL 42) (c.endPc 42)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 42 ⟨hi, le_refl _⟩ acc hlen hF hS h22
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen]; omega, h25, ?_⟩⟩
  rw [Result.toState_pc]; rfl
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem headR_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : c.i0 ≤ i ∧ i < 42) (hi0 : i ≠ 0) (hd : c.dig i < 7)
    (hp0 : c.startPc i < 209920) (hrp : c.rungPc i (c.dig i) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 =
      some (headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (if c.dig i = 6 then 6 else 5) (if c.dig i = 6 then 6 else 5) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i (by omega)
  have hs := slotL_props i (by omega)
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h22 : s.getReg .x22 = BitVec.ofNat 64 c.S6 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h22 i (by omega)
  set r := headRH .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i with hr
  have htable := c.header_load hc h25 i (c.dig i) ⟨hi.1, by omega⟩ (by omega) hF
    (kr _ _ (by simp [known]) (by decide))
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRH, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x22 (offL i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x22 (offL i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst := piece_steps hrun hp0 s hpc hobl
  have hec := piece_ecall hrun hp0 s hobl (by simp [hr, headRH])
  have hn : r.steps = (if c.dig i = 6 then 6 else 5) ∧ r.cycles = (if c.dig i = 6 then 6 else 5) := by
    simp only [hr, headRH]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := headRH_keeps .x22 (offL i) (c.dig i) (if c.dig i = 6 then some (slotL i) else none) (c.startPc i) i
  have a0e : (addC (E.reg .x22) (offL i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h22]; exact c.base_off0 hc i (by omega)
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (c.w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRH]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
    split_ifs <;> simp_all
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 ⟨hi.1, by omega⟩ hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slotL_props (c.i0 + j) (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · exact h25
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRH]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : c.dig i = 6
    · simp only [h6, if_true, E.eval]
    · simp only [h6, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [Result.toState_pc]; simp only [hr, headRH, hrp]
    by_cases h6 : c.dig i = 6 <;> simp [h6, E.eval]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
theorem land_mask (n k : Nat) (hk : k ≤ 9) :
    n &&& (512 * (2 ^ k - 1)) = 512 * (n / 512 % 2 ^ k) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, show (512 : Nat) = 2 ^ 9 by norm_num, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul,
    Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h9 : 9 ≤ j
  · simp only [h9, decide_true, Bool.true_and, show j - 9 + 9 = j by omega]
    by_cases hj : j - 9 < k
    · simp [hj]
    · simp [hj]
  · simp [h9]
theorem even_andNot1' (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]
theorem tab_target (a base b off : Nat) (h : off ≤ base) (ha : a + base + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 base + (BitVec.ofNat 64 b - BitVec.ofNat 64 off) =
      BitVec.ofNat 64 (a + (base - off) + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem field_shl (W s k : Nat) (hs : s ≤ 9) (hk : k ≤ 9) :
    W * 2 ^ s % 2 ^ 64 / 512 % 2 ^ k = W / 2 ^ (9 - s) % 2 ^ k := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, show (512 : Nat) = 2 ^ 9 by norm_num,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < k
  · simp only [hj, decide_true, Bool.true_and, show j + 9 < 64 by omega, show s ≤ j + 9 by omega]
    rw [show j + 9 - s = j + (9 - s) by omega]
  · simp [hj]
theorem shE_mask (s : MachineState) (w : Reg) (W : Word) (hw : s.getReg w = W) (b k : Nat) (hb : b < 64)
    (hk : k ≤ 9) :
    ((shE w b).eval s &&& BitVec.ofNat 64 (512 * (2 ^ k - 1))).toNat = 512 * (W.toNat / 2 ^ b % 2 ^ k) := by
  have hm : 512 * (2 ^ k - 1) < 2 ^ 64 := by
    have : 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk
    omega
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, land_mask _ _ hk]
  congr 1
  unfold shE
  split_ifs with h1 h2
  · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 9 - b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 9 - b < 64 by omega),
      Nat.shiftLeft_eq, field_shl _ _ _ (by omega) hk, show 9 - (9 - b) = b by omega]
  · simp only [E.eval, BinOp.eval, hw, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show b - 9 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b - 9 < 64 by omega),
      Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
      show 2 ^ (b - 9) * 512 = 2 ^ b by rw [show (512 : Nat) = 2 ^ 9 by norm_num, ← Nat.pow_add]; congr 1; omega]
  · have : b = 9 := by omega
    subst this
    simp only [E.eval, hw]
    rfl
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
theorem dig8_shift (X t' m : Nat) : X / 8 ^ (3 * t' + m) % 8 = X / 2 ^ (9 * t') / 8 ^ m % 8 := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_add, show (8 : Nat) ^ (3 * t') = 2 ^ (9 * t') by
    rw [show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_mul]; ring_nf]
theorem kOf_eq (c : LCtx) (t : Nat) (ht : t < 14) :
    c.kOf t = (if t < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * (t % 7)) % 512 := by
  unfold kOf dig
  by_cases h7 : t < 7
  · simp only [h7, if_true, show 3 * t < 21 by omega, show 3 * t + 1 < 21 by omega, show 3 * t + 2 < 21 by omega]
    rw [show t % 7 = t by omega]
    have e0 : c.d0.toNat / 8 ^ (3 * t) % 8 = c.d0.toNat / 2 ^ (9 * t) % 8 := by
      have := dig8_shift c.d0.toNat t 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d0.toNat / 2 ^ (9 * t) = Y
    norm_num
    omega
  · simp only [h7, if_false, show ¬ 3 * t < 21 by omega, show ¬ 3 * t + 1 < 21 by omega,
      show ¬ 3 * t + 2 < 21 by omega, show 3 * t < 42 by omega, show 3 * t + 1 < 42 by omega,
      show 3 * t + 2 < 42 by omega, if_true]
    rw [show t % 7 = t - 7 by omega, show 3 * t + 1 - 21 = 3 * (t - 7) + 1 by omega,
      show 3 * t + 2 - 21 = 3 * (t - 7) + 2 by omega, show 3 * t - 21 = 3 * (t - 7) by omega]
    have e0 : c.d1.toNat / 8 ^ (3 * (t - 7)) % 8 = c.d1.toNat / 2 ^ (9 * (t - 7)) % 8 := by
      have := dig8_shift c.d1.toNat (t - 7) 0; simpa using this
    rw [e0, dig8_shift, dig8_shift]
    generalize c.d1.toNat / 2 ^ (9 * (t - 7)) = Y
    norm_num
    omega
theorem kOf_lt (c : LCtx) (t : Nat) (ht : t < 14) : c.kOf t < 512 := by
  rw [c.kOf_eq t ht]; exact Nat.mod_lt _ (by norm_num)
theorem x_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (t : Nat) (ht : t < 13) (hi : c.i0 ≤ 3 * t + 2) (hp : c.tX (3 * t + 2) < 209920)
    (hrun : vrun (c.tX (3 * t + 2)) 5 = some (xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
      (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)))
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 (3 * t + 2) acc s) :
    ∃ u, Steps vimage s (if 9 * ((t + 1) % 7) = 9 then 3 else 4)
      (if 9 * ((t + 1) % 7) = 9 then 3 else 4) u ∧ c.ChainIn s0 (3 * t + 3) acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  set r := xJ (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) with hr
  have hst := piece_steps hrun hp s hpc' (by simp [hr, xJ])
  have hkeep := xJ_keeps (if t + 1 < 7 then .x16 else .x17) (9 * ((t + 1) % 7)) .x2
    (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760)
  have hW : s.getReg (if t + 1 < 7 then .x16 else .x17) = (if t + 1 < 7 then c.d0 else c.d1) := by
    split
    · exact kr .x16 c.d0 (by simp [known]) (by decide)
    · exact kr .x17 c.d1 (by simp [known]) (by decide)
  have h2 : s.getReg .x2 = BitVec.ofNat 64 (512 * (2 ^ 9 - 1)) := kr .x2 0x3fe00 (by simp [known]) (by decide)
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have hm := shE_mask s _ _ hW (9 * ((t + 1) % 7)) 9 (by omega) (le_refl _)
  have hk1 := c.kOf_lt (t + 1) (by omega)
  have hrow : ((if t + 1 < 7 then c.d0 else c.d1).toNat / 2 ^ (9 * ((t + 1) % 7)) % 2 ^ 9) = c.kOf (t + 1) := by
    rw [c.kOf_eq (t + 1) (by omega)]; rfl
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [hr, xJ, E.eval, BinOp.eval]
    rw [h2, h15]
    have e : ((shE (if t + 1 < 7 then Reg.x16 else Reg.x17) (9 * ((t + 1) % 7))).eval s &&&
        BitVec.ofNat 64 (512 * (2 ^ 9 - 1))) = BitVec.ofNat 64 (512 * c.kOf (t + 1)) := by
      apply BitVec.eq_of_toNat_eq; rw [hm, hrow, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have e2 : BitVec.ofNat 64 (512 * c.kOf (t + 1)) + BitVec.ofNat 64 0x6e000 +
        (BitVec.ofNat 64 (32 * (t + 1)) - BitVec.ofNat 64 1760) =
        BitVec.ofNat 64 (0x1000 + 4 * entW (t + 1) (c.kOf (t + 1))) := by
      rw [tab_target _ _ _ _ (by omega) (by omega)]
      congr 1
      unfold entW ttabIdx; omega
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc
    rw [if_neg (by omega), if_pos (by omega), show (3 * t + 3) / 3 = t + 1 by omega]
end LCtx
end SigGolfCandidate.T3M
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
namespace LCtx
def ChainOut (c : LCtx) (s0 : MachineState) (n : Nat) (acc : List Digest) (s : MachineState) : Prop :=
  c.Base s0 (c.Wr n) acc s ∧ acc.length = n - c.i0 ∧ s.pc = pcOf c.ret
theorem next_inline (c : LCtx) (s0 : MachineState) (i : Nat) (hi : i < 42) (h2 : i % 3 ≠ 2)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 i acc s) : c.ChainIn s0 (i + 1) acc s := by
  obtain ⟨hB, hlen, h25, hpc⟩ := hs
  refine ⟨hB, hlen.trans (by omega), h25, ?_⟩
  rw [hpc]
  simp only [endPc, startPc, show i ≠ 42 by omega, show i + 1 ≠ 42 by omega, if_false]
  by_cases h0 : i % 3 = 0
  · rw [if_pos h0, if_neg (show (i + 1) % 3 ≠ 0 by omega), if_pos (show (i + 1) % 3 = 1 by omega)]
    unfold tB; rw [show (i + 1) / 3 = i / 3 by omega]
  · rw [if_neg h0, if_pos (show i % 3 = 1 by omega), if_neg (show (i + 1) % 3 ≠ 0 by omega),
      if_neg (show (i + 1) % 3 ≠ 1 by omega)]
    unfold tC; rw [show (i + 1) / 3 = i / 3 by omega]
theorem x13_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (_hi : c.i0 ≤ 41) (hp : c.tX 41 < 209920) (hrun : vrun (c.tX 41) 4 = some ctabX)
    (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 41 acc s) :
    ∃ u, Steps vimage s 3 3 u ∧ c.ChainIn s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have hpc' : s.pc = pcOf (c.tX 41) := by rw [hpc]; unfold endPc; simp
  have hst := piece_steps hrun hp s hpc' (by simp [ctabX])
  have h15 : s.getReg .x15 = BitVec.ofNat 64 0x6e000 := kr .x15 0x6e000 (by simp [known]) (by decide)
  have h29 : s.getReg .x29 = 7#64 - BitVec.ofNat 64 c.ck := kr .x29 _ (by simp [known]) (by decide)
  have hck := hc.2.2.2.2.2.2.1
  refine ⟨ctabX.toState s, hst, ⟨⟨fun x hx => (ctabX_keeps.reg s (not_mem_sub hx (by decide))).trans (hR x hx),
    hF.mono (fun A _ h => by
      have hlo := hc.2.2.2.2.1
      unfold Wr at h ⊢; rcases h with h | h
      · exact Or.inl h
      · right; refine ⟨?_, h.2⟩; omega), hS⟩, by omega, h25, ?_⟩⟩
  · rw [Result.toState_pc]
    simp only [ctabX, E.eval, BinOp.eval, h15, h29]
    have e2 : BitVec.ofNat 64 0x6e000 - (7#64 - BitVec.ofNat 64 c.ck) <<< ((5 : Word).toNat % 64) + (-1824 : Word) =
        BitVec.ofNat 64 (0x1000 + 4 * (ctabIdx + 8 * c.ck)) := by
      have hk : c.ck ≤ 8 := hck
      generalize c.ck = k at hk ⊢
      unfold ctabIdx
      interval_cases k <;> decide
    rw [e2, even_andNot1' _ (by omega)]
    unfold startPc; simp
theorem ret_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2) (p : Nat)
    (hp : p < 209920) (hrun : vrun p 2 = some retR) (s : MachineState) (hpc : s.pc = pcOf p)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) :
    ∃ u, Steps vimage s 1 1 u ∧ (∀ x, u.getReg x = s.getReg x) ∧ (∀ A, u.getMem A = s.getMem A) ∧
      u.pc = pcOf c.ret := by
  have hst := piece_steps hrun hp s hpc (by simp [retR])
  have h1 : s.getReg .x1 = pcOf c.ret := (hR .x1 (by decide)).trans (hk (.x1, pcOf c.ret) (by simp [known]))
  refine ⟨retR.toState s, hst, fun x => retR_keeps.reg s (by simp), fun A => rfl, ?_⟩
  rw [Result.toState_pc]
  simp only [retR, E.eval, BinOp.eval, h1]
  exact even_andNot1' _ (by have := hc.2.2.2.2.2.2.2.1; omega)
theorem ckdone_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hrun : vrun ckDone 2 = some retR) (acc : List Digest) (s : MachineState) (hs : c.EndInv s0 42 acc s) :
    ∃ u, Steps vimage s 1 1 u ∧ c.ChainOut s0 43 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.ret_step hc hk ckDone (by decide) hrun s (by rw [hpc]; rfl) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩
theorem ck8_step (c : LCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h8 : c.ck = 8) (hrun : vrun (ctabIdx + 64) 2 = some retR) (acc : List Digest) (s : MachineState)
    (hs : c.ChainIn s0 42 acc s) : ∃ u, Steps vimage s 1 1 u ∧ c.ChainOut s0 42 acc u := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, -, hpc⟩ := hs
  obtain ⟨u, hst, hreg, hmem, hpcu⟩ := c.ret_step hc hk (ctabIdx + 64) (by decide) hrun s
    (by rw [hpc]; unfold startPc; simp [h8]) hR
  refine ⟨u, hst, ⟨⟨fun x hx => (hreg x).trans (hR x hx), fun A hA hn => (hmem _).trans (hF A hA hn),
    fun j hj => ?_⟩, hlen, hpcu⟩⟩
  exact ⟨(hmem _).trans (hS j hj).1, (hmem _).trans (hS j hj).2⟩
end LCtx
end SigGolfCandidate.T3M
