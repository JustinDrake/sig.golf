import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.Common
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-! # W1a chains: semantics of the in-place chain code

The state of the chain phase of layer `lay`:
* `Fresh wl lay i`: the witness words not yet overwritten by verify: words `2 .. 7` (pad and value)
  of every chain block of the chains `(lay, i ..)` and of the layers `< lay` (processed later), and
  the counters `c0 .. c3` in the tweak slot of block `(0, 0)` while layer 0's chain 0 has not run;
* chain `i`'s head writes its tweak slot, its rungs overwrite the value slot and spill into the next
  block's tweak slot (or the next region's block 0, or past the witness): none of these is fresh
  for `(lay, i + 1)`.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Tweak word 0 of the hypertree inputs of layer `lay`: tag byte 1, layer, the rest zero. -/
def hWord (lay : Nat) : Nat := 0x101 + 65536 * lay

/-- The byte address of chain block `(lay, i)` and the layer base `s6`. -/
def blkN (lay i : Nat) : Nat := 0x800 + blockOff lay i
def s6N (lay : Nat) : Nat := blkN lay 0 + 1344
/-- Tweak word 0 of chain `i` (byte 4, the step, zero). -/
def twW0 (lay i : Nat) : Nat := hWord lay + 2 ^ 40 * i

theorem blkN_eq (lay i : Nat) : blkN lay i = 4992 + 2688 * lay + 64 * i := by
  unfold blkN; rw [blockOff_eq]; omega

theorem s6N_eq (lay : Nat) : s6N lay = 6336 + 2688 * lay := by
  unfold s6N; rw [blkN_eq]; omega

/-! ## Fresh witness words -/

def FreshW (lay i lay' i' k : Nat) : Prop :=
  lay' < 5 ∧ i' < 42 ∧ k < 8 ∧ (lay' < lay ∨ (lay' = lay ∧ i ≤ i')) ∧
    (2 ≤ k ∨ (lay' = 0 ∧ i' = 0 ∧ (0 < lay ∨ i = 0)))

def Fresh (wl : List Byte) (lay i : Nat) (s : MachineState) : Prop :=
  ∀ lay' i' k, FreshW lay i lay' i' k →
    s.getMem (BitVec.ofNat 64 (blkN lay' i' + 8 * k)) = w64 (slice wl (blockOff lay' i' + 8 * k) 8)

theorem Fresh_of_all {wl : List Byte} {s : MachineState} (h : WitAll wl s) (lay i : Nat) :
    Fresh wl lay i s := by
  intro lay' i' k hw
  obtain ⟨h1, h2, h3, -, -⟩ := hw
  have e := h ((blockOff lay' i' + 8 * k) / 8) (by rw [blockOff_eq]; omega)
  have e8 : 8 * ((blockOff lay' i' + 8 * k) / 8) = blockOff lay' i' + 8 * k := by
    rw [blockOff_eq]; omega
  rw [e8] at e
  rw [show blkN lay' i' + 8 * k = 0x800 + (blockOff lay' i' + 8 * k) by unfold blkN; omega]
  exact e

theorem Fresh_sub {wl : List Byte} {s : MachineState} {l1 i1 l2 i2 : Nat} (hF : Fresh wl l1 i1 s)
    (h : ∀ a b k, FreshW l2 i2 a b k → FreshW l1 i1 a b k) : Fresh wl l2 i2 s :=
  fun a b k hw => hF a b k (h a b k hw)

theorem Fresh_frame {wl : List Byte} {s t : MachineState} {lay i : Nat} (hF : Fresh wl lay i s)
    (h : ∀ A, A < 2 ^ 64 → 0x800 + 2944 ≤ A → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) :
    Fresh wl lay i t := by
  intro a b k hw
  rw [h _ (by obtain ⟨h1, h2, h3, -⟩ := hw; rw [blkN_eq]; omega) (by rw [blkN_eq]; omega)]
  exact hF a b k hw

/-- The next chain: chain `i`'s own block and its spill are not fresh for `(lay, i + 1)`. -/
theorem FreshW_next {lay i a b k : Nat} (h : FreshW lay (i + 1) a b k) : FreshW lay i a b k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by omega, ?_⟩
  rcases h5 with h5 | ⟨h6, h7, h8⟩
  · exact Or.inl h5
  · exact Or.inr ⟨h6, h7, by omega⟩

/-- The layer transition: after layer `lay`'s chains, the fresh words of layer `lay - 1`. -/
theorem FreshW_layer {lay a b k : Nat} (hl : 1 ≤ lay) (h : FreshW (lay - 1) 0 a b k) :
    FreshW lay 42 a b k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, by omega, ?_⟩
  rcases h5 with h5 | ⟨h6, h7, _⟩
  · exact Or.inl h5
  · exact Or.inr ⟨h6, h7, Or.inl (by omega)⟩

/-- A word written by chain `i` (tweak slot, value slot, spill) is not fresh for `(lay, i + 1)`. -/
theorem fresh_ne {lay i a b k : Nat} (hw : FreshW lay (i + 1) a b k) (hi : i < 42) (d : Nat)
    (hd : d = 0 ∨ d = 8 ∨ d = 48 ∨ d = 56 ∨ d = 64 ∨ d = 72) :
    blkN a b + 8 * k ≠ blkN lay i + d := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  rw [blkN_eq, blkN_eq]
  rcases h4 with h4 | ⟨rfl, h4⟩ <;> omega

/-- The words of chain `i`'s own block that are still fresh: its pad (and the value, before the first
rung). -/
theorem FreshW_own {lay i k : Nat} (hl : lay < 5) (hi : i < 42) (hk : 2 ≤ k) (hk' : k < 8) :
    FreshW lay i lay i k := ⟨hl, hi, hk', Or.inr ⟨rfl, le_refl _⟩, Or.inl hk⟩

/-- The counters of layers `0 .. 3` (words 0, 1 of block `(0, 0)`) are fresh at the start of every
layer's chains. -/
theorem FreshW_ctr {lay k : Nat} (hl : lay < 5) (hk : k < 2) : FreshW lay 0 0 0 k :=
  ⟨by omega, by omega, by omega, by omega, Or.inr ⟨rfl, rfl, Or.inr rfl⟩⟩

/-! ## Addresses of the chain code -/

theorem bk_eval (s : MachineState) (lay i k : Nat) (hx : s.getReg .x22 = BitVec.ofNat 64 (s6N lay))
    (hl : lay < 5) (hi : i < 42) (hk : k < 2 ^ 20) :
    (bk i k).eval s = BitVec.ofNat 64 (blkN lay i + k) := by
  unfold bk
  rw [norm_eval, addC_eval]
  simp only [E.eval, hx, offW]
  apply BitVec.eq_of_toNat_eq
  rw [s6N_eq, blkN_eq]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ldK_eval (s : MachineState) (lay i k : Nat) (hx : s.getReg .x22 = BitVec.ofNat 64 (s6N lay))
    (hl : lay < 5) (hi : i < 42) (hk : k < 2 ^ 20) :
    (ldK i k).eval s = s.getMem (BitVec.ofNat 64 (blkN lay i + k)) := by
  unfold ldK
  simp only [E.eval, Addr.toE_eval, bk_eval s lay i k hx hl hi hk]

theorem valid_blk (lay i k w : Nat) (hl : lay < 5) (hi : i < 42) (hk : k < 128) (hw : w = 1 ∨ w = 8)
    (ha : (blkN lay i + k) % w = 0) :
    accessValid (BitVec.ofNat 64 (blkN lay i + k)) w = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [blkN_eq]; omega)]
  refine ⟨?_, ha⟩
  simp only [MEMORY_BYTES]; rw [blkN_eq]; omega

theorem hashArgsB_ok (a d : Nat) (ha : a % 8 = 0) (ha2 : a + 64 ≤ 2 ^ 24) (hd : d % 8 = 0)
    (hd2 : d + 32 ≤ 2 ^ 24) : hashArgsB a (64 * (0 + 1)) d = true := by
  simp only [hashArgsB, MEMORY_BYTES]; simp; omega

theorem safeDest_slot (i : Nat) (hi : i < 42) : safeDest (slotA i) = true := by
  interval_cases i <;> decide

theorem valid_of (B k w : Nat) (hB : B + 256 < 2 ^ 24) (hk : k < 128) (ha : (B + k) % w = 0) :
    accessValid (BitVec.ofNat 64 (B + k)) w = true ∨ w = 0 ∨ 8 < w := by
  by_cases hw : w = 0 ∨ 8 < w
  · exact Or.inr hw
  · left
    rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨?_, ha⟩
    simp only [MEMORY_BYTES]; omega

theorem blkN_mod8 (lay i : Nat) : blkN lay i % 8 = 0 := by rw [blkN_eq]; omega

theorem s6N_mod8 (lay : Nat) : s6N lay % 8 = 0 := by rw [s6N_eq]; omega


/-! ## The chain context -/

structure CCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  tau : Nat
  e : Nat
  d0 : Word
  d1 : Word
  /-- The return pc of the chain code (the transition copy's leaf block). -/
  ret : Word

def CCtx.x31 (c : CCtx) : Word := BitVec.ofNat 64 (c.tau + 2 ^ 32 * c.e)

def CCtx.Regs (c : CCtx) (s : MachineState) : Prop :=
  s.getReg .x16 = c.d0 ∧ s.getReg .x17 = c.d1 ∧
  s.getReg .x23 = BitVec.ofNat 64 (c.e + 2 ^ heightL c.lay) ∧ s.getReg .x30 = BitVec.ofNat 64 (if c.lay = 0 then c.e else c.tau) ∧
  s.getReg .x31 = c.x31

def CCtx.ok (c : CCtx) : Prop :=
  c.lay < 5 ∧ c.tau < 2 ^ 32 ∧ c.e < 2 ^ 32 ∧ c.wl.length = 16384 ∧ c.d0.toNat < 2 ^ 63 ∧
    c.d1.toNat < 2 ^ 63

/-- The running-header register `x25` is no longer used by the chain code (address headers). -/
def carryW0 (lay : Nat) : Word := BitVec.ofNat 64 (hWord lay) - K40

/-- The address header before the tree-high byte (zero in these programs). -/
def newTwW0 (lay i mu : Nat) : Nat := blkN lay i + 2 ^ 32 * mu

theorem newTwW0_lt40 (lay i mu : Nat) (hl : lay < 7) (hi : i < 42) (hm : mu < 8) :
    newTwW0 lay i mu < 2 ^ 40 := by
  unfold newTwW0
  rw [blkN_eq]
  norm_num at *
  omega

/-- Digit `i` of the current layer. -/
def dig (c : CCtx) (i : Nat) : Nat := (if i < 21 then c.d0 else c.d1).toNat / 8 ^ (i % 21) % 8

theorem dig_lt (c : CCtx) (i : Nat) : dig c i < 8 := by unfold dig; omega

/-- The table row of triple `t`. -/
def kOf (c : CCtx) (t : Nat) : Nat := dig c (3 * t) + 8 * dig c (3 * t + 1) + 64 * dig c (3 * t + 2)

/-- The shared code block of chain `i`'s triple. -/
def tb (c : CCtx) (i : Nat) : Nat := triBase (i / 3) (dig c (3 * (i / 3) + 1)) (dig c (3 * (i / 3) + 2))
def tB (c : CCtx) (i : Nat) : Nat := pcB (i / 3) (dig c (3 * (i / 3) + 1)) (dig c (3 * (i / 3) + 2))
def tC (c : CCtx) (i : Nat) : Nat := pcC (i / 3) (dig c (3 * (i / 3) + 1)) (dig c (3 * (i / 3) + 2))
def tX (c : CCtx) (i : Nat) : Nat := pcX (i / 3) (dig c (3 * (i / 3) + 1)) (dig c (3 * (i / 3) + 2))

/-- Where chain `i`'s code starts: `A` in its table slot, `B` and `C` in the shared block. -/
def startPc (c : CCtx) (i : Nat) : Nat :=
  if i % 3 = 0 then entW (i / 3) (kOf c (i / 3)) else if i % 3 = 1 then tB c i else tC c i

/-- The first word of rung `mu` of chain `i`. -/
def rungPc (c : CCtx) (i mu : Nat) : Nat :=
  if i % 3 = 0 then tb c i + 2 * (mu - 1)
  else (if i % 3 = 1 then tB c i else tC c i) + 4 + 2 * (mu - dig c i - 1)

/-- Where chain `i`'s code ends: the next chain's code, or the extraction after `C`. -/
def endPc (c : CCtx) (i : Nat) : Nat :=
  if i % 3 = 0 then tB c i else if i % 3 = 1 then tC c i else tX c i

/-- Bytes 6, 7 of the word at CB (`0xC0`) are zero. A t0 conjunct of `LayerIn` (there the chain
tweak was built in CB); W1a's layers neither read nor write CB, and the conjunct is only carried
through the chain phase so that the interface of `LayerGood` with `Top` keeps its shape. -/
def CB0 (s : MachineState) : Prop := (s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 64 = 0

/-- The registers and buffers common to the whole chain phase (`acc` = the chain ends so far). -/
def ChBase (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK chK0 s ∧ c.Regs s ∧ s.getReg .x22 = BitVec.ofNat 64 (s6N c.lay) ∧
  s.getReg .x27 = BitVec.ofNat 64 (hWord c.lay + 768) ∧ s.getReg .x1 = c.ret ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ CB0 s

/-- Before chain `i`'s code (`x25` = the previous chain's tweak word 0). -/
def ChainIn (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  ChBase c i acc s ∧ True ∧ Fresh c.wl c.lay i s ∧
  s.pc = pcOf (startPc c i)

/-- Chain `i`'s tweak slot: word 0 with the layer and the chain (byte 4, the step, free), word 1. -/
def TwOk (c : CCtx) (i : Nat) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 (blkN c.lay i))).toNat % 2 ^ 32 = blkN c.lay i ∧
  (s.getMem (BitVec.ofNat 64 (blkN c.lay i))).toNat / 2 ^ 40 = 0 ∧
  s.getMem (BitVec.ofNat 64 (blkN c.lay i + 8)) = c.x31

/-- Chain `i`'s pad (words 2 .. 5 of its block). -/
def PadOk (c : CCtx) (i : Nat) (s : MachineState) : Prop :=
  ∀ k, 2 ≤ k → k < 6 → s.getMem (BitVec.ofNat 64 (blkN c.lay i + 8 * k)) =
    w64 (slice c.wl (blockOff c.lay i + 8 * k) 8)

/-- At rung `mu` of chain `i` with the value `v` in the block's value slot. -/
def StepInv (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (s : MachineState) : Prop :=
  ChBase c i acc s ∧ True ∧ Fresh c.wl c.lay (i + 1) s ∧
  PadOk c i s ∧ TwOk c i s ∧ s.getMem (BitVec.ofNat 64 (blkN c.lay i + 48)) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (blkN c.lay i + 56)) = vw1 v ∧ v.length = 16 ∧
  s.getReg .x10 = BitVec.ofNat 64 (blkN c.lay i) ∧ s.getReg .x12 = BitVec.ofNat 64 (blkN c.lay i + 48) ∧
  s.pc = pcOf (rungPc c i mu)

/-- After chain `i` (its end value is in its leaf-pk slot, the last element of `acc`). -/
def EndInv (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  ChBase c (i + 1) acc s ∧ True ∧ Fresh c.wl c.lay (i + 1) s ∧
  s.pc = pcOf (endPc c i)

theorem length_witChain (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) :
    (witChain c.wl c.lay i).length = 16 := by
  obtain ⟨h1, -, -, h4, -⟩ := hc
  unfold witChain; rw [blockOff_eq]; apply length_slice16; omega

theorem length_witPad (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) :
    (witPad c.wl c.lay i).length = 32 := by
  obtain ⟨h1, -, -, h4, -⟩ := hc
  unfold witPad slice; rw [blockOff_eq]; simp; omega

/-! ## The hash input of a chain step -/

theorem slice_slice (l : List Byte) (a b n m : Nat) (h : b + m ≤ n) :
    slice (slice l a n) b m = slice l (a + b) m := by
  simp only [slice, List.drop_take, List.drop_drop, List.take_take]
  rw [Nat.min_eq_left (by omega), Nat.add_comm]

theorem wordsOfN_pad (pad : List Byte) :
    wordsOfN 4 pad = [w64 (slice pad 0 8), w64 (slice pad 8 8), w64 (slice pad 16 8), w64 (slice pad 24 8)] := by
  simp [wordsOfN, slice, List.drop_drop]

/-- The W1a chain block `tw' || pad || v` as words (`p' = mu - 1 + 256 i`). -/
theorem fmt_chainInputP_words (lay tau e i mu : Nat) (pad : List Byte) (v : Val) (hp : pad.length = 32)
    (hv : v.length = 16) (hmu : 1 ≤ mu) (hmu' : mu ≤ 8) (hi : i < 2 ^ 24) :
    fmt (chainInputP lay tau e i mu pad v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 1 lay tau (mu - 1 + 256 * i)), BitVec.ofNat 64 (twHi tau e),
        w64 (slice pad 0 8), w64 (slice pad 8 8), w64 (slice pad 16 8), w64 (slice pad 24 8),
        vw0 v, vw1 v] := by
  rw [fmt_chainInputP _ _ _ _ _ _ _ hp hv hmu hmu' hi]
  have hl : (tweak 1 lay tau (mu - 1 + 256 * i) e ++ pad ++ v).length ≤ 8 * 8 := by
    simp [length_tweak, hv, hp]
  have h8 : wordsOfN 8 (tweak 1 lay tau (mu - 1 + 256 * i) e ++ (pad ++ v)) =
      wordsOfN 2 (tweak 1 lay tau (mu - 1 + 256 * i) e) ++ wordsOfN 6 (pad ++ v) :=
    wordsOfN_append 2 6 _ _ (by simp [length_tweak])
  have h6 : wordsOfN 6 (pad ++ v) = wordsOfN 4 pad ++ wordsOfN 2 v :=
    wordsOfN_append 4 2 _ _ (by simp [hp])
  have h2 : wordsOfN 2 v = [vw0 v, vw1 v] := by
    have := wordsOfN_val_append v hv 0 []
    simpa [wordsOfN] using this
  have hw : wordsOfN 8 (tweak 1 lay tau (mu - 1 + 256 * i) e ++ pad ++ v) =
      [BitVec.ofNat 64 (twLo 1 lay tau (mu - 1 + 256 * i)), BitVec.ofNat 64 (twHi tau e),
        w64 (slice pad 0 8), w64 (slice pad 8 8), w64 (slice pad 16 8), w64 (slice pad 24 8),
        vw0 v, vw1 v] := by
    rw [List.append_assoc, h8, h6, wordsOfN_tweak, wordsOfN_pad, h2]; rfl
  unfold queryOfWords ofList
  rw [← hw, wordsToNat_wordsOfN 8 _ hl]

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

/-- The step byte `sb MU, 4(block)` on a tweak word with the layer (low 32 bits) and the chain. -/
theorem stepByte_toNat (w : Word) (lay i p : Nat) (hl : lay < 5) (hi : i < 42) (hp : p < 8)
    (h1 : w.toNat % 2 ^ 32 = blkN lay i) (h2 : w.toNat / 2 ^ 40 = 0) :
    (StoreKind.merge .b w 4 (BitVec.ofNat 64 p)).toNat = newTwW0 lay i p := by
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold newTwW0
  rw [blkN_eq] at h1 ⊢
  generalize w.toNat = x at *
  norm_num at h1 h2 ⊢
  omega


/-! ## Runs of the chain code -/

theorem Glob_frameC {gk : List (Reg × Word)} {wl pk : List Byte} {s t : MachineState}
    (hG : Glob gk wl pk s) (hr : ∀ p ∈ gk, t.getReg p.1 = s.getReg p.1)
    (hm : ∀ A, A < 0x800 + 2944 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) :
    Glob gk wl pk t := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨fun p hp => (hr p hp).trans (h1 p hp), fun j hj => ?_, ?_, fun a ha => ?_⟩
  · rw [hm _ (by omega)]; exact h2 j hj
  · exact ⟨(hm 0xA0 (by omega)).trans h3.1, (hm 0xA8 (by omega)).trans h3.2⟩
  · have : a < 0x800 := by simp [pSlots] at ha; omega
    rw [hm a (by omega)]; exact h4 a ha

theorem Glob_frameS {gk : List (Reg × Word)} {wl pk : List Byte} {s t : MachineState}
    (hG : Glob gk wl pk s) (hr : ∀ p ∈ gk, t.getReg p.1 = s.getReg p.1)
    (hm : ∀ A, A < 0x800 + 2944 → (A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8 ∨ 0x800 ≤ A) →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) :
    Glob gk wl pk t := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨fun p hp => (hr p hp).trans (h1 p hp), fun j hj => ?_, ?_, fun a ha => ?_⟩
  · rw [hm _ (by omega) (Or.inr (Or.inr (Or.inr (by omega))))]; exact h2 j hj
  · exact ⟨(hm 0xA0 (by omega) (by simp)).trans h3.1, (hm 0xA8 (by omega) (by simp)).trans h3.2⟩
  · have : a < 0x800 := by simp [pSlots] at ha; omega
    rw [hm a (by omega) (Or.inl ha)]; exact h4 a ha

theorem crun {stops : List Nat} {p : Nat} {dirs : List Dir} {r : PRes}
    (hrun : runAt chK0 stops p dirs = some r) (s : MachineState) (hpc : s.pc = pcOf p)
    (hk : KnownOK chK0 s) (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound hrun vlook_ok s hpc hk hobl hbr

theorem known_eval {s : MachineState} (hk : KnownOK chK0 s) (x : Reg) :
    ((RegFile.withKnown chK0).get x).eval s = s.getReg x :=
  RegFile.withKnown_eval s chK0 hk x

theorem chK0_x5 : ((.x5 : Reg), (0 : Word)) ∈ chK0 := by simp [chK0, gkL, gkL0, baseK]
theorem chK0_x11 : ((.x11 : Reg), (64 : Word)) ∈ chK0 := by simp [chK0]

theorem blk_ofNat_add (lay i k : Nat) : BitVec.ofNat 64 (blkN lay i) + BitVec.ofNat 64 k =
    BitVec.ofNat 64 (blkN lay i + k) := by rw [BitVec.ofNat_add_ofNat]

theorem twLo_tau (lay tau p : Nat) (h : tau < 2 ^ 32) : twLo 1 lay tau p = twLo 1 lay 0 p := by
  unfold twLo; rw [Nat.div_eq_of_lt h, Nat.zero_div]

/-- Chain `i`'s pad words in the witness are the pad's. -/
theorem pad_word (c : CCtx) (i k : Nat) (hk : 2 ≤ k) (hk' : k < 6) :
    w64 (slice c.wl (blockOff c.lay i + 8 * k) 8) = w64 (slice (witPad c.wl c.lay i) (8 * (k - 2)) 8) := by
  unfold witPad; rw [slice_slice _ _ _ _ _ (by omega),
    show blockOff c.lay i + 16 + 8 * (k - 2) = blockOff c.lay i + 8 * k by omega]

theorem addrFmt_chainInputP_words (lay tau e i mu : Nat) (pad : List Byte) (v : Val)
    (hp : pad.length = 32) (hv : v.length = 16) (hl : lay < 7) (ht : tau < 2 ^ 32)
    (hi : i < 42) (hmu : 1 ≤ mu) (hmu' : mu ≤ 8) :
    addrFmt (chainInputP lay tau e i mu pad v) = queryOfWords 0
      [BitVec.ofNat 64 (newTwW0 lay i (mu - 1)), BitVec.ofNat 64 (twHi tau e),
        w64 (slice pad 0 8), w64 (slice pad 8 8), w64 (slice pad 16 8), w64 (slice pad 24 8),
        vw0 v, vw1 v] := by
  have hd : twLo 1 lay tau (mu - 1 + 256 * i) = AddressFormat.oldHeader lay 0 i (mu - 1) := by
    unfold twLo AddressFormat.oldHeader
    simp only [Nat.reduceMod, Nat.reducePow, Nat.mul_zero, Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega : lay < 256),
      show tau / 4294967296 = 0 by omega,
      show (mu - 1 + 256 * i) % 4294967296 = mu - 1 + 256 * i by omega]
    simp only [Nat.zero_mod, Nat.mul_zero, Nat.add_zero]
    omega
  have hw : AddressFormat.oldHeader lay 0 i (mu - 1) < 2 ^ 64 := by unfold AddressFormat.oldHeader; omega
  rw [addrFmt, fmt_chainInputP_words lay tau e i mu pad v hp hv hmu hmu' (by omega), hd,
    AddressFormat.queryPerm_words _ _ rfl (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold AddressFormat.oldHeader; omega) (by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]; unfold AddressFormat.oldHeader; omega)]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
  unfold AddressFormat.oldHeader
  rw [AddressFormat.old_header lay 0 i (mu - 1) hl (by norm_num) hi (by omega)]
  congr 2
  unfold newTwW0
  rw [blkN_eq]
  simp only [Nat.mul_zero, Nat.add_zero]
  rfl

/-- The machine hash input of a chain step at block `b`: `tw' || pad || v`. -/
theorem chain_hashInput (c : CCtx) (hc : c.ok) (i mu : Nat) (hi : i < 42) (hmu : 1 ≤ mu) (hmu' : mu ≤ 7)
    (v : Val) (hv : v.length = 16) (t : MachineState)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 (blkN c.lay i)) (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (m0 : t.getMem (BitVec.ofNat 64 (blkN c.lay i)) = BitVec.ofNat 64 (newTwW0 c.lay i (mu - 1)))
    (m1 : t.getMem (BitVec.ofNat 64 (blkN c.lay i + 8)) = c.x31) (hP : PadOk c i t)
    (m6 : t.getMem (BitVec.ofNat 64 (blkN c.lay i + 48)) = vw0 v)
    (m7 : t.getMem (BitVec.ofNat 64 (blkN c.lay i + 56)) = vw1 v) :
    hashInput t = addrFmt (chainInputP c.lay c.tau c.e i mu (witPad c.wl c.lay i) v) := by
  have hpl := length_witPad c hc i hi
  obtain ⟨hlay, htau, he, hwl, -⟩ := hc
  rw [hashInput_ofNat _ _ 0 h10 h11 (blkN_mod8 _ _) (by rw [blkN_eq]; omega),
    addrFmt_chainInputP_words _ _ _ _ _ _ _ hpl hv (by omega) (by omega) hi hmu (by omega)]
  apply congrArg (queryOfWords 0)
  simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
    Nat.mul_zero, List.cons.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, m6, m7, trivial⟩
  · exact m0
  · rw [m1]; unfold CCtx.x31 twHi; apply congrArg (BitVec.ofNat 64); omega
  · rw [hP 2 (by omega) (by omega), pad_word c i 2 (by omega) (by omega)]
  · rw [hP 3 (by omega) (by omega), pad_word c i 3 (by omega) (by omega)]
  · rw [hP 4 (by omega) (by omega), pad_word c i 4 (by omega) (by omega)]
  · rw [hP 5 (by omega) (by omega), pad_word c i 5 (by omega) (by omega)]


theorem fresh_disj {lay i a b k : Nat} (hw : FreshW lay (i + 1) a b k) (hi : i < 42) :
    blkN a b + 8 * k ≠ blkN lay i ∧ blkN a b + 8 * k ≠ blkN lay i + 8 ∧
      (blkN a b + 8 * k + 8 ≤ blkN lay i + 48 ∨ blkN lay i + 48 + 32 ≤ blkN a b + 8 * k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  rw [blkN_eq, blkN_eq]
  rcases h4 with h4 | ⟨rfl, h4⟩ <;> omega

theorem rungPc_succ (c : CCtx) (i mu : Nat) (h1 : 1 ≤ mu) (hd : dig c i < mu) :
    rungPc c i (mu + 1) = rungPc c i mu + 2 := by
  unfold rungPc; split_ifs <;> omega

theorem rungPc_end (c : CCtx) (i : Nat) (hd : dig c i < 7) : rungPc c i 7 + 3 = endPc c i := by
  have e1 : i % 3 = 1 → dig c (3 * (i / 3) + 1) = dig c i := fun h => by
    rw [show 3 * (i / 3) + 1 = i by omega]
  have e2 : i % 3 = 2 → dig c (3 * (i / 3) + 2) = dig c i := fun h => by
    rw [show 3 * (i / 3) + 2 = i by omega]
  unfold rungPc endPc tb tB tC tX pcX pcC pcB partLen
  split_ifs <;> omega

/-- Just before the `ecall` of step `mu` of chain `i` (value `v` in the value slot, the step byte
written, `a2` = the value slot, or the leaf-pk slot for step 7). -/
def PreHash (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (t : MachineState) : Prop :=
  ChBase c i acc t ∧ True ∧ Fresh c.wl c.lay (i + 1) t ∧
  PadOk c i t ∧ t.getMem (BitVec.ofNat 64 (blkN c.lay i)) = BitVec.ofNat 64 (newTwW0 c.lay i (mu - 1)) ∧
  t.getMem (BitVec.ofNat 64 (blkN c.lay i + 8)) = c.x31 ∧
  t.getMem (BitVec.ofNat 64 (blkN c.lay i + 48)) = vw0 v ∧
  t.getMem (BitVec.ofNat 64 (blkN c.lay i + 56)) = vw1 v ∧ v.length = 16 ∧
  t.getReg .x10 = BitVec.ofNat 64 (blkN c.lay i) ∧
  t.getReg .x12 = BitVec.ofNat 64 (if mu = 7 then slotA i else blkN c.lay i + 48) ∧
  t.pc = pcOf (rungPc c i mu + (if mu = 7 then 2 else 1)) ∧ fetch image t = some (.base .ECALL)

/-- The step hash of `PreHash`: the query, then rung `mu + 1` or (after step 7) the chain's end. -/
theorem prehash_step (c : CCtx) (hc : c.ok) (i mu : Nat) (hi : i < 42) (h1 : 1 ≤ mu) (h7 : mu ≤ 7)
    (hd : dig c i < mu) (acc : List Val) (v : Val) (t : MachineState) (ht : PreHash c i acc mu v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = addrFmt (chainInputP c.lay c.tau c.e i mu (witPad c.wl c.lay i) v) ∧
      ∀ a, (mu < 7 → StepInv c i acc (mu + 1) (answerBytes 16 a) (writeHash t a)) ∧
        (mu = 7 → EndInv c i (acc ++ [answerBytes 16 a]) (writeHash t a)) := by
  obtain ⟨hB, h25, hF, hwP, t0, t1, hv0, hv1, hvl, t10, t12, tpc, -⟩ := ht
  obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
  have hlay := hc.1
  have hB8 : blkN c.lay i % 8 = 0 := blkN_mod8 _ _
  have hBr : 4992 ≤ blkN c.lay i ∧ blkN c.lay i + 256 < 2 ^ 24 := by rw [blkN_eq]; omega
  have t11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK _ chK0_x11
  refine ⟨hK _ chK0_x5, ?_, ?_, ?_⟩
  · have hdl : (if mu = 7 then slotA i else blkN c.lay i + 48) % 8 = 0 ∧
        (if mu = 7 then slotA i else blkN c.lay i + 48) + 32 ≤ 2 ^ 24 := by
      by_cases h : mu = 7
      · rw [if_pos h]; unfold slotA; omega
      · rw [if_neg h]; omega
    exact hashArgs_ofNat _ _ _ _ t10 t11 t12 (by omega) (by omega) (by omega)
      (hashArgsB_ok _ _ hB8 (by omega) hdl.1 hdl.2)
  · exact chain_hashInput c hc i mu hi h1 h7 v hvl t t10 t11 t0 t1 hwP hv0 hv1
  · intro a
    have gk12 : ∀ q ∈ gkL, q.1 ≠ .x12 := by decide
    have hK' : KnownOK chK0 (writeHash t a) := Known_writeHash hK a
    have hR' : c.Regs (writeHash t a) := by simp only [CCtx.Regs, writeHash_getReg]; exact hR
    refine ⟨fun hmu => ?_, fun hmu => ?_⟩
    · -- the next rung
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (blkN c.lay i + 48) := by rw [t12, if_neg (by omega)]
      have wfr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ blkN c.lay i + 48 ∨ blkN c.lay i + 48 + 32 ≤ A) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
        fun A hA h => writeHash_frame t a _ A d12 hA (by omega) h
      refine ⟨⟨Glob_frameC hG (fun q _ => writeHash_getReg _ _ _) (fun A hA => wfr A (by omega) (Or.inl (by omega))),
        hK', hR', by rw [writeHash_getReg]; exact h22, by rw [writeHash_getReg]; exact h27,
        by rw [writeHash_getReg]; exact h1r,
        LBOk_frame hLB (fun j hj => ⟨wfr _ (by omega) (Or.inl (by rw [hlen] at hj; omega)),
          wfr _ (by omega) (Or.inl (by rw [hlen] at hj; omega))⟩), hlen, hvs,
        by unfold CB0; rw [wfr _ (by omega) (Or.inl (by omega))]; exact hCB⟩,
        trivial, ?_, fun k hk hk' => ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, by simp,
        by rw [writeHash_getReg]; exact t10, by rw [writeHash_getReg]; exact d12, ?_⟩
      · intro a' b' k hw
        obtain ⟨n1, n2, n3⟩ := fresh_disj hw hi
        rw [wfr _ (by rw [blkN_eq]; obtain ⟨ha5, hb42, hk8, -⟩ := hw; omega) n3]
        exact hF a' b' k hw
      · rw [wfr _ (by omega) (Or.inl (by omega))]; exact hwP k hk hk'
      · rw [wfr _ (by omega) (Or.inl (by omega)), t0, BitVec.toNat_ofNat]; unfold newTwW0; simp only [blkN_eq, Nat.reducePow]; omega
      · rw [wfr _ (by omega) (Or.inl (by omega)), t0, BitVec.toNat_ofNat]
        have hb := newTwW0_lt40 c.lay i (mu - 1) (by omega) hi (by omega)
        rw [Nat.mod_eq_of_lt (lt_trans hb (by norm_num : 2 ^ 40 < 2 ^ 64)), Nat.div_eq_of_lt hb]
      · rw [wfr _ (by omega) (Or.inl (by omega))]; exact t1
      · rw [writeHash_at0 _ a _ d12 (by omega)]; exact (vw0_answer a).symm
      · rw [show blkN c.lay i + 56 = blkN c.lay i + 48 + 8 by omega, writeHash_at8 _ a _ d12 (by omega)]
        exact (vw1_answer a).symm
      · rw [writeHash_pc, tpc, rungPc_succ c i mu h1 hd, if_neg (by omega), pcOf_add4]
    · -- the chain's end: the answer is in the leaf-pk slot `i`
      subst hmu
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slotA i) := by rw [t12, if_pos rfl]
      have wfr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ slotA i ∨ slotA i + 32 ≤ A) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) :=
        fun A hA h => writeHash_frame t a _ A d12 hA (by unfold slotA; omega) h
      refine ⟨⟨Glob_writeHash hG a _ d12 (safeDest_slot i hi),
        hK', hR', by rw [writeHash_getReg]; exact h22, by rw [writeHash_getReg]; exact h27,
        by rw [writeHash_getReg]; exact h1r, ?_, by simp [hlen], ?_,
        by unfold CB0; rw [wfr _ (by omega) (Or.inl (by unfold slotA; omega))]; exact hCB⟩,
        trivial,
        ?_, ?_⟩
      · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
        · rw [hlen] at hj
          unfold slotA at wfr
          exact ⟨wfr _ (by omega) (Or.inl (by omega)), wfr _ (by omega) (Or.inl (by omega))⟩
        · rw [hlen, show 0x360 + 16 * i = slotA i from rfl, writeHash_at0 _ a _ d12 (by unfold slotA; omega)]
          exact (vw0_answer a).symm
        · rw [hlen, show 0x368 + 16 * i = slotA i + 8 by unfold slotA; omega,
            writeHash_at8 _ a _ d12 (by unfold slotA; omega)]
          exact (vw1_answer a).symm
      · intro w hw
        rcases List.mem_append.mp hw with h | h
        · exact hvs w h
        · rw [List.mem_singleton.mp h]; simp
      · intro a' b' k hw
        rw [wfr _ (by rw [blkN_eq]; obtain ⟨ha5, hb42, hk8, -⟩ := hw; omega)
          (Or.inr (by unfold slotA; rw [blkN_eq]; omega))]
        exact hF a' b' k hw
      · rw [writeHash_pc, tpc, if_pos rfl, ← rungPc_end c i (by omega), pcOf_add4]

/-- Rung `mu ≥ dig + 2` of chain `i` (after the previous step's hash): its `sb` (and `li a2`). -/
theorem rung_step (c : CCtx) (hc : c.ok) (i mu p : Nat) (hi : i < 42) (h1 : 1 ≤ mu) (h7 : mu ≤ 7)
    (hchk : rungCheck i mu p = true) (hp : rungPc c i mu = p) (acc : List Val)
    (v : Val) (s : MachineState) (hs : StepInv c i acc mu v s) :
    ∃ t, Steps image s (if mu = 7 then 2 else 1) (if mu = 7 then 2 else 1) t ∧ PreHash c i acc mu v t := by
  have hrun := optBeq_eq hchk
  obtain ⟨hB, h25, hF, hP, hT, hv0, hv1, hvl, h10, h12, hpc⟩ := hs
  obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
  have hlay := hc.1
  set B := blkN c.lay i with hBdef
  have hB8 : B % 8 = 0 := blkN_mod8 _ _
  have hBr : 4992 ≤ B ∧ B + 256 < 2 ^ 24 := by simp only [hBdef, blkN_eq, Nat.reducePow]; omega
  have hobl : ∀ o ∈ (rungExp i mu p).st.obl, o.holds s := by
    simp only [rungExp, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 4⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      have := valid_of B 4 1 (by omega) (by omega) (by omega)
      show accessValid (BitVec.ofNat 64 B + BitVec.ofNat 64 4) 1 = true
      rw [BitVec.ofNat_add_ofNat]; simpa using this
  obtain ⟨hst, hec⟩ := crun hrun s (by rw [hpc, hp]) hK hobl (by simp [rungExp])
  set t := (rungExp i mu p).toState s with ht
  have treg : ∀ x, x ≠ .x12 → t.getReg x = s.getReg x := by
    intro x hx; rw [ht, PRes.toState_getReg]; simp only [rungExp]; split
    · rw [RegFile.get_set_ne _ _ hx, known_eval hK]
    · rw [known_eval hK]
  have t12 : t.getReg .x12 = BitVec.ofNat 64 (if mu = 7 then slotA i else B + 48) := by
    rw [ht, PRes.toState_getReg]
    by_cases h : mu = 7
    · simp only [rungExp, if_pos h]; rw [RegFile.get_set_self _ _ (by decide)]; rfl
    · simp only [rungExp, if_neg h]; rw [known_eval hK, h12]
  have tmem : ∀ A, t.getMem A = if A = BitVec.ofNat 64 B then
      StoreKind.merge .b (s.getMem (BitVec.ofNat 64 B)) 4 (BitVec.ofNat 64 (mu - 1)) else s.getMem A := by
    intro A
    rw [ht, PRes.toState_getMem]
    show memEval s [(⟨some (.reg .x10), 0⟩, .bin (.st .b 4) (.ld (.reg .x10)) (posE (mu - 1)))] A = _
    rw [memEval_cons]
    simp only [Addr.eval, E.eval, BinOp.eval, h10, posE, BitVec.add_zero]
    simp [memEval]
  have tfr : ∀ A, A < 2 ^ 64 → A ≠ B → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hne; rw [tmem, if_neg (fun h => hne ((ofNat_eq_iff hA (by omega)).mp h))]
  have gk12 : ∀ q ∈ gkL, q.1 ≠ .x12 := by decide
  have ck12 : ∀ q ∈ chK0, q.1 ≠ .x12 := by decide
  refine ⟨t, by rw [show (rungExp i mu p).steps = (if mu = 7 then 2 else 1) by simp [rungExp],
      show (rungExp i mu p).cycles = (if mu = 7 then 2 else 1) by simp [rungExp]] at hst; exact hst,
    ⟨⟨Glob_frameC hG (fun q hq => treg _ (gk12 q hq)) (fun A hA => tfr A (by omega) (by omega)),
      fun q hq => (treg _ (ck12 q hq)).trans (hK q hq), ?_, (treg _ (by decide)).trans h22,
      (treg _ (by decide)).trans h27, (treg _ (by decide)).trans h1r,
      LBOk_frame hLB (fun j hj => ⟨tfr _ (by omega) (by rw [hlen] at hj; omega),
        tfr _ (by omega) (by rw [hlen] at hj; omega)⟩), hlen, hvs,
        by unfold CB0; rw [tfr _ (by omega) (by omega)]; exact hCB⟩,
      trivial, ?_, fun k hk hk' => by rw [tfr _ (by omega) (by omega)]; exact hP k hk hk',
      ?_, (tfr _ (by omega) (by omega)).trans hT.2.2, (tfr _ (by omega) (by omega)).trans hv0,
      (tfr _ (by omega) (by omega)).trans hv1, hvl, (treg _ (by decide)).trans h10, t12, ?_, hec rfl⟩⟩
  · obtain ⟨r1, r2, r3, r4, r5⟩ := hR
    exact ⟨(treg _ (by decide)).trans r1, (treg _ (by decide)).trans r2, (treg _ (by decide)).trans r3,
      (treg _ (by decide)).trans r4, (treg _ (by decide)).trans r5⟩
  · intro a' b' k hw
    obtain ⟨n1, -, -⟩ := fresh_disj hw hi
    rw [tfr _ (by rw [blkN_eq]; obtain ⟨ha5, hb42, hk8, -⟩ := hw; omega) n1]
    exact hF a' b' k hw
  · rw [tmem, if_pos rfl]
    apply BitVec.eq_of_toNat_eq
    rw [stepByte_toNat _ _ _ _ hlay hi (by omega) hT.1 hT.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    unfold newTwW0; simp only [blkN_eq, Nat.reducePow]; omega
  · rw [PRes.toState_pc _ _ (by simp [rungExp]), hp]; rfl


theorem twW0_word (lay i : Nat) (hl : lay < 5) (hi : i < 42) :
    (BitVec.ofNat 64 (twW0 lay i)).toNat % 2 ^ 32 = hWord lay ∧
      (BitVec.ofNat 64 (twW0 lay i)).toNat / 2 ^ 40 = i := by
  rw [BitVec.toNat_ofNat]; unfold twW0 hWord; constructor <;> omega

theorem twW0_bump (lay i : Nat) (hl : lay < 5) (hi : i < 42) :
    BitVec.ofNat 64 (twW0 lay i) - K40 + K40 = BitVec.ofNat 64 (twW0 lay i) := by
  rw [BitVec.sub_add_cancel]

theorem K40_eq : K40 = BitVec.ofNat 64 (2 ^ 40) := rfl

theorem twW0_succ (lay i : Nat) (hl : lay < 5) (hi : i < 42) :
    BitVec.ofNat 64 (twW0 lay (i + 1)) - K40 = BitVec.ofNat 64 (twW0 lay i) := by
  rw [K40_eq, show twW0 lay (i + 1) = twW0 lay i + 2 ^ 40 by unfold twW0; ring,
    ← BitVec.ofNat_add_ofNat, BitVec.add_sub_cancel]

/-- The head of chain `i` (digit `d < 7`) with its first rung `d + 1`, from the chain's start. -/
theorem head_step (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (hd : dig c i < 7) (acc : List Val)
    (hrun : runAt chK0 [] (startPc c i) [] =
      some (headExp i (dig c i) (rungPc c i (dig c i + 1)) (decide (i % 3 = 0))))
    (s : MachineState) (hs : ChainIn c i acc s) :
    ∃ t, Steps image s (4 + (if i % 3 = 0 then 1 else 0) + (if dig c i = 6 then 2 else 1))
        (4 + (if i % 3 = 0 then 1 else 0) + (if dig c i = 6 then 2 else 1)) t ∧
      PreHash c i acc (dig c i + 1) (witChain c.wl c.lay i) t := by
  obtain ⟨hB, h25, hF, hpc⟩ := hs
  obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
  have hlay := hc.1
  set d := dig c i with hdd
  set B := blkN c.lay i with hBdef
  have hB8 : B % 8 = 0 := blkN_mod8 _ _
  have hBr : 4992 ≤ B ∧ B + 256 < 2 ^ 24 := by simp only [hBdef, blkN_eq, Nat.reducePow]; omega
  have bke : ∀ k, k < 2 ^ 20 → (bk i k).eval s = BitVec.ofNat 64 (B + k) := fun k hk =>
    bk_eval s c.lay i k h22 hlay hi hk
  set r := headExp i d (rungPc c i (d + 1)) (decide (i % 3 = 0)) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headExp, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl | rfl)
    · show ((E.reg .x22).eval s).toNat % 8 = 0
      simp only [E.eval, h22, BitVec.toNat_ofNat]; have := s6N_mod8 c.lay; rw [s6N_eq] at this ⊢; omega
    · show accessValid ((bk i 4).eval s) 1 = true
      rw [bke 4 (by omega)]; have := valid_of B 4 1 (by omega) (by omega) (by omega); simpa using this
    · show accessValid ((bk i 8).eval s) 8 = true
      rw [bke 8 (by omega)]; have := valid_of B 8 8 (by omega) (by omega) (by omega); simpa using this
    · show accessValid ((bk i 0).eval s) 8 = true
      rw [bke 0 (by omega)]; have := valid_of B 0 8 (by omega) (by omega) (by omega); simpa using this
  obtain ⟨hst, hec⟩ := crun hrun s hpc hK hobl (by simp [hr, headExp])
  set t := r.toState s with ht
  have a0e : (addC (.reg .x22) (offW i)).eval s = BitVec.ofNat 64 B := by
    have := bke 0 (by omega); unfold bk at this; rw [norm_eval] at this
    rw [addC_eval] at this ⊢; simpa using this
  have treg : ∀ x, x ≠ .x10 → x ≠ .x12 → x ≠ .x25 → t.getReg x = s.getReg x := by
    intro x h1 h2 h3; rw [ht, PRes.toState_getReg]; simp only [hr, headExp]
    rw [RegFile.get_set_ne _ _ h2, RegFile.get_set_ne _ _ h1, known_eval hK]
  have t10 : t.getReg .x10 = BitVec.ofNat 64 B := by
    rw [ht, PRes.toState_getReg]; simp only [hr, headExp]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
  have t12 : t.getReg .x12 = BitVec.ofNat 64 (if d + 1 = 7 then slotA i else B + 48) := by
    rw [ht, PRes.toState_getReg]; simp only [hr, headExp]
    rw [RegFile.get_set_self _ _ (by decide)]
    by_cases h6 : d = 6
    · rw [if_pos h6, if_pos (by omega)]; rfl
    · rw [if_neg h6, if_neg (by omega), addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl,
        BitVec.ofNat_add_ofNat]
  have t25 : True := trivial
  have tmem : ∀ A, t.getMem A = if A = BitVec.ofNat 64 B then
      StoreKind.merge .b (BitVec.ofNat 64 B) 4 (BitVec.ofNat 64 d)
      else if A = BitVec.ofNat 64 (B + 8) then c.x31 else s.getMem A := by
    intro A
    rw [ht, PRes.toState_getMem]
    show memEval s [(bk i 0, .bin (.st .b 4) (addC (.reg .x22) (offW i)) (posE d)), (bk i 8, .reg .x31)] A = _
    rw [memEval_cons, memEval_cons, bke 0 (by omega), bke 8 (by omega)]
    simp only [E.eval, BinOp.eval, posE, Nat.add_zero, a0e, hR.2.2.2.2]
    rfl
  have tfr : ∀ A, A < 2 ^ 64 → A ≠ B → A ≠ B + 8 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [tmem, if_neg (fun h => h1 ((ofNat_eq_iff hA (by omega)).mp h)),
      if_neg (fun h => h2 ((ofNat_eq_iff hA (by omega)).mp h))]
  have gk : ∀ q ∈ gkL, q.1 ≠ .x10 ∧ q.1 ≠ .x12 ∧ q.1 ≠ .x25 := by decide
  have ck : ∀ q ∈ chK0, q.1 ≠ .x10 ∧ q.1 ≠ .x12 ∧ q.1 ≠ .x25 := by decide
  have fr6 : ∀ k, 2 ≤ k → k < 8 → t.getMem (BitVec.ofNat 64 (B + 8 * k)) =
      w64 (slice c.wl (blockOff c.lay i + 8 * k) 8) := fun k hk hk' => by
    rw [tfr _ (by omega) (by omega) (by omega)]; exact hF _ _ _ (FreshW_own hlay hi hk hk')
  have hn : r.steps = 4 + (if i % 3 = 0 then 1 else 0) + (if d = 6 then 2 else 1) ∧ r.cycles = r.steps := by
    refine ⟨?_, rfl⟩
    simp only [hr, headExp]; by_cases h : i % 3 = 0 <;> simp [h]
  refine ⟨t, by rw [hn.2, hn.1] at hst; exact hst,
    ⟨⟨Glob_frameC hG (fun q hq => treg _ (gk q hq).1 (gk q hq).2.1 (gk q hq).2.2)
        (fun A hA => tfr A (by omega) (by omega) (by omega)),
      fun q hq => (treg _ (ck q hq).1 (ck q hq).2.1 (ck q hq).2.2).trans (hK q hq), ?_,
      (treg _ (by decide) (by decide) (by decide)).trans h22,
      (treg _ (by decide) (by decide) (by decide)).trans h27, (treg _ (by decide) (by decide) (by decide)).trans h1r,
      LBOk_frame hLB (fun j hj => ⟨tfr _ (by omega) (by rw [hlen] at hj; omega) (by rw [hlen] at hj; omega),
        tfr _ (by omega) (by rw [hlen] at hj; omega) (by rw [hlen] at hj; omega)⟩), hlen, hvs,
        by unfold CB0; rw [tfr _ (by omega) (by omega) (by omega)]; exact hCB⟩,
      t25, ?_, fun k hk hk' => fr6 k hk (by omega), ?_, ?_, ?_, ?_, length_witChain c hc i hi, t10, t12, ?_,
      hec rfl⟩⟩
  · obtain ⟨r1, r2, r3, r4, r5⟩ := hR
    exact ⟨(treg _ (by decide) (by decide) (by decide)).trans r1, (treg _ (by decide) (by decide) (by decide)).trans r2,
      (treg _ (by decide) (by decide) (by decide)).trans r3, (treg _ (by decide) (by decide) (by decide)).trans r4,
      (treg _ (by decide) (by decide) (by decide)).trans r5⟩
  · intro a' b' k hw
    obtain ⟨n1, n2, -⟩ := fresh_disj hw hi
    rw [tfr _ (by rw [blkN_eq]; obtain ⟨ha5, hb42, hk8, -⟩ := hw; omega) n1 n2]
    exact hF a' b' k (FreshW_next hw)
  · rw [tmem, if_pos rfl]
    apply BitVec.eq_of_toNat_eq
    have w1 : (BitVec.ofNat 64 B).toNat % 2 ^ 32 = blkN c.lay i := by
      simp only [BitVec.toNat_ofNat]; simp only [hBdef, blkN_eq, Nat.reducePow]; omega
    have w2 : (BitVec.ofNat 64 B).toNat / 2 ^ 40 = 0 := by
      have hb : B < 2 ^ 24 := by omega
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hb (by norm_num : 2 ^ 24 < 2 ^ 64)),
        Nat.div_eq_of_lt (lt_trans hb (by norm_num : 2 ^ 24 < 2 ^ 40))]
    rw [stepByte_toNat _ _ _ _ hlay hi (dig_lt c i) w1 w2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    · congr 1
    · unfold newTwW0; simp only [blkN_eq, Nat.reducePow]; omega
  · rw [tmem, if_neg (fun h => by have := (ofNat_eq_iff (by omega) (by omega)).mp h; omega), if_pos rfl]
  · rw [fr6 6 (by omega) (by omega), witChain, vw0_slice]
  · rw [fr6 7 (by omega) (by omega), witChain, vw1_slice]
  · rw [PRes.toState_pc _ _ (by simp [hr, headExp])]; simp only [hr, headExp, rungEnd]

/-- The digit-7 copy of chain `i`: its witness value into the leaf-pk slot. -/
theorem copy_step (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (hd : dig c i = 7) (acc : List Val)
    (hrun : runAt chK0 [endPc c i] (startPc c i) [] = some (copyExp i (endPc c i) (decide (i % 3 = 0))))
    (s : MachineState) (hs : ChainIn c i acc s) :
    ∃ t, Steps image s (4 + (if i % 3 = 0 then 1 else 0)) (4 + (if i % 3 = 0 then 1 else 0)) t ∧
      EndInv c i (acc ++ [witChain c.wl c.lay i]) t := by
  obtain ⟨hB, h25, hF, hpc⟩ := hs
  obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
  have hlay := hc.1
  set B := blkN c.lay i with hBdef
  have hBr : 4992 ≤ B ∧ B + 256 < 2 ^ 24 := by simp only [hBdef, blkN_eq, Nat.reducePow]; omega
  have bke : ∀ k, k < 2 ^ 20 → (bk i k).eval s = BitVec.ofNat 64 (B + k) := fun k hk =>
    bk_eval s c.lay i k h22 hlay hi hk
  set r := copyExp i (endPc c i) (decide (i % 3 = 0)) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, copyExp, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show accessValid ((bk i 56).eval s) 8 = true
      rw [bke 56 (by omega)]; have := valid_of B 56 8 (by omega) (by omega) (by simp only [hBdef, blkN_eq, Nat.reducePow]; omega)
      simpa using this
    · show accessValid ((bk i 48).eval s) 8 = true
      rw [bke 48 (by omega)]; have := valid_of B 48 8 (by omega) (by omega) (by simp only [hBdef, blkN_eq, Nat.reducePow]; omega)
      simpa using this
  obtain ⟨hst, -⟩ := crun hrun s hpc hK hobl (by simp [hr, copyExp])
  set t := r.toState s with ht
  have treg : ∀ x, x ≠ .x3 → x ≠ .x14 → x ≠ .x25 → t.getReg x = s.getReg x := by
    intro x h1 h2 h3; rw [ht, PRes.toState_getReg]; simp only [hr, copyExp]
    rw [RegFile.get_set_ne _ _ h2, RegFile.get_set_ne _ _ h1, known_eval hK]
  have ldv : ∀ k, k = 48 ∨ k = 56 → (ldK i k).eval s = s.getMem (BitVec.ofNat 64 (B + k)) := fun k hk =>
    ldK_eval s c.lay i k h22 hlay hi (by omega)
  have tmem : ∀ A, t.getMem A = if A = BitVec.ofNat 64 (slotA i + 8) then s.getMem (BitVec.ofNat 64 (B + 56))
      else if A = BitVec.ofNat 64 (slotA i) then s.getMem (BitVec.ofNat 64 (B + 48)) else s.getMem A := by
    intro A
    rw [ht, PRes.toState_getMem]
    show memEval s [(⟨none, BitVec.ofNat 64 (slotA i + 8)⟩, ldK i 56), (⟨none, BitVec.ofNat 64 (slotA i)⟩, ldK i 48)] A = _
    rw [memEval_cons, memEval_cons, ldv 56 (by omega), ldv 48 (by omega)]
    simp only [Addr.eval]; rfl
  have hsl : slotA i + 16 ≤ 0x800 := by unfold slotA; omega
  have tfr : ∀ A, A < 2 ^ 64 → A ≠ slotA i → A ≠ slotA i + 8 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [tmem, if_neg (fun h => h2 ((ofNat_eq_iff hA (by omega)).mp h)),
      if_neg (fun h => h1 ((ofNat_eq_iff hA (by omega)).mp h))]
  have gk : ∀ q ∈ gkL, q.1 ≠ .x3 ∧ q.1 ≠ .x14 ∧ q.1 ≠ .x25 := by decide
  have ck : ∀ q ∈ chK0, q.1 ≠ .x3 ∧ q.1 ≠ .x14 ∧ q.1 ≠ .x25 := by decide
  have fr : ∀ k, 6 ≤ k → k < 8 → s.getMem (BitVec.ofNat 64 (B + 8 * k)) =
      w64 (slice c.wl (blockOff c.lay i + 8 * k) 8) := fun k hk hk' =>
    hF _ _ _ (FreshW_own hlay hi (by omega) hk')
  have hn : r.steps = 4 + (if i % 3 = 0 then 1 else 0) ∧ r.cycles = r.steps := by
    refine ⟨?_, rfl⟩
    simp only [hr, copyExp]; by_cases h : i % 3 = 0 <;> simp [h]
  have hGt : Glob gkL c.wl c.pk t :=
    Glob_frameS hG (fun q hq => treg _ (gk q hq).1 (gk q hq).2.1 (gk q hq).2.2) (fun A hA hp => by
      have hs1 : A ≠ slotA i ∧ A ≠ slotA i + 8 := by
        unfold slotA; rcases hp with hp | hp | hp | hp
        · simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at hp; omega
        all_goals omega
      exact tfr A (by omega) hs1.1 hs1.2)
  refine ⟨t, by rw [hn.2, hn.1] at hst; exact hst,
    ⟨hGt, fun q hq => (treg _ (ck q hq).1 (ck q hq).2.1 (ck q hq).2.2).trans (hK q hq), ?_,
      (treg _ (by decide) (by decide) (by decide)).trans h22,
      (treg _ (by decide) (by decide) (by decide)).trans h27, (treg _ (by decide) (by decide) (by decide)).trans h1r,
      ?_, by simp [hlen], ?_,
      by unfold CB0; rw [tfr _ (by omega) (by unfold slotA; omega) (by unfold slotA; omega)]; exact hCB⟩,
      ?_, ?_, ?_⟩
  · obtain ⟨r1, r2, r3, r4, r5⟩ := hR
    exact ⟨(treg _ (by decide) (by decide) (by decide)).trans r1, (treg _ (by decide) (by decide) (by decide)).trans r2,
      (treg _ (by decide) (by decide) (by decide)).trans r3, (treg _ (by decide) (by decide) (by decide)).trans r4,
      (treg _ (by decide) (by decide) (by decide)).trans r5⟩
  · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
    · rw [hlen] at hj
      unfold slotA at tfr
      exact ⟨tfr _ (by omega) (by omega) (by omega), tfr _ (by omega) (by omega) (by omega)⟩
    · rw [hlen, show 0x360 + 16 * i = slotA i from rfl, tmem,
        if_neg (fun h => by have := (ofNat_eq_iff (by omega) (by omega)).mp h; omega), if_pos rfl,
        show B + 48 = B + 8 * 6 by omega, fr 6 (by omega) (by omega), witChain, vw0_slice]
    · rw [hlen, show 0x368 + 16 * i = slotA i + 8 by unfold slotA; omega, tmem, if_pos rfl,
        show B + 56 = B + 8 * 7 by omega, fr 7 (by omega) (by omega), witChain, vw1_slice]
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hvs w h
    · rw [List.mem_singleton.mp h]; exact length_witChain c hc i hi
  · trivial
  · intro a' b' k hw
    rw [tfr _ (by rw [blkN_eq]; obtain ⟨ha5, hb42, hk8, -⟩ := hw; omega)
      (by unfold slotA; rw [blkN_eq]; omega) (by unfold slotA; rw [blkN_eq]; omega)]
    exact hF a' b' k (FreshW_next hw)
  · rw [PRes.toState_pc _ _ (by simp [hr, copyExp])]; rfl


/-! ## The triple dispatch -/

theorem land_tmask (n : Nat) : n &&& 0x3fe00 = 512 * (n / 512 % 512) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and]
  rw [show 512 * (n / 512 % 512) = (n >>> 9 % 2 ^ 9) <<< 9 by
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega]
  rw [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < 18
  · interval_cases j <;> simp <;> intro _ <;> decide
  · rw [Nat.testBit_lt_two_pow (show 0x3fe00 < 2 ^ j from
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 18 ≤ j by omega)))]
    simp; omega

theorem even_andNot1 (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]

/-- The digit word of triple `t` and its table row. -/
def triW (c : CCtx) (t : Nat) : Word := if t < 7 then c.d0 else c.d1

theorem PRes.toState_pc_some (r : PRes) (s : MachineState) (e : E) (h : r.spc = some e) :
    (r.toState s).pc = e.eval s := by
  simp [PRes.toState, PRes.finalPc, h]

theorem tri_lo (D : Nat) : (D * 512 % 2 ^ 64) &&& 0x3fe00 = 512 * (D % 512) := by
  rw [land_tmask, show (2:Nat) ^ 64 = 2 ^ 55 * 512 by norm_num, Nat.mul_mod_mul_right,
    Nat.mul_div_cancel _ (by norm_num), Nat.mod_mod_of_dvd _ (by norm_num)]

theorem tri_hi (D k : Nat) : (D / 2 ^ k) &&& 0x3fe00 = 512 * (D / 2 ^ (k + 9) % 512) := by
  rw [land_tmask, Nat.div_div_eq_div_mul, show 2 ^ k * 512 = 2 ^ (k + 9) by rw [Nat.pow_add]]

theorem TMASK_toNat : TMASK.toNat = 0x3fe00 := rfl
theorem TTA5_toNat : TTA5.toNat = 0x50000 := rfl

theorem tri_fin (Y : Word) (X : Nat) (h : Y.toNat &&& 0x3fe00 = 512 * X) (hX : X < 512) :
    (Y &&& TMASK) + TTA5 = BitVec.ofNat 64 (0x50000 + 512 * X) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_and, TMASK_toNat, TTA5_toNat, h, Nat.mod_eq_of_lt (by omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem tri_case0 (D : Word) :
    (D <<< ((BitVec.ofNat 64 9).toNat % 64) &&& TMASK) + TTA5 =
      BitVec.ofNat 64 (0x50000 + 512 * (D.toNat % 512)) := by
  apply tri_fin _ _ _ (Nat.mod_lt _ (by norm_num))
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [show 9 % 2 ^ 64 % 64 = 9 by norm_num, Nat.shiftLeft_eq, tri_lo]

theorem tri_case1 (D : Word) :
    ((D + 0) &&& TMASK) + TTA5 = BitVec.ofNat 64 (0x50000 + 512 * (D.toNat / 512 % 512)) := by
  apply tri_fin _ _ _ (Nat.mod_lt _ (by norm_num))
  rw [show D + 0 = D from BitVec.add_zero D, land_tmask]

theorem tri_case2 (D : Word) (k : Nat) (hk : k < 64) :
    (D >>> ((BitVec.ofNat 64 k).toNat % 64) &&& TMASK) + TTA5 =
      BitVec.ofNat 64 (0x50000 + 512 * (D.toNat / 2 ^ (k + 9) % 512)) := by
  apply tri_fin _ _ _ (Nat.mod_lt _ (by norm_num))
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow, tri_hi]

theorem triX_evalN (t : Nat) (s : MachineState) (D : Word) (w : Reg) (hDw : s.getReg w = D) :
    (let sh := 9 * (t % 7)
     let e0 : E := if sh < 9 then mkBin .sll (.reg w) (cw (9 - sh))
       else if 9 < sh then mkBin .srl (.reg w) (cw (sh - 9)) else addC (.reg w) 0
     mkAdd (mkBin .and e0 (.c TMASK)) (.c TTA5)).eval s =
      BitVec.ofNat 64 (0x50000 + 512 * (D.toNat / 2 ^ (9 * (t % 7)) % 512)) := by
  simp only []
  have hm7 : t % 7 < 7 := Nat.mod_lt _ (by norm_num)
  generalize t % 7 = m at hm7 ⊢
  rw [mkAdd_eval, mkBin_eval]
  simp only [E.eval, BinOp.eval]
  rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
  · rw [if_pos (by omega), mkBin_eval]
    simp only [E.eval, BinOp.eval, cw, hDw]
    rw [show 9 - 9 * 0 = 9 from rfl, tri_case0, show 9 * 0 = 0 from rfl, Nat.pow_zero, Nat.div_one]
  · rw [if_neg (by omega), if_neg (by omega), addC_eval]
    simp only [E.eval, hDw]
    rw [tri_case1]; rfl
  · rw [if_neg (by omega), if_pos (by omega), mkBin_eval]
    simp only [E.eval, BinOp.eval, cw, hDw]
    rw [tri_case2 D _ (by omega), show 9 * m - 9 + 9 = 9 * m by omega]

theorem triX_eval (c : CCtx) (t : Nat) (s : MachineState) (hR : c.Regs s) :
    (triX t).eval s = BitVec.ofNat 64 (0x50000 + 512 * ((triW c t).toNat / 2 ^ (9 * (t % 7)) % 512)) := by
  have hDw : s.getReg (if t < 7 then Reg.x16 else Reg.x17) = triW c t := by
    unfold triW; split
    · exact hR.1
    · exact hR.2.1
  exact triX_evalN t s _ _ hDw

/-- The row of triple `t` from its digit word. -/
theorem triRow (c : CCtx) (t : Nat) (ht : t < 14) :
    (triW c t).toNat / 2 ^ (9 * (t % 7)) % 512 = kOf c t := by
  unfold kOf dig triW
  have h1 : 3 * t < 21 ↔ t < 7 := by omega
  have e0 : (3 * t) % 21 = 3 * (t % 7) := by omega
  have e1 : (3 * t + 1) % 21 = 3 * (t % 7) + 1 := by omega
  have e2 : (3 * t + 2) % 21 = 3 * (t % 7) + 2 := by omega
  rw [e0, e1, e2]
  have c1 : (3 * t + 1 < 21) = (t < 7) := by apply propext; omega
  have c2 : (3 * t + 2 < 21) = (t < 7) := by apply propext; omega
  have c0 : (3 * t < 21) = (t < 7) := by apply propext; omega
  simp only [c0, c1, c2]
  generalize (if t < 7 then c.d0 else c.d1).toNat = D
  rw [show (8 : Nat) ^ (3 * (t % 7)) = 2 ^ (9 * (t % 7)) by rw [show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]; ring_nf,
    show (8 : Nat) ^ (3 * (t % 7) + 1) = 2 ^ (9 * (t % 7)) * 8 by rw [Nat.pow_succ, show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]; ring_nf,
    show (8 : Nat) ^ (3 * (t % 7) + 2) = 2 ^ (9 * (t % 7)) * 64 by rw [Nat.pow_succ, Nat.pow_succ, show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]; ring_nf,
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
  generalize D / 2 ^ (9 * (t % 7)) = X
  omega

theorem ttab_pc (t k : Nat) :
    0x50000 + 512 * k + (32 * t) - 2048 = 0x1000 + 4 * entW t k := by
  unfold entW; rw [show ttabIdx = 80384 from rfl]; omega

theorem triTgt_eval (c : CCtx) (hc : c.ok) (t : Nat) (ht : t < 14) (s : MachineState) (hR : c.Regs s) :
    (triTgt t).eval s = pcOf (entW t (kOf c t)) := by
  unfold triTgt
  rw [mkBin_eval, mkAdd_eval, triX_eval c t s hR, triRow c t ht]
  simp only [E.eval, BinOp.eval]
  have hk : kOf c t < 512 := by unfold kOf; have := dig_lt c (3 * t); have := dig_lt c (3 * t + 1); have := dig_lt c (3 * t + 2); omega
  have e : BitVec.ofNat 64 (0x50000 + 512 * kOf c t) + (BitVec.ofNat 64 (32 * t) - BitVec.ofNat 64 2048) =
      BitVec.ofNat 64 (0x1000 + 4 * entW t (kOf c t)) := by
    rw [← ttab_pc]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, even_andNot1 _ (by omega)]
  rfl

/-- After chain `C` of triple `t`: the dispatch of triple `t + 1` (or, after the last triple, the return). -/
theorem x_step (c : CCtx) (hc : c.ok) (t : Nat) (ht : t < 14) (acc : List Val)
    (hrun : runAt chK0 [] (tX c (3 * t + 2)) [.jmp] = some (xExp t))
    (hret : c.ret &&& ~~~1#64 = c.ret) (s : MachineState) (hs : EndInv c (3 * t + 2) acc s) :
    (t + 1 < 14 → ∃ u, Steps image s (xSteps t) (xSteps t) u ∧ ChainIn c (3 * t + 3) acc u) ∧
      (t = 13 → ∃ u, Steps image s 1 1 u ∧ ChBase c 42 acc u ∧ Fresh c.wl c.lay 42 u ∧ u.pc = c.ret) := by
  obtain ⟨hB, h25, hF, hpc⟩ := hs
  have hpc' : s.pc = pcOf (tX c (3 * t + 2)) := by
    rw [hpc]; unfold endPc; rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨hst, -⟩ := crun hrun s hpc' hB.2.1 (by simp [xExp]; split <;> simp) (by simp [xExp]; split <;> simp)
  have hRs := hB.2.2.1
  refine ⟨fun h1 => ?_, fun h13 => ?_⟩
  · have hx : xExp t = ⟨⟨(RegFile.withKnown chK0).set .x14 (triX (t + 1)), [], []⟩, 0, false, xSteps t, xSteps t, [],
        some (triTgt (t + 1))⟩ := by simp [xExp, h1]
    rw [hx] at hst
    set u := PRes.toState ⟨⟨(RegFile.withKnown chK0).set .x14 (triX (t + 1)), [], []⟩, 0, false, xSteps t, xSteps t, [],
        some (triTgt (t + 1))⟩ s with hu
    have ureg : ∀ x, x ≠ .x14 → u.getReg x = s.getReg x := by
      intro x hx; rw [hu, PRes.toState_getReg, RegFile.get_set_ne _ _ hx, known_eval hB.2.1]
    have umem : ∀ A, u.getMem A = s.getMem A := fun A => rfl
    obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
    have gk : ∀ q ∈ gkL, q.1 ≠ .x14 := by decide
    have ck : ∀ q ∈ chK0, q.1 ≠ .x14 := by decide
    refine ⟨u, hst, ⟨Glob_frameC hG (fun q hq => ureg _ (gk q hq)) (fun A _ => umem _),
      fun q hq => (ureg _ (ck q hq)).trans (hK q hq), ?_, (ureg _ (by decide)).trans h22,
      (ureg _ (by decide)).trans h27, (ureg _ (by decide)).trans h1r,
      LBOk_frame hLB (fun j _ => ⟨umem _, umem _⟩), by rw [hlen], hvs, by unfold CB0; rw [umem]; exact hCB⟩, ?_,
      fun a b k hw => (umem _).trans (hF a b k (by simpa using hw)), ?_⟩
    · obtain ⟨r1, r2, r3, r4, r5⟩ := hR
      exact ⟨(ureg _ (by decide)).trans r1, (ureg _ (by decide)).trans r2, (ureg _ (by decide)).trans r3,
        (ureg _ (by decide)).trans r4, (ureg _ (by decide)).trans r5⟩
    · trivial
    · rw [hu, PRes.toState_pc_some _ _ _ rfl, triTgt_eval c hc (t + 1) h1 s hRs]
      unfold startPc; rw [if_pos (by omega), show (3 * t + 3) / 3 = t + 1 by omega]
  · subst h13
    have hx : xExp 13 = ⟨⟨RegFile.withKnown chK0, [], []⟩, 0, false, 1, 1, [],
        some (mkBin .and (.reg .x1) (.c (~~~1#64)))⟩ := by simp [xExp]
    rw [hx] at hst
    set u := PRes.toState ⟨⟨RegFile.withKnown chK0, [], []⟩, 0, false, 1, 1, [],
        some (mkBin .and (.reg .x1) (.c (~~~1#64)))⟩ s with hu
    have ureg : ∀ x, u.getReg x = s.getReg x := by
      intro x; rw [hu, PRes.toState_getReg, known_eval hB.2.1]
    have umem : ∀ A, u.getMem A = s.getMem A := fun A => rfl
    obtain ⟨hG, hK, hR, h22, h27, h1r, hLB, hlen, hvs, hCB⟩ := hB
    refine ⟨u, hst, ⟨Glob_frameC hG (fun q _ => ureg _) (fun A _ => umem _), fun q hq => (ureg _).trans (hK q hq),
      ?_, (ureg _).trans h22, (ureg _).trans h27, (ureg _).trans h1r,
      LBOk_frame hLB (fun j _ => ⟨umem _, umem _⟩), by rw [hlen], hvs, by unfold CB0; rw [umem]; exact hCB⟩,
      fun a b k hw => (umem _).trans (hF a b k (by simpa using hw)), ?_⟩
    · obtain ⟨r1, r2, r3, r4, r5⟩ := hR
      exact ⟨(ureg _).trans r1, (ureg _).trans r2, (ureg _).trans r3, (ureg _).trans r4, (ureg _).trans r5⟩
    · rw [hu, PRes.toState_pc_some _ _ _ rfl]
      simp only [mkBin_eval, E.eval, BinOp.eval, h1r, hret]

end SigGolfCandidate.Verify
