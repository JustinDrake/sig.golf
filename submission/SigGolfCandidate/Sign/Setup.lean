import SigGolfCandidate.Sign.DigestPairs
import SigGolfCandidate.Sign.Mac
import SigGolfCandidate.Keygen.State

/-!
# `sign`: setup and the cache MAC check

* block 0 (0 .. 25): `S`, `m` into the buffers, then a jump to the MAC routine at 3034.
* 3034 .. 3160: the arithmetic MAC. Init, then three rounds: key query `i` (answer at `EO`), a pass per half
  of the answer (`MacPass.mac_pass_region`), each tag word XORed with the cached one into `s10`. The scratch
  words (`PB`, `PB + 8`, `EO .. EO + 32`) are zeroed again, then one branch on `s10`: the continuation at 63
  or `fail_mac` at 142.
* 63 .. 64: `LIM = 2^19`, then the randomizer packer at 2844 .. 2886; the digest loop starts at 65.

`mac_sim` : the machine refines the three key queries followed by `if macTag a0 a1 a2 region = cacheTag then
rest else pure none`, given a simulation of `rest` from the digest loop. The cache is not written.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

-- Memory effect of the setup block (kernel-checked with a variable state).
kernel_theorem blk0_pbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x6C0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x640) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbM : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x660) 4 = t.readWords (BitVec.ofNat 64 0x20) 4
kernel_theorem blk0_db0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0x0) = BitVec.ofNat 64 0
theorem blk0_rb0 (t : MachineState) :
    lo32 ((blk0.res.toState t).getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701 := by
  simp (config := { decide := true }) only [blk0.res, rv_simp, lo32_replace0, Nat.zero_div, ↓reduceIte]

/-- Addresses written by the setup block. -/
def setupW (a : Nat) : Prop :=
  a = 0x0 ∨ a = 0x620 ∨ (0x640 ≤ a ∧ a < 0x680) ∨ (0x6C0 ≤ a ∧ a < 0x6E0)

/-- Addresses written up to the digest loop (setup, the randomizer block). -/
def macW (a : Nat) : Prop :=
  setupW a ∨ (0x160 ≤ a ∧ a < 0x180) ∨ (0x780 ≤ a ∧ a < 0x7c0)

/-- Facts at the start of the digest loop. -/
structure MacOk (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState) : Prop where
  pc : u.pc = pcOf 65
  mem : DigMem (toList sk) (toList m) u
  x5 : u.getReg .x5 = 0
  x6 : u.getReg .x6 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 19)
  pbS : u.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk)
  frame : Frame (s0 sk cache m) u macW

theorem MacOk.inv {sk : SecretKey} {cache : Cache} {m : Message} {u : MachineState}
    (h : MacOk sk cache m u) : DigInv u 0 u :=
  ⟨h.pc, by rw [h.x6]; rfl, by norm_num, RegsEq.refl _ _, Frame.refl _ _, rfl⟩

theorem length_cacheRegion (cache : Cache) : (cacheRegion (toList cache)).length = 65504 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  simp [cacheRegion, slice, hlen, regionBytes]; decide

theorem cacheTag_eq (cache : Cache) : cacheTag (toList cache) = slice (toList cache) 65536 (8 * 6) := by
  unfold cacheTag; rw [regionBytes_eq]

theorem length_cacheTag (cache : Cache) : (cacheTag (toList cache)).length = 48 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  rw [cacheTag_eq]
  simp [slice, hlen]

theorem setup_frame (t : MachineState) : Frame t (blk0.res.toState t) setupW := by
  apply frame_toState; intro x hx hW
  simp only [blk0.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, ne_eq, ofNat_eq_iff]
  simp only [setupW] at hW
  omega

theorem setup_regs (t : MachineState) :
    RegsEq t (blk0.res.toState t) [.x1, .x3, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x29] := by
  intro r hr; rw [Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl

/-! ## Block specifications of the MAC routine -/

/-- Normalization of symbolic-block results (as `Keygen.kgn`). -/
macro "sgn" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, Keygen.ofNat_add_ofNat, Keygen.ofNat_shl', Keygen.ofNat_shr',
      Keygen.ofNat_eq_iff, BitVec.toNat_ofNat, accessValid_iff, MEMORY_BYTES, ne_eq, bne_iff_ne,
      decide_eq_true_eq, ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd,
      Nat.reduceMul, Nat.reducePow, Keygen.ofNat_shl, $ts',*])

/-- MAC init: `s2 = 2^61 - 1`, `s3 = s9 = CACHE + 65536`, `s5 = 0`, `s10 = 0`, word 0 of `tw_mackey`
at `PB`. -/
theorem spec3044 (s : MachineState) (hpc : s.pc = pcOf 3044) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = pcOf 3054 ∧
      t.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1) ∧ t.getReg .x19 = BitVec.ofNat 64 0x14B00 ∧
      t.getReg .x25 = BitVec.ofNat 64 0x14B00 ∧ t.getReg .x21 = BitVec.ofNat 64 0 ∧
      t.getReg .x26 = 0 ∧
      (∀ r, r ≠ .x18 → r ≠ .x19 → r ≠ .x25 → r ≠ .x21 → r ≠ .x26 → r ≠ .x3 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 0x6A0) = BitVec.ofNat 64 0xE01 ∧
      ∀ A < 2 ^ 64, A ≠ 0x6A0 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  have hobl : blk3044.res.obligs s := by simp only [blk3044.res, rv_simp]
  refine ⟨_, symRun_sound blk3044 codeAt_3044 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sgn [blk3044.res] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · intro r h1 h2 h3 h4 h5 h6; cases r <;> simp_all [blk3044.res, rv_simp] <;> rfl
  · sgn [blk3044.res] <;> rfl
  · intro A hA hne
    sgn [blk3044.res]
    rw [if_neg (by omega)]

/-- Key query `i` setup: word 1 of `tw_mackey(i)` at `PB + 8`, `a0 = PB`, `a1 = 64`, `a2 = EO`; at the
ECALL. -/
theorem spec3054 (s : MachineState) (hpc : s.pc = pcOf 3054) (i : Nat) (hi : i < 3)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 5 5 t ∧ fetch image t = some (.base .ECALL) ∧ t.pc = pcOf 3059 ∧
      t.getReg .x10 = BitVec.ofNat 64 0x6A0 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x140 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 0x6A8) = BitVec.ofNat 64 (2 ^ 32 * i) ∧
      ∀ A < 2 ^ 64, A ≠ 0x6A8 → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  have hobl : blk3054.res.obligs s := by simp only [blk3054.res, rv_simp]
  refine ⟨_, symRun_sound blk3054 codeAt_3054 s hpc hobl, symRun_ecall blk3054 codeAt_3054 s hobl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sgn [blk3054.res] <;> rfl
  · sgn [blk3054.res] <;> rfl
  · sgn [blk3054.res] <;> rfl
  · sgn [blk3054.res] <;> rfl
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk3054.res, rv_simp] <;> rfl
  · sgn [blk3054.res, h21]
    congr 1; ring
  · intro A hA hne
    sgn [blk3054.res]
    rw [if_neg (by omega)]

/-- `s6 = EO`: the first half of the answer. -/
theorem spec3060 (s : MachineState) (hpc : s.pc = pcOf 3060) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 3061 ∧ t.getReg .x22 = BitVec.ofNat 64 0x140 ∧
      (∀ r, r ≠ .x22 → t.getReg r = s.getReg r) ∧ ∀ A : Word, t.getMem A = s.getMem A := by
  have hobl : blk3060.res.obligs s := by simp only [blk3060.res, rv_simp]
  refine ⟨_, symRun_sound blk3060 codeAt_3060 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · sgn [blk3060.res] <;> rfl
  · sgn [blk3060.res] <;> rfl
  · intro r h1; cases r <;> simp_all [blk3060.res, rv_simp] <;> rfl
  · intro A; sgn [blk3060.res]

/-- XOR the tag word with the cached one at `s9` into `s10`; `s6 = EO + 16`. -/
theorem spec3101 (s : MachineState) (hpc : s.pc = pcOf 3101) (A : Nat) (hA : A + 8 < 2 ^ 24)
    (hA8 : A % 8 = 0) (h25 : s.getReg .x25 = BitVec.ofNat 64 A)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 0x140) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 3105 ∧ t.getReg .x22 = BitVec.ofNat 64 0x150 ∧
      t.getReg .x26 = s.getReg .x26 ||| (s.getMem (BitVec.ofNat 64 A) ^^^ s.getReg .x14) ∧
      (∀ r, r ≠ .x22 → r ≠ .x26 → r ≠ .x15 → t.getReg r = s.getReg r) ∧
      ∀ B : Word, t.getMem B = s.getMem B := by
  have hobl : blk3101.res.obligs s := by sgn [blk3101.res, h25]; omega
  refine ⟨_, symRun_sound blk3101 codeAt_3101 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · sgn [blk3101.res] <;> rfl
  · sgn [blk3101.res, h22] <;> rfl
  · sgn [blk3101.res, h25]
  · intro r h1 h2 h3; cases r <;> simp_all [blk3101.res, rv_simp] <;> rfl
  · intro B; sgn [blk3101.res]

/-- XOR the tag word with the cached one at `s9 + 8` into `s10`; `s9 += 16`; next key or the end. -/
theorem spec3145 (s : MachineState) (hpc : s.pc = pcOf 3145) (A i : Nat) (hA : A + 16 < 2 ^ 24)
    (hA8 : A % 8 = 0) (hi : i < 3) (h25 : s.getReg .x25 = BitVec.ofNat 64 A)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = (if i + 1 = 3 then pcOf 3152 else pcOf 3054) ∧
      t.getReg .x25 = BitVec.ofNat 64 (A + 16) ∧ t.getReg .x21 = BitVec.ofNat 64 (i + 1) ∧
      t.getReg .x26 = s.getReg .x26 ||| (s.getMem (BitVec.ofNat 64 (A + 8)) ^^^ s.getReg .x14) ∧
      (∀ r, r ≠ .x25 → r ≠ .x21 → r ≠ .x26 → r ≠ .x15 → r ≠ .x3 → t.getReg r = s.getReg r) ∧
      ∀ B : Word, t.getMem B = s.getMem B := by
  have hobl : blk3145.res.obligs s := by sgn [blk3145.res, h25]; omega
  refine ⟨_, symRun_sound blk3145 codeAt_3145 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · sgn [blk3145.res, h21]
    by_cases h : i = 2
    · subst h; rfl
    · rw [if_pos (by omega), if_neg (by omega)]
  · sgn [blk3145.res, h25]
  · sgn [blk3145.res, h21]
  · sgn [blk3145.res, h25]
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk3145.res, rv_simp] <;> rfl
  · intro B; sgn [blk3145.res]

/-- Scrub the scratch words, branch on the accumulated difference. -/
theorem spec3152 (s : MachineState) (hpc : s.pc = pcOf 3152) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = (if s.getReg .x26 = 0 then pcOf 3159 else pcOf 3160) ∧
      (∀ r, t.getReg r = s.getReg r) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = 0x6A0 ∨ A = 0x6A8 ∨ A = 0x140 ∨ A = 0x148 ∨ A = 0x150 ∨ A = 0x158 then 0
        else s.getMem (BitVec.ofNat 64 A) := by
  have hobl : blk3152.res.obligs s := by simp only [blk3152.res, rv_simp]
  refine ⟨_, symRun_sound blk3152 codeAt_3152 s hpc hobl, ?_, ?_, ?_⟩
  · sgn [blk3152.res]
    by_cases h : s.getReg .x26 = 0
    · simp [h]
    · simp [h]
  · intro r; cases r <;> simp_all [blk3152.res, rv_simp] <;> rfl
  · intro A hA
    sgn [blk3152.res]
    split_ifs <;> first | rfl | omega

theorem spec3159 (s : MachineState) (hpc : s.pc = pcOf 3159) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 63 ∧ (∀ r, t.getReg r = s.getReg r) ∧
      ∀ B : Word, t.getMem B = s.getMem B := by
  have hobl : blk3159.res.obligs s := by simp only [blk3159.res, rv_simp]
  refine ⟨_, symRun_sound blk3159 codeAt_3159 s hpc hobl, ?_, ?_, ?_⟩
  · sgn [blk3159.res] <;> rfl
  · intro r; cases r <;> simp_all [blk3159.res, rv_simp] <;> rfl
  · intro B; sgn [blk3159.res]

theorem spec3160 (s : MachineState) (hpc : s.pc = pcOf 3160) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 142 ∧ (∀ r, t.getReg r = s.getReg r) ∧
      ∀ B : Word, t.getMem B = s.getMem B := by
  have hobl : blk3160.res.obligs s := by simp only [blk3160.res, rv_simp]
  refine ⟨_, symRun_sound blk3160 codeAt_3160 s hpc hobl, ?_, ?_, ?_⟩
  · sgn [blk3160.res] <;> rfl
  · intro r; cases r <;> simp_all [blk3160.res, rv_simp] <;> rfl
  · intro B; sgn [blk3160.res]

/-! ## The rounds -/

/-- The six scratch doublewords of the routine. -/
def Scr (a : Nat) : Prop := a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0x140 ∨ a = 0x148 ∨ a = 0x150 ∨ a = 0x158

/-- MAC round context relative to the state `u0` after the setup block: `i` key answers used, `s10 = 0`
iff the tag words `0 .. 2 i - 1` equal the cached ones. -/
structure SCtx (u0 : MachineState) (i : Nat) (tag : List Nat) (t : MachineState) : Prop where
  pc : t.pc = if i < 3 then pcOf 3054 else pcOf 3152
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 (2 ^ 61 - 1)
  x19 : t.getReg .x19 = BitVec.ofNat 64 0x14B00
  x21 : t.getReg .x21 = BitVec.ofNat 64 i
  x25 : t.getReg .x25 = BitVec.ofNat 64 (0x14B00 + 16 * i)
  tw : t.getMem (BitVec.ofNat 64 0x6A0) = BitVec.ofNat 64 0xE01
  mem : ∀ a < 2 ^ 64, ¬ Scr a → t.getMem (BitVec.ofNat 64 a) = u0.getMem (BitVec.ofNat 64 a)
  tlen : tag.length = 2 * i
  acc : t.getReg .x26 = 0 ↔ ∀ j < 2 * i,
    BitVec.ofNat 64 (tag.getD j 0) = u0.getMem (BitVec.ofNat 64 (0x14B00 + 8 * j))

theorem or_xor_eq_zero (d c w : Word) : d ||| (c ^^^ w) = 0 ↔ d = 0 ∧ w = c := by
  constructor
  · intro h
    have hb : ∀ k, d.getLsbD k = false ∧ (c ^^^ w).getLsbD k = false := by
      intro k
      have := congrArg (fun x : Word => x.getLsbD k) h
      simpa [BitVec.getLsbD_or, Bool.or_eq_false_iff] using this
    have h1 : d = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [(hb k).1]
    have h2 : c ^^^ w = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro k hk; simp [(hb k).2]
    refine ⟨h1, ?_⟩
    have e : w = c ^^^ (c ^^^ w) := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    rw [e, h2]; simp
  · rintro ⟨rfl, rfl⟩
    simp

/-- One MAC round: key query `i`, a pass per half of the answer, both tag words compared. -/
theorem round_sim (S : List Byte) (hS : S.length = 32) (region : List Byte) (hR : region.length = 65504)
    (u0 : MachineState) (hP : u0.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0])
    (hSw : u0.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S)
    (hRw : wordsToNat (u0.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat region)
    (i : Nat) (hi : i < 3) (tag : List Nat) (t : MachineState) (h : SCtx u0 i tag t)
    {β : Type} (f : BitVec 256 → OracleComp HashSpec β) (W : Nat) (Q : β → MachineState → Prop)
    (hnext : ∀ a u, SCtx u0 (i + 1) (tag ++ macWords a (chunks32 region)) u → Sim image u W (f a) Q) :
    Sim image t (5 + (8 * 1 + (622328 + W))) (H (macKeyInput S i) >>= f) Q := by
  obtain ⟨u, hst, hfe, upc, u10, u11, u12, uun, u6A8, ufr⟩ :=
    spec3054 t (by rw [h.pc, if_pos hi]) i hi h.x21
  have um : ∀ a < 2 ^ 64, ¬ Scr a → u.getMem (BitVec.ofNat 64 a) = u0.getMem (BitVec.ofNat 64 a) :=
    fun a ha hs => by rw [ufr a ha (by simp only [Scr] at hs; omega), h.mem a ha hs]
  have hq : hashInput u = pad64 (macKeyInput S i) := by
    obtain ⟨hn, hw⟩ := words_macKeyInput S hS i
    refine hashInput_eq_pad64 u _ 0 hn (by rw [u11]) (by norm_num) (by rw [u10]; decide) ?_
    rw [hw, u10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      readWords_congr u0 u _ 2 (fun k hk => um _ (by omega) (by simp only [Scr]; omega)),
      readWords_congr u0 u _ 4 (fun k hk => um _ (by omega) (by simp only [Scr]; omega)), hP, hSw,
      ufr 0x6A0 (by norm_num) (by norm_num), h.tw, u6A8, twWords_eq, twWord0]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    constructor <;> apply ofNat_congr <;> omega
  have hb : (pad64 (macKeyInput S i)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_macKeyInput S hS i).1]
  have hq' : hashInput u = addrFmt (macKeyInput S i) :=
    hq.trans (addrFmt_thInput _ _ _ _ _ _ (by decide)).symm
  refine (Sim.steps hst (Sim.query_bind (W := 622328 + W) hfe
    (by rw [uun _ (by simp) (by simp) (by simp) (by simp)]; exact h.x5)
    (hashArgs_of u10 u11 u12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq' (fun a => ?_))).mono (by
        rw [show macKeyInput S i = thInput (tweak 14 0 0 0 i) S from rfl,
          blocks_fmt_th _ _ _ _ _ _ (by decide),
          ← show macKeyInput S i = thInput (tweak 14 0 0 0 i) S from rfl, hb]) (fun _ _ h => h)
  -- after the answer
  have wpc : (writeHash u a).pc = pcOf 3060 := by
    rw [writeHash_pc, upc]; apply BitVec.eq_of_toNat_eq; simp
  have wm : ∀ x < 2 ^ 64, (writeHash u a).getMem (BitVec.ofNat 64 x) =
      if x = 0x140 + 24 then a.extractLsb' 192 64 else if x = 0x140 + 16 then a.extractLsb' 128 64
      else if x = 0x140 + 8 then a.extractLsb' 64 64 else if x = 0x140 then a.extractLsb' 0 64
      else u.getMem (BitVec.ofNat 64 x) :=
    fun x hx => writeHash_getMem_ofNat u a 0x140 x u12 (by norm_num) hx
  obtain ⟨v, vst, vpc, v22, vun, vm⟩ := spec3060 (writeHash u a) wpc
  have vr : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x22 → v.getReg r = t.getReg r :=
    fun r h3 h10 h11 h12 h22 => by rw [vun r h22, writeHash_getReg, uun r h3 h10 h11 h12]
  have vmu : ∀ x < 2 ^ 64, ¬ Scr x → v.getMem (BitVec.ofNat 64 x) = u0.getMem (BitVec.ofNat 64 x) := by
    intro x hx hs
    have hs' := hs
    simp only [Scr] at hs'
    rw [vm, wm x hx, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      um x hx hs]
  have hwv : wordsToNat (v.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat region := by
    rw [readWords_congr u0 v _ 8188 (fun k hk => vmu _ (by omega) (by simp only [Scr]; omega)), hRw]
  -- first half
  obtain ⟨p1, pst1, ppc1, p14, pun1, pm1⟩ := MacPass.mac_pass_region codeAt_3061 v vpc 0x140 region v22
    (by norm_num) (by norm_num)
    (by rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x18)
    (by rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x19) hR hwv
  rw [vm, wm 0x140 (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl, vm, wm (0x140 + 8) (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
    if_pos rfl, MacPass.tagWord0] at p14
  set T := 0x14B00 + 16 * i with hT
  obtain ⟨q, qst, qpc, q22, q26, qun, qm⟩ := spec3101 p1 (by rw [ppc1]; rfl) T (by omega) (by omega)
    (by rw [pun1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x25)
    (by rw [pun1 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact v22)
  have qr : ∀ r, r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x23 → r ≠ .x24 → r ≠ .x22 →
      r ≠ .x26 → q.getReg r = v.getReg r :=
    fun r h13 h14 h15 h16 h17 h23 h24 h22 h26 => by
      rw [qun r h22 h26 h15, pun1 r h13 h14 h15 h16 h17 h23 h24]
  have qmv : ∀ x : Word, q.getMem x = v.getMem x := fun x => by rw [qm, pm1]
  have hwq : wordsToNat (q.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat region := by
    rw [readWords_congr v q _ 8188 (fun k hk => qmv _), hwv]
  -- second half
  obtain ⟨p2, pst2, ppc2, r14, pun2, pm2⟩ := MacPass.mac_pass_region codeAt_3105 q qpc 0x150 region q22
    (by norm_num) (by norm_num)
    (by rw [qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x18)
    (by rw [qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x19) hR hwq
  rw [qmv, vm, wm 0x150 (by norm_num), if_neg (by norm_num), if_pos rfl, qmv, vm,
    wm (0x150 + 8) (by norm_num), if_pos rfl, MacPass.tagWord1] at r14
  obtain ⟨z, zst, zpc, z25, z21, z26, zun, zm⟩ := spec3145 p2 (by rw [ppc2]; rfl) T i (by omega) (by omega) hi
    (by rw [pun2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x25)
    (by rw [pun2 _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      qr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x21)
  have zr : ∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 →
      r ≠ .x17 → r ≠ .x21 → r ≠ .x22 → r ≠ .x23 → r ≠ .x24 → r ≠ .x25 → r ≠ .x26 →
      z.getReg r = t.getReg r := by
    intro r h3 h10 h11 h12 h13 h14 h15 h16 h17 h21 h22 h23 h24 h25 h26
    rw [zun r h25 h21 h26 h15 h3, pun2 r h13 h14 h15 h16 h17 h23 h24,
      qr r h13 h14 h15 h16 h17 h23 h24 h22 h26, vr r h3 h10 h11 h12 h22]
  have zmv : ∀ x : Word, z.getMem x = v.getMem x := fun x => by rw [zm, pm2, qmv]
  -- the accumulated difference
  have hT1 : p1.getMem (BitVec.ofNat 64 T) = u0.getMem (BitVec.ofNat 64 T) := by
    rw [pm1, vmu T (by omega) (by simp only [Scr]; omega)]
  have hT2 : p2.getMem (BitVec.ofNat 64 (T + 8)) = u0.getMem (BitVec.ofNat 64 (T + 8)) := by
    rw [pm2, qmv, vmu (T + 8) (by omega) (by simp only [Scr]; omega)]
  have h26 : z.getReg .x26 = 0 ↔ t.getReg .x26 = 0 ∧
      BitVec.ofNat 64 ((macWords a (chunks32 region)).getD 0 0) = u0.getMem (BitVec.ofNat 64 T) ∧
      BitVec.ofNat 64 ((macWords a (chunks32 region)).getD 1 0) = u0.getMem (BitVec.ofNat 64 (T + 8)) := by
    rw [z26, or_xor_eq_zero, hT2, r14,
      pun2 .x26 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), q26,
      or_xor_eq_zero, hT1, p14,
      pun1 .x26 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp),
      vr .x26 (by simp) (by simp) (by simp) (by simp) (by simp)]
    exact and_assoc
  have hcs : (macWords a (chunks32 region)).length = 2 := rfl
  refine (Sim.steps ((vst.trans (pst1.trans (qst.trans (pst2.trans zst)))).of_eq rfl
    (show 1 + (311158 + (4 + (311158 + 7))) = 622328 by norm_num)) (hnext a z ?_))
  refine ⟨?_, ?_, ?_, ?_, z21, ?_, ?_, ?_, ?_, ?_⟩
  · rw [zpc]
    by_cases h3 : i + 1 = 3
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_pos (by omega)]
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x5
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x18
  · rw [zr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.x19
  · rw [z25]; congr 1
  · rw [zmv, vm, wm 0x6A0 (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
      if_neg (by norm_num), ufr 0x6A0 (by norm_num) (by norm_num)]
    exact h.tw
  · intro x hx hs
    rw [zmv, vmu x hx hs]
  · rw [List.length_append, h.tlen, hcs]; ring
  · rw [h26, h.acc]
    constructor
    · rintro ⟨hold, hw0, hw1⟩ j hj
      by_cases h1 : j < 2 * i
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.tlen]; exact h1),
          ← List.getD_eq_getElem?_getD]
        exact hold j h1
      · by_cases h2 : j = 2 * i
        · subst h2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.tlen]), h.tlen,
            Nat.sub_self, ← List.getD_eq_getElem?_getD, show 0x14B00 + 8 * (2 * i) = T by omega]
          exact hw0
        · have h3 : j = 2 * i + 1 := by omega
          subst h3
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.tlen]; omega), h.tlen,
            show 2 * i + 1 - 2 * i = 1 by omega, ← List.getD_eq_getElem?_getD,
            show 0x14B00 + 8 * (2 * i + 1) = T + 8 by omega]
          exact hw1
    · intro hall
      refine ⟨fun j hj => ?_, ?_, ?_⟩
      · have := hall j (by omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.tlen]; exact hj),
          ← List.getD_eq_getElem?_getD] at this
      · have := hall (2 * i) (by omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.tlen]), h.tlen,
          Nat.sub_self, ← List.getD_eq_getElem?_getD, show 0x14B00 + 8 * (2 * i) = T by omega] at this
      · have := hall (2 * i + 1) (by omega)
        rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.tlen]; omega), h.tlen,
          show 2 * i + 1 - 2 * i = 1 by omega, ← List.getD_eq_getElem?_getD,
          show 0x14B00 + 8 * (2 * i + 1) = T + 8 by omega] at this

/-- Cycles of the setup and of the MAC routine up to the digest loop: `26 + 10 + 3 * 622341 + 8 + 45`. -/
def macCyc : Nat := 1867112

/-- **The MAC check.** -/
theorem mac_sim (sk : SecretKey) (cache : Cache) (m : Message) {β : Type}
    (rest : OracleComp HashSpec (Option β)) (Wr : Nat) (Q : Option β → MachineState → Prop)
    (hrest : ∀ u, MacOk sk cache m u → Sim image u Wr rest Q)
    (hbad : ∀ t, t.pc = pcOf 144 → t.getReg .x5 = 1 → t.getReg .x10 = 1 → Q none t) :
    Sim image (s0 sk cache m) (macCyc + Wr)
      (H (macKeyInput (toList sk) 0) >>= fun a0 => H (macKeyInput (toList sk) 1) >>= fun a1 =>
        H (macKeyInput (toList sk) 2) >>= fun a2 =>
        if macTag a0 a1 a2 (cacheRegion (toList cache)) = cacheTag (toList cache) then rest
        else pure none) Q := by
  set s := s0 sk cache m with hs0
  have hS : (toList sk).length = 32 := length_toList sk
  have hs := symRun_sound blk0 codeAt_0 s (s0_pc sk cache m) (by simp only [blk0.res, rv_simp])
  have hk : blk0.res.cycles = 26 := rfl
  have hk' : blk0.res.steps = 26 := rfl
  rw [hk, hk'] at hs
  set u := blk0.res.toState s with hu
  have f := setup_frame s
  have rg := setup_regs s
  have pc1 : u.pc = pcOf 3044 := by simp only [hu, blk0.res, rv_simp]
  have x5 : u.getReg .x5 = 0 := by rw [rg.get .x5]; exact s0_getReg sk cache m .x5 (by decide)
  have hR := length_cacheRegion cache
  -- the state after the setup
  have uP : u.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0] := by
    rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega), readWords_ofNat_two,
      s0_zero sk cache m 0x6B0 (by norm_num) (by norm_num) (by omega),
      s0_zero sk cache m (0x6B0 + 8) (by norm_num) (by norm_num) (by omega)]
  have uS : u.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk) := by
    rw [hu, blk0_pbS, s0_readWords_sk]
  have uR : wordsToNat (u.readWords (BitVec.ofNat 64 0x4B20) 8188) = leNat (cacheRegion (toList cache)) := by
    rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega),
      show (0x4B20 : Nat) = 0x4B00 + 32 from rfl,
      s0_readWords_cache sk cache m 32 8188 (by norm_num) (by norm_num), wordsToNat_wordsOf]
    rfl
  have uT : ∀ j < 6, u.getMem (BitVec.ofNat 64 (0x14B00 + 8 * j)) =
      (wordsOf (cacheTag (toList cache))).getD j 0 := by
    intro j hj
    rw [f.getMem (by omega) (by simp only [setupW]; omega), cacheTag_eq,
      ← s0_readWords_cache sk cache m 65536 6 (by norm_num) (by norm_num),
      show (0x4B00 + 65536 : Nat) = 0x14B00 from rfl, MacPass.readWords_getD _ 6 _ j hj]
  have hw6 : (wordsOf (cacheTag (toList cache))).length = 6 := by
    rw [cacheTag_eq, ← s0_readWords_cache sk cache m 65536 6 (by norm_num) (by norm_num), readWords_length]
  have uZ : ∀ a, Scr a → u.getMem (BitVec.ofNat 64 a) = 0 := by
    intro a ha
    simp only [Scr] at ha
    rw [f.getMem (by omega) (by simp only [setupW]; omega)]
    exact s0_zero sk cache m a (by omega) (by omega) (by omega)
  -- init
  obtain ⟨v, vst, vpc, v18, v19, v25, v21, v26, vun, v6A0, vfr⟩ := spec3044 u pc1
  have h0 : SCtx u 0 [] v := by
    refine ⟨by rw [vpc]; rfl, ?_, v18, v19, v21, v25, v6A0, fun a ha hs => ?_, rfl, ?_⟩
    · rw [vun _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact x5
    · exact vfr a ha (by simp only [Scr] at hs; omega)
    · exact ⟨fun _ j hj => absurd hj (by omega), fun _ => v26⟩
  set region := cacheRegion (toList cache) with hregion
  set cs := chunks32 region with hcs
  refine (Sim.steps hs (Sim.steps vst
    (round_sim (toList sk) hS region hR u uP uS uR 0 (by norm_num) [] v h0 _ _ Q (fun a0 w0 c0 =>
    round_sim (toList sk) hS region hR u uP uS uR 1 (by norm_num) _ w0 c0 _ _ Q (fun a1 w1 c1 =>
    round_sim (toList sk) hS region hR u uP uS uR 2 (by norm_num) _ w1 c1 _ (8 + (45 + Wr)) Q
      (fun a2 w2 c2 => ?_)))))).mono (by unfold macCyc; omega) (fun _ _ h => h)
  -- the end of the routine
  have hiff : macTag a0 a1 a2 region = cacheTag (toList cache) ↔ w2.getReg .x26 = 0 := by
    rw [c2.acc, macTag_eq_iff a0 a1 a2 region _ (length_cacheTag cache) hw6]
    simp only [List.nil_append]
    constructor
    · intro h j hj; rw [uT j hj]; exact h j hj
    · intro h j hj; rw [← uT j hj]; exact h j hj
  obtain ⟨x, xst, xpc, xr, xm⟩ := spec3152 w2 (by rw [c2.pc]; rfl)
  have xu : ∀ a < 2 ^ 64, x.getMem (BitVec.ofNat 64 a) = u.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    rw [xm a ha]
    by_cases hsc : Scr a
    · rw [if_pos (by simpa only [Scr] using hsc), uZ a hsc]
    · rw [if_neg (by simpa only [Scr] using hsc), c2.mem a ha hsc]
  -- the failure exit
  have fail : ∀ t, t.pc = pcOf 142 → Sim image t 2 (pure none) Q := by
    intro t tpc
    have hs142 := symRun_sound blk142 codeAt_142 t tpc (by simp only [blk142.res, rv_simp])
    have hc142 : blk142.res.cycles = 2 := rfl
    rw [hc142] at hs142
    exact Sim.pure_steps hs142 (hbad _ (by simp only [blk142.res, rv_simp]) (by simp only [blk142.res, rv_simp])
      (by simp only [blk142.res, rv_simp]))
  by_cases hd : w2.getReg .x26 = 0
  swap
  · rw [if_neg (fun h => hd (hiff.mp h))]
    obtain ⟨y, yst, ypc, -, -⟩ := spec3160 x (by rw [xpc, if_neg hd])
    exact (Sim.steps xst (Sim.steps yst (fail y ypc))).mono (by omega) (fun _ _ h => h)
  rw [if_pos (hiff.mpr hd)]
  obtain ⟨t6, yst, pc6, yr, ym⟩ := spec3159 x (by rw [xpc, if_pos hd])
  have m6 : ∀ a < 2 ^ 64, t6.getMem (BitVec.ofNat 64 a) = u.getMem (BitVec.ofNat 64 a) :=
    fun a ha => by rw [ym, xu a ha]
  have hs7 := symRun_sound blk63 codeAt_63 t6 pc6 (by simp only [blk63.res, rv_simp])
  have hc7 : blk63.res.cycles = 2 := rfl
  rw [hc7] at hs7
  set t7 := blk63.res.toState t6 with ht7
  have n7 : ∀ a < 2 ^ 64, t7.getMem (BitVec.ofNat 64 a) = u.getMem (BitVec.ofNat 64 a) := fun a ha => by
    rw [ht7, Result.toState_getMem, show blk63.res.st.mem = [] from rfl, memEval_nil, m6 a ha]
  have r7 : RegsEq t6 t7 [.x6, .x7] := by
    intro r hr; rw [ht7, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc7 : t7.pc = pcOf 2844 := by simp only [ht7, blk63.res, rv_simp]
  have hs8 := symRun_sound blk2844 codeAt_2844 t7 pc7 (by simp only [blk2844.res, rv_simp])
  rw [blk2844_cycles] at hs8
  set t8 := blk2844.res.toState t7 with ht8
  have f8 : Frame t7 t8 (fun a => 0x780 ≤ a ∧ a < 0x7c0) := blk2844_frame t7
  have r8 := blk2844_regs t7
  have fr : Frame s t7 macW := by
    intro a ha hW
    rw [n7 a ha, f.getMem ha (fun h => hW (Or.inl h))]
  have fr8 : Frame s t8 macW := (fr.trans f8).mono (by
    intro a ha
    rcases ha with h | h
    · exact h
    · exact Or.inr (Or.inr h))
  have fu : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ macW (a + 8 * i)) →
      t7.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
    fun a n h1 h2 => fr.readWords a n h1 h2
  have fu7 : ∀ a n, a + 8 * n < 2 ^ 64 →
      t7.readWords (BitVec.ofNat 64 a) n = u.readWords (BitVec.ofNat 64 a) n := by
    intro a n h1
    exact readWords_congr _ _ a n (fun i hi => n7 _ (by omega))
  have hz : ∀ a n, a % 8 = 0 → a + 8 * n + 8 < 2 ^ 64 →
      (∀ i < n, a + 8 * i + 8 ≤ 0x20 ∨ (0x40 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x80) ∨
        (0xA0 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x4B00) ∨ 0x24B00 ≤ a + 8 * i) →
      s.readWords (BitVec.ofNat 64 a) n = List.replicate n 0 := by
    intro a n h8 hb hout
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      rw [readWords_ofNat_succ, s0_zero sk cache m a h8 (by omega) (by simpa using hout 0 (by omega)),
        ih (a + 8) (by omega) (by omega)
          (fun i hi => by rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact hout _ (by omega))]
      rfl
  have x5' : t7.getReg .x5 = 0 := by
    rw [r7.get .x5, yr, xr, c2.x5]
  have ok : MacOk sk cache m t8 := by
    refine ⟨blk2844_pc t7, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fr8⟩
    · rw [f8.readWords _ _ (by norm_num) (by intro i hi; omega),
        fu7 _ _ (by norm_num), hu, blk0_rbS, s0_readWords_sk]
    · rw [f8.readWords _ _ (by norm_num) (by intro i hi; omega),
        fu7 _ _ (by norm_num), hu, blk0_rbM, s0_readWords_msg]
    · have hw := blk2844_words t7
      rw [← ht8] at hw
      rw [hw]
      rw [f8.getMem (by norm_num) (by omega), f8.getMem (by norm_num) (by omega),
        f8.getMem (by norm_num) (by omega), f8.getMem (by norm_num) (by omega),
        f8.getMem (by norm_num) (by omega), f8.getMem (by norm_num) (by omega),
        f8.getMem (by norm_num) (by omega), f8.getMem (by norm_num) (by omega)]
    · rw [f8.readWords _ _ (by norm_num) (by intro i hi; omega), readWords_ofNat_succ,
        n7 _ (by norm_num), hu, blk0_db0,
        fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [f8.readWords _ _ (by norm_num) (by intro i hi; omega),
        fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega), s0_readWords_msg]
    · rw [r8.get .x5, x5']
    · exact blk2844_x6 t7
    · rw [r8.get .x7]; simp only [ht7, blk63.res, rv_simp]; rfl
    · rw [f8.readWords _ _ (by norm_num) (by intro i hi; omega),
        fu7 _ _ (by norm_num), hu, blk0_pbS, s0_readWords_sk]
  exact (Sim.steps xst (Sim.steps yst (Sim.steps hs7 (Sim.steps hs8 (hrest t8 ok))))).mono (by omega)
    (fun _ _ h => h)

end SigGolfCandidate.Sign
