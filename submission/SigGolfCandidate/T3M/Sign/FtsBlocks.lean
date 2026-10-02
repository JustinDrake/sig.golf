import SigGolfCandidate.T3M.Sign.BaseInv

/-!
# Sign: block specifications of the FTS phase (words 172..356)

`ds_done` (172): the index `N mod 2^31` to `TREE` and `IDXV`, the FTS arena, the proof and secret
pointers; `fts_coord` (186), `fts_leaf` (189..249: the PRF pair at even leaves into `SEC`, the FTS leaf
hash into heap node `2048 + leaf`), `fts_leaves_done` (250: `build_levels`, height 11, tag 10), the
secrets (256..277), the frontier (278..330), the outer siblings (331..344) and the root to the forest
block (345..356).
-/

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)

/-- Close a memory read of a block result: resolve the `if`s of the symbolic memory, then compare
addresses. -/
macro "ite_close" : tactic =>
  `(tactic| ((repeat (first | rw [if_neg (by sg_omega)] | rw [if_pos (by sg_omega)])); first | (congr 2; sg_omega) | rfl))

/-- `omega` for block obligations (after `t3n`): drop `True` conjuncts first. -/
macro "obl_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC, and_true, true_and] at *); omega))

/-- `sg_omega` that tolerates the address `simp` closing the goal. -/
macro "sgo" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC, false_or, or_false] at *) <;> omega))

/-- `(w << 33) >> 33` is `w mod 2^31`. -/
theorem shl33_shr33 (w : Word) : (w <<< 33) >>> 33 = BitVec.ofNat 64 (w.toNat % 2 ^ 31) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := w.isLt
  omega

/-- `ds_done` (172..185): `TREE = IDXV = N mod 2^31`, `sp = FTS`, proof / secret pointers, `coord = 0`. -/
theorem blk172_spec (s : MachineState) (hpc : s.pc = pcOf 172) :
    ∃ t, Steps image s 14 14 t ∧ t.pc = pcOf 186 ∧
      t.getReg .x9 = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 ((s.getMem (BitVec.ofNat 64 NBUF)).toNat % 2 ^ 31) ∧
      t.getReg .x2 = BitVec.ofNat 64 FTS ∧ t.getReg .x16 = BitVec.ofNat 64 (SIG + 352) ∧
      t.getReg .x26 = BitVec.ofNat 64 (SIG + 16) ∧ t.getReg .x8 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x2, .x8, .x9, .x16, .x26, .x28] ∧ Frame s t (fun A => A = IDXV) := by
  refine ⟨_, symRun_sound blk_172 codeAt_172 s hpc (by simp [blk_172.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_172.res, E.eval]
  · simp only [Result.toState_getReg, blk_172.res]; t3n []; rw [shl33_shr33]; rfl
  · simp only [Result.toState_getMem, blk_172.res, IDXV, NBUF]; t3n []; rw [shl33_shr33]; rfl
  · simp [blk_172.res, rv_simp]
  · simp [blk_172.res, rv_simp]
  · simp [blk_172.res, rv_simp]
  · simp [blk_172.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_172.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [IDXV] at hn
    simp only [Result.toState_getMem, blk_172.res]
    t3n []
    rw [if_neg (by omega)]

/-- `fts_coord` (186): `coord ≥ 7` ends the FTS phase. -/
theorem blk186_spec (s : MachineState) (hpc : s.pc = pcOf 186) (c : Nat) (hc : c < 2 ^ 63)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c < 7 then pcOf 188 else pcOf 357) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_186 codeAt_186 s hpc (by simp [blk_186.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_186.res, E.eval, CmpOp.eval, h8, ofNat_slt c 7 hc (by norm_num)]
    by_cases h : c < 7 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_186.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_186.res, rv_simp]

/-- `LEAF := 0`. -/
theorem blk188_spec (s : MachineState) (hpc : s.pc = pcOf 188) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 189 ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_188 codeAt_188 s hpc (by simp [blk_188.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_188.res, E.eval]
  · simp [blk_188.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_188.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_188.res, rv_simp]

/-- `fts_leaf` (189): `LEAF ≥ 2048` ends the leaves. -/
theorem blk189_spec (s : MachineState) (hpc : s.pc = pcOf 189) (leaf : Nat) (hl : leaf < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if leaf < 2048 then pcOf 192 else pcOf 250) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_189 codeAt_189 s hpc (by simp [blk_189.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_189.res, E.eval, CmpOp.eval, h18, ofNat_slt leaf 2048 hl (by norm_num)]
    by_cases h : leaf < 2048 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_189.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_189.res, rv_simp]

/-- Odd leaves skip the PRF. -/
theorem blk192_spec (s : MachineState) (hpc : s.pc = pcOf 192) (leaf : Nat) (hl : leaf < 2 ^ 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if leaf % 2 = 0 then pcOf 194 else pcOf 211) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_192 codeAt_192 s hpc (by simp [blk_192.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_192.res, E.eval, CmpOp.eval, BinOp.eval, h18, ofNat_and1]
    by_cases h : leaf % 2 = 0
    · simp [h]
    · have h1 : leaf % 2 = 1 := by omega
      simp [h1]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_192.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_192.res, rv_simp]

/-- The FTS PRF header `T8(coord, index, pair)` at `PRIV+16`, the HASH arguments `(PRIV, 64, SEC + 16 leaf)`. -/
theorem blk194_spec (s : MachineState) (hpc : s.pc = pcOf 194) (c idx leaf : Nat) (hc : c < 256)
    (hidx : idx < 2 ^ 32) (hleaf : leaf < 2048)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h9 : s.getReg .x9 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 210 ∧
      t.getReg .x10 = BitVec.ofNat 64 PRIV ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (SEC + 16 * leaf) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 16)) = BitVec.ofNat 64 (2049 + 65536 * c) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 24)) = BitVec.ofNat 64 (idx + 2 ^ 32 * (leaf / 2)) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = PRIV + 16 ∨ A = PRIV + 24) := by
  refine ⟨_, symRun_sound blk_194 codeAt_194 s hpc (by simp [blk_194.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_194.res, E.eval]
  · simp [blk_194.res, rv_simp]
  · simp [blk_194.res, rv_simp]
  · simp only [Result.toState_getReg, blk_194.res]; t3n [h18]; sg_omega
  · simp only [Result.toState_getMem, blk_194.res, PRIV]
    t3n [h8]
    rw [ofNat_or_disjoint' 2049 (c * 65536) 16 (by norm_num) (by omega)]
    congr 1; omega
  · simp only [Result.toState_getMem, blk_194.res, PRIV]
    t3n [h9, h18]
    rw [ofNat_shr leaf 1 (by omega), ofNat_shl, ofNat_or_disjoint' idx (leaf / 2 ^ 1 * 2 ^ 32) 32 hidx (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_194.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, blk_194.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

theorem fetch_210 (s : MachineState) (hpc : s.pc = pcOf 210) : fetch image s = some (.base .ECALL) :=
  (codeAt_210.fetch s hpc).trans rfl

set_option maxRecDepth 100000 in
/-- `fts_noprf` (211..235): the secret of `leaf` to `FLEAF+32`, the header `T9(coord, index, leaf)`, the
HASH arguments `(FLEAF, 64, LFOUT)`. -/
theorem blk211_spec (s : MachineState) (hpc : s.pc = pcOf 211) (c idx leaf : Nat) (hc : c < 256)
    (hidx : idx < 2 ^ 32) (hleaf : leaf < 2048)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) (h9 : s.getReg .x9 = BitVec.ofNat 64 idx)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 25 25 t ∧ t.pc = pcOf 236 ∧
      t.getReg .x10 = BitVec.ofNat 64 FLEAF ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 LFOUT ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 32)) = s.getMem (BitVec.ofNat 64 (SEC + 16 * leaf)) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 40)) = s.getMem (BitVec.ofNat 64 (SEC + 16 * leaf + 8)) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 16)) = BitVec.ofNat 64 (2305 + 65536 * c) ∧
      t.getMem (BitVec.ofNat 64 (FLEAF + 24)) = BitVec.ofNat 64 (idx + 2 ^ 32 * leaf) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = FLEAF + 16 ∨ A = FLEAF + 24 ∨ A = FLEAF + 32 ∨ A = FLEAF + 40) := by
  have hobl : Oblig.all s blk_211.res.st.obl := by
    simp only [blk_211.res]
    t3n [h18]
    sg_omega
  refine ⟨_, symRun_sound blk_211 codeAt_211 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_211.res, E.eval]
  · simp [blk_211.res, rv_simp]
  · simp [blk_211.res, rv_simp]
  · simp [blk_211.res, rv_simp]
  · simp only [Result.toState_getMem, blk_211.res, FLEAF, SEC]
    t3n [h18]
    congr 2; omega
  · simp only [Result.toState_getMem, blk_211.res, FLEAF, SEC]
    t3n [h18]
    congr 2; omega
  · simp only [Result.toState_getMem, blk_211.res, FLEAF]
    t3n [h8]
    rw [ofNat_or_disjoint' 2305 (c * 65536) 16 (by norm_num) (by omega)]
    congr 1; omega
  · simp only [Result.toState_getMem, blk_211.res, FLEAF]
    t3n [h9, h18]
    rw [ofNat_or_disjoint' idx (leaf * 4294967296) 32 hidx (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_211.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [FLEAF] at hn
    simp only [Result.toState_getMem, blk_211.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem fetch_236 (s : MachineState) (hpc : s.pc = pcOf 236) : fetch image s = some (.base .ECALL) :=
  (codeAt_236.fetch s hpc).trans rfl

/-- 237..249: the leaf hash to heap node `2048 + leaf`, `LEAF += 1`, back to `fts_leaf`. -/
theorem blk237_spec (s : MachineState) (hpc : s.pc = pcOf 237) (leaf : Nat) (hleaf : leaf < 2048)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h2 : s.getReg .x2 = BitVec.ofNat 64 FTS) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 189 ∧ t.getReg .x18 = BitVec.ofNat 64 (leaf + 1) ∧
      t.getMem (BitVec.ofNat 64 (FTS + 16 * (2048 + leaf))) = s.getMem (BitVec.ofNat 64 LFOUT) ∧
      t.getMem (BitVec.ofNat 64 (FTS + 16 * (2048 + leaf) + 8)) = s.getMem (BitVec.ofNat 64 (LFOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x18, .x28, .x29] ∧
      Frame s t (fun A => A = FTS + 16 * (2048 + leaf) ∨ A = FTS + 16 * (2048 + leaf) + 8) := by
  have hobl : Oblig.all s blk_237.res.st.obl := by
    simp only [blk_237.res]
    t3n [h18, h2]
    sg_omega
  refine ⟨_, symRun_sound blk_237 codeAt_237 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_237.res, E.eval]
  · simp only [Result.toState_getReg, blk_237.res]; t3n [h18]
  · simp only [Result.toState_getMem, blk_237.res, FTS, LFOUT]
    t3n [h18, h2, FTS]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, blk_237.res, FTS, LFOUT]
    t3n [h18, h2, FTS]
    rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_237.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [FTS] at hn
    simp only [Result.toState_getMem, blk_237.res]
    t3n [h18, h2, FTS]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fts_leaves_done` (250..255): `H = 11`, `E = hdr0 10 coord`, `jal build_levels` (return to 256). -/
theorem blk250_spec (s : MachineState) (hpc : s.pc = pcOf 250) (c : Nat) (hc : c < 256)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (1013 + 113) ∧ t.getReg .x1 = pcOf 256 ∧
      t.getReg .x15 = BitVec.ofNat 64 11 ∧ t.getReg .x21 = BitVec.ofNat 64 (2561 + 65536 * c) ∧
      RegsExcept s t [.x1, .x15, .x21, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_250 codeAt_250 s hpc (by simp [blk_250.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_250.res, E.eval]
  · simp [blk_250.res, rv_simp]
  · simp [blk_250.res, rv_simp]
  · simp only [Result.toState_getReg, blk_250.res]
    t3n [h8]
    rw [ofNat_or_disjoint' 2561 (c * 65536) 16 (by norm_num) (by omega)]
    congr 1; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_250.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_250.res, rv_simp]

/-- 256..262: `ROWP = SEL + 24 coord`, `J = 0`. -/
theorem blk256_spec (s : MachineState) (hpc : s.pc = pcOf 256) (c : Nat) (hc : c < 7)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = pcOf 263 ∧ t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c) ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7, .x19, .x25] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_256 codeAt_256 s hpc (by simp [blk_256.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_256.res, E.eval]
  · simp only [Result.toState_getReg, blk_256.res]; t3n [h8]; sg_omega
  · simp [blk_256.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_256.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_256.res, rv_simp]

/-- `fts_sec` (263): `J ≥ 3` ends the secrets. -/
theorem blk263_spec (s : MachineState) (hpc : s.pc = pcOf 263) (j : Nat) (hj : j < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if j < 3 then pcOf 265 else pcOf 278) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_263 codeAt_263 s hpc (by simp [blk_263.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_263.res, E.eval, CmpOp.eval, h19, ofNat_slt j 3 hj (by norm_num)]
    by_cases h : j < 3 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_263.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_263.res, rv_simp]

/-- 265..277: secret `SEC + 16 [ROWP + 8 J]` to `[SDST]`, `SDST += 16`, `J += 1`. -/
theorem blk265_spec (s : MachineState) (hpc : s.pc = pcOf 265) (j rowp sdst g : Nat)
    (hrow : rowp + 8 * j + 8 ≤ 2 ^ 24) (hrow8 : rowp % 8 = 0) (hsd : sdst + 16 ≤ 2 ^ 24) (hsd8 : sdst % 8 = 0)
    (hg : g < 2048) (hj : j < 3)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (h25 : s.getReg .x25 = BitVec.ofNat 64 rowp)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 sdst)
    (hgm : s.getMem (BitVec.ofNat 64 (rowp + 8 * j)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf 263 ∧ t.getReg .x19 = BitVec.ofNat 64 (j + 1) ∧
      t.getReg .x26 = BitVec.ofNat 64 (sdst + 16) ∧
      t.getMem (BitVec.ofNat 64 sdst) = s.getMem (BitVec.ofNat 64 (SEC + 16 * g)) ∧
      t.getMem (BitVec.ofNat 64 (sdst + 8)) = s.getMem (BitVec.ofNat 64 (SEC + 16 * g + 8)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x26, .x28] ∧
      Frame s t (fun A => A = sdst ∨ A = sdst + 8) := by
  have hm : s.getMem (BitVec.ofNat 64 (j * 8 + rowp)) = BitVec.ofNat 64 g := by
    rw [show j * 8 + rowp = rowp + 8 * j by ring]; exact hgm
  have hobl : Oblig.all s blk_265.res.st.obl := by
    simp only [blk_265.res]
    t3n [h19, h25, h26, hm]
    sg_omega
  refine ⟨_, symRun_sound blk_265 codeAt_265 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_265.res, E.eval]
  · simp only [Result.toState_getReg, blk_265.res]; t3n [h19]
  · simp only [Result.toState_getReg, blk_265.res]; t3n [h26]
  · simp only [Result.toState_getMem, blk_265.res, SEC]
    t3n [h19, h25, h26, hm]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2; omega
  · simp only [Result.toState_getMem, blk_265.res, SEC]
    t3n [h19, h25, h26, hm]
    try rw [if_pos (by omega)]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_265.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_265.res]
    t3n [h26]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fts_sec_done` (278..279): `DSTART = 8`, `J = 0`. -/
theorem blk278_spec (s : MachineState) (hpc : s.pc = pcOf 278) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 280 ∧ t.getReg .x23 = BitVec.ofNat 64 8 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x19, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_278 codeAt_278 s hpc (by simp [blk_278.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_278.res, E.eval]
  · simp [blk_278.res, rv_simp]
  · simp [blk_278.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_278.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_278.res, rv_simp]

/-- `fr_leaf` (280): `J ≥ 3` ends the frontier. -/
theorem blk280_spec (s : MachineState) (hpc : s.pc = pcOf 280) (j : Nat) (hj : j < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if j < 3 then pcOf 282 else pcOf 331) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_280 codeAt_280 s hpc (by simp [blk_280.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_280.res, E.eval, CmpOp.eval, h19, ofNat_slt j 3 hj (by norm_num)]
    by_cases h : j < 3 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_280.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_280.res, rv_simp]

/-- 282..290: `HS = 2048 + [ROWP + 8 J]`, `NXT = 0`; `J = 2` skips the next leaf. -/
theorem blk282_spec (s : MachineState) (hpc : s.pc = pcOf 282) (j rowp g : Nat)
    (hrow : rowp + 8 * j + 16 ≤ 2 ^ 24) (hrow8 : rowp % 8 = 0) (hg : g < 2048) (hj : j < 3)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) (h25 : s.getReg .x25 = BitVec.ofNat 64 rowp)
    (hgm : s.getMem (BitVec.ofNat 64 (rowp + 8 * j)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = (if j = 2 then pcOf 295 else pcOf 291) ∧
      t.getReg .x20 = BitVec.ofNat 64 (2048 + g) ∧ t.getReg .x21 = BitVec.ofNat 64 0 ∧
      t.getReg .x6 = BitVec.ofNat 64 (rowp + 8 * j) ∧
      RegsExcept s t [.x6, .x7, .x20, .x21] ∧ Frame s t (fun _ => False) := by
  have hm : s.getMem (BitVec.ofNat 64 (j * 8 + rowp)) = BitVec.ofNat 64 g := by
    rw [show j * 8 + rowp = rowp + 8 * j by ring]; exact hgm
  have hobl : Oblig.all s blk_282.res.st.obl := by
    simp only [blk_282.res]
    t3n [h19, h25]
    omega
  refine ⟨_, symRun_sound blk_282 codeAt_282 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_282.res, E.eval, CmpOp.eval, h19]
    by_cases h : j = 2
    · subst h; simp
    · rw [if_neg h]
      have : BitVec.ofNat 64 j ≠ 2#64 := fun he => h (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
      simp [this]
  · simp only [Result.toState_getReg, blk_282.res]; t3n [h19, h25, hm]; omega
  · simp [blk_282.res, rv_simp]
  · simp only [Result.toState_getReg, blk_282.res]; t3n [h19, h25]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_282.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_282.res, rv_simp]

/-- 291..294: `NXT = 2048 + [t1 + 8]` (the next leaf). -/
theorem blk291_spec (s : MachineState) (hpc : s.pc = pcOf 291) (a g : Nat) (ha : a + 16 ≤ 2 ^ 24)
    (ha8 : a % 8 = 0) (hg : g < 2048) (h6 : s.getReg .x6 = BitVec.ofNat 64 a)
    (hgm : s.getMem (BitVec.ofNat 64 (a + 8)) = BitVec.ofNat 64 g) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 295 ∧ t.getReg .x21 = BitVec.ofNat 64 (2048 + g) ∧
      RegsExcept s t [.x7, .x21] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s blk_291.res.st.obl := by
    simp only [blk_291.res]
    t3n [h6]
    omega
  refine ⟨_, symRun_sound blk_291 codeAt_291 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · simp [blk_291.res, E.eval]
  · simp only [Result.toState_getReg, blk_291.res]; t3n [h6, hgm]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_291.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_291.res, rv_simp]

/-- `fr_nonext` (295): `LEV = DSTART`. -/
theorem blk295_spec (s : MachineState) (hpc : s.pc = pcOf 295) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 296 ∧ t.getReg .x22 = s.getReg .x23 ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_295 codeAt_295 s hpc (by simp [blk_295.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_295.res, E.eval]
  · simp [blk_295.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_295.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_295.res, rv_simp]

/-- `fr_desc` (296): `LEV = 0` ends the descent. -/
theorem blk296_spec (s : MachineState) (hpc : s.pc = pcOf 296) (l : Nat) (hl : l < 2 ^ 64)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if l = 0 then pcOf 310 else pcOf 297) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_296 codeAt_296 s hpc (by simp [blk_296.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_296.res, E.eval, CmpOp.eval, h22]
    by_cases h : l = 0
    · subst h; simp
    · rw [if_neg h]
      have : BitVec.ofNat 64 l ≠ 0#64 := fun he => h (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hl] at this)
      simp [this]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_296.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_296.res, rv_simp]

theorem shift_dec (l : Nat) (hl : l < 64) :
    (BitVec.ofNat 64 (l + 1) + 18446744073709551615#64).toNat % 64 = l := by
  rw [show (18446744073709551615#64 : Word) = BitVec.ofNat 64 18446744073709551615 from rfl, ofNat_add_ofNat,
    BitVec.toNat_ofNat]
  omega

theorem bit_beq (x : Nat) : ((BitVec.ofNat 64 x &&& 1#64) == 0#64) = decide (x % 2 = 0) := by
  rw [ofNat_and1]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

theorem bit_bne (x : Nat) : ((BitVec.ofNat 64 x &&& 1#64) != 0#64) = decide (x % 2 = 1) := by
  rw [ofNat_and1]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> rw [h] <;> decide

theorem ofNat_xor1 (v : Nat) (hv : v < 2 ^ 64) : BitVec.ofNat 64 v ^^^ 1#64 = BitVec.ofNat 64 (v ^^^ 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, toNat_ofNat_lt hv, toNat_ofNat_lt (Nat.xor_lt_two_pow hv (by norm_num))]
  rfl

theorem toNat_mod64 (l : Nat) (hl : l < 64) : (BitVec.ofNat 64 l).toNat % 64 = l := by
  rw [toNat_ofNat_lt (by omega)]; omega

/-- 297..300: `LEV -= 1`, `t1 = HS >> LEV`; a left child (bit 0) continues the descent. -/
theorem blk297_spec (s : MachineState) (hpc : s.pc = pcOf 297) (l hs : Nat) (hl : l < 64)
    (hhs : hs < 2 ^ 64) (h22 : s.getReg .x22 = BitVec.ofNat 64 (l + 1))
    (h20 : s.getReg .x20 = BitVec.ofNat 64 hs) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = (if hs / 2 ^ l % 2 = 0 then pcOf 296 else pcOf 301) ∧
      t.getReg .x22 = BitVec.ofNat 64 l ∧ t.getReg .x6 = BitVec.ofNat 64 (hs / 2 ^ l) ∧
      RegsExcept s t [.x6, .x7, .x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_297 codeAt_297 s hpc (by simp [blk_297.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_297.res, E.eval, CmpOp.eval, BinOp.eval, h22, h20, shift_dec l hl,
      ofNat_shr hs l hhs, bit_beq]
    by_cases h : hs / 2 ^ l % 2 = 0 <;> simp [h]
  · simp only [Result.toState_getReg, blk_297.res]
    t3n [h22, h20]
    omega
  · simp only [Result.toState_getReg, blk_297.res]
    t3n [h22, h20]
    rw [show (l + 1 + 18446744073709551615) % 18446744073709551616 % 64 = l by omega, ofNat_shr hs l hhs]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_297.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_297.res, rv_simp]

/-- Emit node `v ^^^ 1` of the arena (`[PP] := node`, `PP += 16`): 301..309 (back to `fr_desc`). -/
theorem blk301_spec (s : MachineState) (hpc : s.pc = pcOf 301) (v pp : Nat) (hv : v < 4096)
    (hpp : pp + 16 ≤ 2 ^ 24) (hpp8 : pp % 8 = 0)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 v) (h2 : s.getReg .x2 = BitVec.ofNat 64 FTS)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 pp) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf 296 ∧ t.getReg .x16 = BitVec.ofNat 64 (pp + 16) ∧
      t.getMem (BitVec.ofNat 64 pp) = s.getMem (BitVec.ofNat 64 (FTS + 16 * (v ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (pp + 8)) = s.getMem (BitVec.ofNat 64 (FTS + 16 * (v ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x16, .x28] ∧ Frame s t (fun A => A = pp ∨ A = pp + 8) := by
  have hx : v ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hv (by norm_num)
  have hobl : Oblig.all s blk_301.res.st.obl := by
    simp only [blk_301.res]
    t3n [h6, h2, h16, ofNat_xor1 v (by omega)]
    sg_omega
  refine ⟨_, symRun_sound blk_301 codeAt_301 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_301.res, E.eval]
  · simp only [Result.toState_getReg, blk_301.res]; t3n [h16]
  · simp only [Result.toState_getMem, blk_301.res, FTS]
    t3n [h6, h2, h16, ofNat_xor1 v (by omega)]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2; sg_omega
  · simp only [Result.toState_getMem, blk_301.res, FTS]
    t3n [h6, h2, h16, ofNat_xor1 v (by omega)]
    try rw [if_pos (by omega)]
    congr 2; sg_omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_301.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_301.res]
    t3n [h16]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fr_asc_init` (310): `LEV = 0`. -/
theorem blk310_spec (s : MachineState) (hpc : s.pc = pcOf 310) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 311 ∧ t.getReg .x22 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_310 codeAt_310 s hpc (by simp [blk_310.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_310.res, E.eval]
  · simp [blk_310.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_310.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_310.res, rv_simp]

/-- `fr_asc` (311): `LEV ≥ 8` ends the ascent. -/
theorem blk311_spec (s : MachineState) (hpc : s.pc = pcOf 311) (l : Nat) (hl : l < 2 ^ 63)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if l < 8 then pcOf 313 else pcOf 328) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_311 codeAt_311 s hpc (by simp [blk_311.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_311.res, E.eval, CmpOp.eval, h22, ofNat_slt l 8 hl (by norm_num)]
    by_cases h : l < 8 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_311.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_311.res, rv_simp]

/-- 313..315: `t1 = HS >> LEV`; a right child (bit 1) skips to `fr_asc_next`. -/
theorem blk313_spec (s : MachineState) (hpc : s.pc = pcOf 313) (l hs : Nat) (hl : l < 64)
    (hhs : hs < 2 ^ 64) (h22 : s.getReg .x22 = BitVec.ofNat 64 l)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 hs) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if hs / 2 ^ l % 2 = 1 then pcOf 326 else pcOf 316) ∧
      t.getReg .x6 = BitVec.ofNat 64 (hs / 2 ^ l) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_313 codeAt_313 s hpc (by simp [blk_313.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_313.res, E.eval, CmpOp.eval, BinOp.eval, h22, h20, toNat_mod64 l hl,
      ofNat_shr hs l hhs, bit_bne]
    by_cases h : hs / 2 ^ l % 2 = 1 <;> simp [h]
  · simp only [Result.toState_getReg, blk_313.res]
    t3n [h22, h20]
    rw [show l % 18446744073709551616 % 64 = l by omega, ofNat_shr hs l hhs]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_313.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_313.res, rv_simp]

/-- 316..318: `t1 ^= 1`; the next leaf's ancestor equal to the sibling ends the ascent. -/
theorem blk316_spec (s : MachineState) (hpc : s.pc = pcOf 316) (l v nxt : Nat) (hl : l < 64)
    (hv : v < 2 ^ 64) (hnxt : nxt < 2 ^ 64) (h22 : s.getReg .x22 = BitVec.ofNat 64 l)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 v) (h21 : s.getReg .x21 = BitVec.ofNat 64 nxt) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if nxt / 2 ^ l = v ^^^ 1 then pcOf 328 else pcOf 319) ∧
      t.getReg .x6 = BitVec.ofNat 64 (v ^^^ 1) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  have hx : v ^^^ 1 < 2 ^ 64 := Nat.xor_lt_two_pow hv (by norm_num)
  refine ⟨_, symRun_sound blk_316 codeAt_316 s hpc (by simp [blk_316.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_316.res, E.eval, CmpOp.eval, BinOp.eval, h22, h6, h21,
      toNat_mod64 l hl, ofNat_shr nxt l hnxt, ofNat_xor1 v hv]
    by_cases h : nxt / 2 ^ l = v ^^^ 1
    · rw [if_pos h, h]; simp
    · rw [if_neg h]
      have : ¬ (BitVec.ofNat 64 (nxt / 2 ^ l) = BitVec.ofNat 64 v ^^^ 1#64) := by
        rw [ofNat_xor1 v hv]
        exact fun he => h ((ofNat_inj (lt_of_le_of_lt (Nat.div_le_self _ _) hnxt) hx).mp he)
      simp [this]
  · simp only [Result.toState_getReg, blk_316.res, rv_simp, h6]
    exact ofNat_xor1 v hv
  · intro r hr; simp at hr; cases r <;> simp_all [blk_316.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_316.res, rv_simp]

/-- 319..325: emit node `v` (`[PP] := node v`, `PP += 16`), on to `fr_asc_next`. -/
theorem blk319_spec (s : MachineState) (hpc : s.pc = pcOf 319) (v pp : Nat) (hv : v < 4096)
    (hpp : pp + 16 ≤ 2 ^ 24) (hpp8 : pp % 8 = 0)
    (h6 : s.getReg .x6 = BitVec.ofNat 64 v) (h2 : s.getReg .x2 = BitVec.ofNat 64 FTS)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 pp) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = pcOf 326 ∧ t.getReg .x16 = BitVec.ofNat 64 (pp + 16) ∧
      t.getMem (BitVec.ofNat 64 pp) = s.getMem (BitVec.ofNat 64 (FTS + 16 * v)) ∧
      t.getMem (BitVec.ofNat 64 (pp + 8)) = s.getMem (BitVec.ofNat 64 (FTS + 16 * v + 8)) ∧
      RegsExcept s t [.x6, .x7, .x16, .x28] ∧ Frame s t (fun A => A = pp ∨ A = pp + 8) := by
  have hobl : Oblig.all s blk_319.res.st.obl := by
    simp only [blk_319.res]
    t3n [h6, h2, h16]
    sg_omega
  refine ⟨_, symRun_sound blk_319 codeAt_319 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_319.res, E.eval]
  · simp only [Result.toState_getReg, blk_319.res]; t3n [h16]
  · simp only [Result.toState_getMem, blk_319.res, FTS]
    t3n [h6, h2, h16]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 2; sg_omega
  · simp only [Result.toState_getMem, blk_319.res, FTS]
    t3n [h6, h2, h16]
    try rw [if_pos (by omega)]
    congr 2; sg_omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_319.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_319.res]
    t3n [h16]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fr_asc_next` (326..327): `LEV += 1`, back to `fr_asc`. -/
theorem blk326_spec (s : MachineState) (hpc : s.pc = pcOf 326) (l : Nat)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 311 ∧ t.getReg .x22 = BitVec.ofNat 64 (l + 1) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_326 codeAt_326 s hpc (by simp [blk_326.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_326.res, E.eval]
  · simp only [Result.toState_getReg, blk_326.res]; t3n [h22]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_326.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_326.res, rv_simp]

/-- `fr_asc_done` (328..330): `DSTART = LEV`, `J += 1`, back to `fr_leaf`. -/
theorem blk328_spec (s : MachineState) (hpc : s.pc = pcOf 328) (j : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 280 ∧ t.getReg .x23 = s.getReg .x22 ∧
      t.getReg .x19 = BitVec.ofNat 64 (j + 1) ∧ RegsExcept s t [.x19, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_328 codeAt_328 s hpc (by simp [blk_328.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_328.res, E.eval]
  · simp [blk_328.res, rv_simp]
  · simp only [Result.toState_getReg, blk_328.res]; t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_328.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_328.res, rv_simp]

/-- `fr_done` (331): `LEV = 8`. -/
theorem blk331_spec (s : MachineState) (hpc : s.pc = pcOf 331) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 332 ∧ t.getReg .x22 = BitVec.ofNat 64 8 ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_331 codeAt_331 s hpc (by simp [blk_331.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_331.res, E.eval]
  · simp [blk_331.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_331.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_331.res, rv_simp]

/-- `fr_outer` (332): `LEV ≥ 11` ends the outer siblings. -/
theorem blk332_spec (s : MachineState) (hpc : s.pc = pcOf 332) (l : Nat) (hl : l < 2 ^ 63)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if l < 11 then pcOf 334 else pcOf 345) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_332 codeAt_332 s hpc (by simp [blk_332.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_332.res, E.eval, CmpOp.eval, h22, ofNat_slt l 11 hl (by norm_num)]
    by_cases h : l < 11 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_332.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_332.res, rv_simp]

/-- 334..344: emit the outer sibling `(HS >> LEV) ^ 1`, `LEV += 1`, back to `fr_outer`. -/
theorem blk334_spec (s : MachineState) (hpc : s.pc = pcOf 334) (l hs pp : Nat) (hl : l < 64)
    (hhs : hs < 4096) (hpp : pp + 16 ≤ 2 ^ 24) (hpp8 : pp % 8 = 0)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 l) (h20 : s.getReg .x20 = BitVec.ofNat 64 hs)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 FTS) (h16 : s.getReg .x16 = BitVec.ofNat 64 pp) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 332 ∧ t.getReg .x22 = BitVec.ofNat 64 (l + 1) ∧
      t.getReg .x16 = BitVec.ofNat 64 (pp + 16) ∧
      t.getMem (BitVec.ofNat 64 pp) = s.getMem (BitVec.ofNat 64 (FTS + 16 * (hs / 2 ^ l ^^^ 1))) ∧
      t.getMem (BitVec.ofNat 64 (pp + 8)) = s.getMem (BitVec.ofNat 64 (FTS + 16 * (hs / 2 ^ l ^^^ 1) + 8)) ∧
      RegsExcept s t [.x6, .x7, .x16, .x22, .x28] ∧ Frame s t (fun A => A = pp ∨ A = pp + 8) := by
  have hd : hs / 2 ^ l < 4096 := lt_of_le_of_lt (Nat.div_le_self _ _) hhs
  have hx : hs / 2 ^ l ^^^ 1 < 4096 := Nat.xor_lt_two_pow (n := 12) hd (by norm_num)
  have e1 : BitVec.ofNat 64 hs >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64 =
      BitVec.ofNat 64 (hs / 2 ^ l ^^^ 1) := by
    rw [toNat_mod64 l hl, ofNat_shr hs l (by omega), ofNat_xor1 _ (by omega)]
  have hobl : Oblig.all s blk_334.res.st.obl := by
    simp only [blk_334.res]
    simp only [rv_simp, h22, h20, h2, h16, e1]
    t3n []
    sg_omega
  refine ⟨_, symRun_sound blk_334 codeAt_334 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_334.res, E.eval]
  · simp only [Result.toState_getReg, blk_334.res]; t3n [h22]
  · simp only [Result.toState_getReg, blk_334.res]; t3n [h16]
  · simp only [Result.toState_getMem, blk_334.res, FTS]
    simp only [rv_simp, h22, h20, h2, h16, e1]
    t3n []
    ite_close
  · simp only [Result.toState_getMem, blk_334.res, FTS]
    simp only [rv_simp, h22, h20, h2, h16, e1]
    t3n []
    ite_close
  · intro r hr; simp at hr; cases r <;> simp_all [blk_334.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, blk_334.res]
    t3n [h16]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `fr_outer_done` (345..346): `t3 = 16 coord`; coordinate 0 skips the header slot. -/
theorem blk345_spec (s : MachineState) (hpc : s.pc = pcOf 345) (c : Nat) (hc : c < 7)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c = 0 then pcOf 348 else pcOf 347) ∧
      t.getReg .x28 = BitVec.ofNat 64 (16 * c) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_345 codeAt_345 s hpc (by simp [blk_345.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_345.res, E.eval, CmpOp.eval, h8]
    by_cases h : c = 0
    · subst h; simp
    · rw [if_neg h]
      have : BitVec.ofNat 64 c ≠ 0#64 := fun he => h (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt (by omega)] at this)
      simp [this]
  · simp only [Result.toState_getReg, blk_345.res]; t3n [h8]; omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_345.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_345.res, rv_simp]

/-- 347: `t3 += 16`. -/
theorem blk347_spec (s : MachineState) (hpc : s.pc = pcOf 347) (o : Nat)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 348 ∧ t.getReg .x28 = BitVec.ofNat 64 (o + 16) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_347 codeAt_347 s hpc (by simp [blk_347.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_347.res, E.eval]
  · simp only [Result.toState_getReg, blk_347.res]; t3n [h28]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_347.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_347.res, rv_simp]

/-- `fr_root0` (348..356): the root (heap node 1) to `FOREST + o`, `coord += 1`, back to `fts_coord`. -/
theorem blk348_spec (s : MachineState) (hpc : s.pc = pcOf 348) (o c : Nat) (ho : o ≤ 112) (ho8 : o % 8 = 0)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 o) (h2 : s.getReg .x2 = BitVec.ofNat 64 FTS)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf 186 ∧ t.getReg .x8 = BitVec.ofNat 64 (c + 1) ∧
      t.getMem (BitVec.ofNat 64 (FOREST + o)) = s.getMem (BitVec.ofNat 64 (FTS + 16)) ∧
      t.getMem (BitVec.ofNat 64 (FOREST + o + 8)) = s.getMem (BitVec.ofNat 64 (FTS + 24)) ∧
      RegsExcept s t [.x6, .x7, .x8, .x28, .x29] ∧
      Frame s t (fun A => A = FOREST + o ∨ A = FOREST + o + 8) := by
  have hobl : Oblig.all s blk_348.res.st.obl := by
    simp only [blk_348.res]
    t3n [h28, h2]
    obl_omega
  refine ⟨_, symRun_sound blk_348 codeAt_348 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_348.res, E.eval]
  · simp only [Result.toState_getReg, blk_348.res]; t3n [h8]
  · simp only [Result.toState_getMem, blk_348.res, FOREST, FTS]
    t3n [h28, h2]
    rw [if_neg (by omega), if_pos (by omega)]
  · simp only [Result.toState_getMem, blk_348.res, FOREST, FTS]
    t3n [h28, h2]
    try rw [if_pos (by omega)]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_348.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [FOREST] at hn
    simp only [Result.toState_getMem, blk_348.res]
    t3n [h28, h2]
    rw [if_neg (by sg_omega), if_neg (by sg_omega)]

end SigGolfCandidate.T3M.Sign
