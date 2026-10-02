import SigGolfCandidate.T3M.Search.SelectOk
import SigGolfCandidate.T3M.Search.CounterSearch

/-!
# The digest search (`ds_loop` + `select_ok`) refines Core's `digestSearch` (stream E)

The loop `ds_loop` (19 words at `d`: expand `d = 30`, sign `d = 153`) with the kernel at `b`
(expand 354, sign 543): per trial `I = s3 < 2^20` it writes `T12(I)` into the digest block
(`DIG + 16`, `DIG + 24`), HASHes `rho | T12(I) | m` (64 bytes at `DIG`) into `NBUF`, calls
`select_ok` (`b + 3`) and leaves for `ds_done` (`d + 19`) iff `a3 ≠ 0`, else `I += 1`;
`I = 2^20` jumps to `fail` (`b`).

* `digestSearch_tbsim`: from `DsPre` (`d`, `I = 0`), the machine refines
  `digestSearch rho m 0 attemptLimit` within `2^20 · 666 + 664` cycles (a failing trial costs
  `26 + k ≤ 666` cycles, `k ≤ 640` the `select_ok` run), ending in `DsPost`;
* `digestSearch_spec`: the same in the shape of t3m/s `Sign/Kernels.lean` (`DigestSearchSpec`).
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The digest block -/

theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) : (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, SphincsSecurity.bytesLE_length]

theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    T3.pad64 (T3.digestInput rho m c) = T3.digestInput rho m c := by
  unfold T3.pad64
  rw [digestInput_length]
  simp

theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 12 0 0 0),
        BitVec.ofNat 64 (hdr1 0 c.toNat), m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput]
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_bytesLE32]
  rfl

theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]

/-- One HASH `ECALL` answering a public query `publicHash input`. -/
theorem TBSim.publicHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h

/-! ## Block specifications -/

section blocks
variable {image : Image} {d b : Nat}

/-- `ds_loop`: `I = 2^20` jumps to `fail`. -/
theorem ds0_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 0)) (i : Nat)
    (hi : i ≤ 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 20 then pcOf (b + 0) else pcOf (d + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds0 hD.2) (codeAt_ds_0 hD) s hpc (by simp [stds_0, blkds30_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_0, rebase, blkds30_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 20
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 1048576#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_0, blkds30_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_0, blkds30_0.res, rv_simp]

/-- The digest block's header `T12(I)` and the HASH arguments (`a0 = DIG`, `a1 = 64`, `a2 = NBUF`). -/
theorem ds2_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 2)) (i : Nat)
    (hi : i < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (d + 14) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 (hdr0 12 0 0 0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 (hdr1 0 i) ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run_ds2 hD.2) (codeAt_ds_2 hD) s hpc
    (by simp [stds_2, blkds30_2.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcEds_2, E.eval]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [DIG]
    rfl
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [h19, DIG]
    rw [hdr1_eq 0 i (by decide) (by omega)]
    congr 1
    omega
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_2, blkds30_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]

/-- The HASH `ECALL` (`d + 14`). -/
theorem ds14_fetch (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 14)) :
    fetch image s = some (.base .ECALL) :=
  ((codeAt_ds_14 hD).fetch s hpc).trans rfl

/-- `jal ra, select_ok`. -/
theorem ds15_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 15)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 3) ∧ t.getReg .x1 = pcOf (d + 16) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds15 hD.2) (codeAt_ds_15 hD) s hpc
    (by simp [stds_15, blkds30_15.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_15, E.eval]
  · simp [stds_15, blkds30_15.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_15, blkds30_15.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [stds_15, blkds30_15.res, rv_simp]

/-- `bne a3, zero, ds_done`. -/
theorem ds16_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 16)) (ok : Bool)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if ok then pcOf (d + 19) else pcOf (d + 17)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds16 hD.2) (codeAt_ds_16 hD) s hpc
    (by simp [stds_16, blkds30_16.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_16, rebase, blkds30_16.res, E.eval, CmpOp.eval, h13]
    cases ok <;> simp
  · intro r hr; simp at hr; cases r <;> simp_all [stds_16, blkds30_16.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_16, blkds30_16.res, rv_simp]

/-- `I += 1`, back to `ds_loop`. -/
theorem ds17_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 17)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (d + 0) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds17 hD.2) (codeAt_ds_17 hD) s hpc
    (by simp [stds_17, blkds30_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_17, E.eval]
  · simp only [Result.toState_getReg, stds_17, blkds30_17.res]
    t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_17, blkds30_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_17, blkds30_17.res, rv_simp]

end blocks

/-! ## Interface: entry, exit, footprint (the shape of t3m/s `Sign/Kernels.lean`) -/

/-- Registers the digest search may change (S's `dsRegs`). -/
abbrev dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]

/-- Doublewords the digest search may change: the counter header, `NBUF`, the selection rows (S's `DsW`). -/
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)

/-- Entry of the digest search (`d` = `ds_loop`, `I = 0`; S's `DsPre` at `d = 153`). -/
structure DsPre (d : Nat) (s : MachineState) (rho : Digest) (m : T3.Message) : Prop where
  pc : s.pc = pcOf d
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64

/-- Entry `j` of selection row `c`: `256 bucket + x_j` (S's `selEntry`). -/
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((T3.selections N).getD c ⟨0, []⟩).bucket * 256 + ((T3.selections N).getD c ⟨0, []⟩).leaves.getD j 0

/-- The selection rows of `N` at `SEL` (row `c` at `SEL + 24 c`; S's `SelRows`). -/
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)

/-- A 256-bit value stored as four little-endian doublewords at `A` (S's `OutAt`). -/
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64

/-- Exit of the digest search: `fail` on exhaustion, else `ds_done` (`d + 19`) with `N` and the
counter `c` in `s3`. -/
def DsPost (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (c, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW ∧
      c.toNat < 2 ^ 20 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat

/-- S's exit (`DsPost` without the counter facts). -/
def DsPostS (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW

/-- S's all-oracle cycle bound of the digest search (≤ 700 cycles per trial). -/
def dsCostS : Nat := T3.attemptLimit * 700 + 100

theorem selEntry_eq (N : HashOutput) (c j : Nat) (hc : c < 7) :
    selEntry N c j = selBucket N c * 256 + (selRow N c).getD j 0 := by
  simp [selEntry, selections_eq, List.getD_eq_getElem?_getD, hc]

theorem NAt.writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    NAt (writeHash t a) a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp

/-! ## The loop -/

section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}

/-- The invariant at `ds_loop` (`d`) before trial `i`. -/
structure DsInv (d : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (d + 0)
  hi : i ≤ 2 ^ 20
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t dsRegs
  frame : Frame s0 t DsW

/-- **The search loop**: from `ds_loop` at trial `i` with `F = 2^20 - i` trials left, within
`F · 666 + 664` cycles. -/
theorem ds_loop (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    ∀ F i t, i + F = 2 ^ 20 → DsInv d s0 i t →
      TBSim image sk t (F * 666 + 664) (T3.digestSearch rho m i F) (DsPost b d s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, _⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := DsPost b d s0) (a := none) ⟨p2, h5, h10⟩)
    exact this.mono (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 20 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨u, s2, p2, h16, h24, h10, h11, h12, r2, f2⟩ :=
      ds2_spec hD t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u dsRegs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have u19 : u.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), r1.get (by decide), hI.x19]
    have fu : Frame s0 u DsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with h | h
      · exact h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have mem : ∀ A, A < 2 ^ 64 → ¬ DsW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ DsW A := by
      intro A hA; simp only [DsW, DIG, NBUF, SEL] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (T3.pad64 (T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput, digestInput_length]) h10 (by decide) (by decide)
        h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput, hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : T3.digestSearch rho m i (F + 1) =
        (T3.publicHash (T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if T3.admissible (T3.selections output) then pure (some (BitVec.ofNat 32 i, output))
          else T3.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind (ds14_fetch hD u p2) h5 hv hq
      (W := 644 + (F * 666 + 664)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput]; ring_nf; omega
    -- the answer `a` at `NBUF`
    have pw : (writeHash u a).pc = pcOf (d + 15) := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : NAt (writeHash u a) a := NAt.writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    obtain ⟨t15, s15, p15, h1, r15, f15⟩ := ds15_spec hD (writeHash u a) pw
    obtain ⟨k, t16, s16, hk, p16, h13, hrows, r16, f16⟩ := selectOk_spec hK t15 p15 (d + 16) h1 a
      (NAt.frame hN (f15.mono (fun _ _ h => h.elim)))
    obtain ⟨t17, s17, p17, r17, f17⟩ := ds16_spec hD t16 p16 _ h13
    have r17' : RegsExcept s0 t17 dsRegs :=
      ((((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans r15).trans
        r16).trans r17).mono (by decide)
    have x19' : t17.getReg .x19 = BitVec.ofNat 64 i := by
      rw [r17.get (by decide), r16.get (by decide), r15.get (by decide), getReg_writeHash, u19]
    have f17' : Frame s0 t17 DsW := ((((fu.trans fw).trans f15).trans f16).trans f17).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with (h | h) | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hN17 : NAt t17 a :=
      NAt.frame (NAt.frame (NAt.frame hN (f15.mono (fun _ _ h => h.elim))) f16) (f17.mono (fun _ _ h => h.elim))
    by_cases hadm : T3.admissible (T3.selections a) = true
    · simp only [hadm, ↓reduceIte] at p17 ⊢
      refine (TBSim.steps (s15.trans (s16.trans s17)) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
      refine ⟨p17, by rw [r17'.get (by decide), hpre.x5], hadm, hN17, ?_, r17', f17', by rw [hc]; exact hi,
        by rw [hc, x19']⟩
      intro c hc7 j hj
      rw [f17.get (by simp only [SEL]; omega) (fun h => h), hrows hadm c hc7 j hj, selEntry_eq a c j hc7]
    · have hadm' : T3.admissible (T3.selections a) = false := by simpa using hadm
      simp only [hadm', Bool.false_eq_true, ↓reduceIte] at p17 ⊢
      obtain ⟨t18, s18, p18, h19, r18, f18⟩ := ds17_spec hD t17 p17 i x19'
      have hI' : DsInv d s0 (i + 1) t18 :=
        ⟨p18, by omega, h19, (r17'.trans r18).mono (by decide),
          (f17'.trans f18).mono (fun A _ h => by simp only [or_false] at h; exact h)⟩
      refine (TBSim.steps (s15.trans (s16.trans (s17.trans s18))) (ih (i + 1) t18 (by omega) hI')).mono
        (by omega) (fun _ _ h => h)

/-- **The digest search refines Core's `digestSearch`** (`ds_loop` at `d`, kernel at `b`): from `DsPre`,
`digestSearch rho m 0 attemptLimit` query for query within `2^20 · 666 + 664` cycles, ending in `DsPost`. -/
theorem digestSearch_tbsim (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    TBSim image sk s0 (2 ^ 20 * 666 + 664) (T3.digestSearch rho m 0 T3.attemptLimit) (DsPost b d s0) :=
  ds_loop hD hK hpre (2 ^ 20) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩

/-- **The digest search at any placement, in S's shape** (`DigestSearchSpec` at `d = 153`, `b = 543`). -/
theorem digestSearch_spec (hD : DsAt image d b) (hK : KernAt image b) (s : MachineState) (rho : Digest)
    (m : T3.Message) (h : DsPre d s rho m) :
    TBSim image sk s dsCostS (T3.digestSearch rho m 0 T3.attemptLimit) (DsPostS b d s) := by
  refine (digestSearch_tbsim (sk := sk) hD hK h).mono (by unfold dsCostS T3.attemptLimit; omega)
    (fun r t ht => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1⟩

end loop

end SigGolfCandidate.T3M.Search
