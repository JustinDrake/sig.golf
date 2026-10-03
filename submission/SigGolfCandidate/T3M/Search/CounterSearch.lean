import SigGolfCandidate.T3M.Search.CsDigits
import SigGolfCandidate.T3M.Sim
import SigGolfCandidate.T3M.Search.TopTables
import SigGolfCandidate.T3M.Search.Params
import SigGolfCandidate.T3M.Search.TopCheck
import SigGolfCandidate.T3M.Search.TopUnpack

/-!
# `counter_search` refines Core's `counterSearch` (stream E; sign base 543, expand base 354)

**`counterSearch_tbsim`**: from the kernel entry (`b + 103`) with the arguments in registers and the
message in the encoding block (`CsPre`), the machine runs Core's
`counterSearch lay tree leaf M 0 counterLimit` query for query, within
`10 + 2^22 · csT lay + csOk lay` cycles: a failing trial costs at most `csT lay` (158 lower, 201 top),
the successful one at most `csOk lay` (incl. the digit bytes), exhaustion `HALT(1)`s at `fail`
(`CsPost none`). On success (`CsPost (some (c, ds))`) it returns to `ret` with `s3 = c`, the digit
bytes `ds` at `DIGITS` (`ds = decode`), changing only `csRegs` and `CsW`.
-/

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer)

set_option linter.unusedSimpArgs false

/-! ## The encoding block -/

theorem pad64_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    T3.pad64 (T3.encodingInput lay tree leaf msg c) =
      T3.encodingInput lay tree leaf msg c ++ List.replicate 28 0 := by
  unfold T3.pad64
  simp only [T3.encodingInput, List.length_append, SphincsSecurity.bytesLE_length]

theorem wordsOf_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.encodingInput lay tree leaf msg c)) =
      [msg.extractLsb' 0 64, msg.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 4 lay.val tree 0),
        BitVec.ofNat 64 (hdr1 tree leaf), BitVec.ofNat 64 c.toNat, 0, 0, 0] := by
  rw [pad64_encodingInput]
  unfold T3.encodingInput
  have e : SphincsSecurity.bytesLE 16 msg ++ SphincsSecurity.bytesLE 16 (T3.header 4 lay.val tree 0 leaf) ++
      SphincsSecurity.bytesLE 4 c ++ List.replicate 28 0 =
      SphincsSecurity.bytesLE 16 msg ++ SphincsSecurity.bytesLE 16 (T3.header 4 lay.val tree 0 leaf) ++
        ((SphincsSecurity.bytesLE 4 c ++ List.replicate 4 0) ++ List.replicate 24 0) := by
    simp only [List.append_assoc]
    rfl
  have hc : T3.readLE (SphincsSecurity.bytesLE 4 c ++ List.replicate 4 0) = c.toNat := by
    rw [readLE_append, readLE_bytesLE, readLE_replicate_zero]
    simp
  rw [e, wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_header,
    wordsOf_append8 _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length, List.length_replicate]),
    hc, show (24 : Nat) = 8 * 3 by rfl, wordsOf_replicate_zero]
  rfl

theorem encodingInput_length (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (T3.pad64 (T3.encodingInput lay tree leaf msg c)).length = 64 := by
  rw [pad64_encodingInput]
  simp only [T3.encodingInput, List.length_append, SphincsSecurity.bytesLE_length, List.length_replicate]

theorem blocks_encodingInput (lay : Layer) (tree leaf : Nat) (msg : Digest) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.encodingInput lay tree leaf msg c))).blocks = 1 := by
  have hl := encodingInput_length lay tree leaf msg c
  rw [blocks_toQ (by rw [Aligned, hl]; omega), hl]

/-! ## `TBSim` with a `shortHash` -/

theorem TBSim.shortHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this

/-! ## Arguments, invariant, postcondition -/

/-- The arguments of one `counter_search` call. -/
structure CsArgs where
  lay : Layer
  tree : Nat
  leaf : Nat
  msg : Digest
  ret : Nat

/-- Cycles of a failing trial: 201 (top), 158 (lower layers). -/
def csT (lay : Layer) : Nat := if lay = 0 then 201 else 158

/-- Cycles of the successful trial incl. the digit bytes and the return (or of the exhaustion). -/
def csOk (lay : Layer) : Nat := if lay = 0 then 1308 else 967

/-- The registers `counter_search` may change. -/
abbrev csRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x25, .x28, .x29, .x30]

/-- The memory `counter_search` may change: the header, counter and answer doublewords of the
encoding block and the digit table. -/
def CsW (A : Nat) : Prop :=
  A = ENC + 16 ∨ A = ENC + 24 ∨ A = ENC + 32 ∨ (EOUT ≤ A ∧ A < EOUT + 32) ∨ DigW A

/-- The precondition at the entry `b + 103`. -/
structure CsPre (b : Nat) (A : CsArgs) (s : MachineState) : Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf A.ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 A.lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 A.tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 A.leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target A.lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount A.lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 A.lay)
  htree : A.tree < 2 ^ 32
  hleaf : A.leaf < 2 ^ 32
  m0 : s.getMem (BitVec.ofNat 64 ENC) = A.msg.extractLsb' 0 64
  m8 : s.getMem (BitVec.ofNat 64 (ENC + 8)) = A.msg.extractLsb' 64 64
  c32 : ∃ x < 2 ^ 32, s.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  z48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = 0
  z56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = 0
  table : TableOK s

/-- The invariant at `cs_loop` (`b + 113`) before trial `i`. -/
structure CsInv (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 113)
  hi : i ≤ 2 ^ 22
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  h16 : t.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : t.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : ∃ x < 2 ^ 32, t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 x
  regs : RegsExcept s0 t csRegs
  frame : Frame s0 t CsW

/-- The postcondition: `none` halts with `HALT(1)` at `fail`; `some (c, ds)` returns to `ret` with
`s3 = c`, the counter in the encoding block, `ds` decoded from some answer and written to `DIGITS`. -/
def CsPost (image : Image) (b : Nat) (A : CsArgs) (s0 : MachineState) : Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf (b + 2) ∧ t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 1 ∧
      fetch image t = some (.base .ECALL)
  | some (c, ds), t => t.pc = pcOf A.ret ∧ c.toNat < 2 ^ 22 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat ∧
      t.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 c.toNat ∧
      (∃ v, T3.decode A.lay v = some ds) ∧ ds.length = T3.chainCount A.lay ∧
      (∀ j < T3.chainCount A.lay, t.getByte (BitVec.ofNat 64 (DIGITS + j)) = BitVec.ofNat 8 (ds.getD j 0)) ∧
      RegsExcept s0 t csRegs ∧ Frame s0 t CsW ∧ (t.getReg .x25).toNat ≤ T3.target A.lay

/-! ## One trial -/

/-- The trial state (`I = i`) between the counter store and the next loop head. -/
structure TrialSt (b : Nat) (A : CsArgs) (s0 : MachineState) (i : Nat) (u : MachineState) : Prop where
  x19 : u.getReg .x19 = BitVec.ofNat 64 i
  h16 : u.getMem (BitVec.ofNat 64 (ENC + 16)) = BitVec.ofNat 64 (hdr0 4 A.lay.val A.tree 0)
  h24 : u.getMem (BitVec.ofNat 64 (ENC + 24)) = BitVec.ofNat 64 (hdr1 A.tree A.leaf)
  c32 : u.getMem (BitVec.ofNat 64 (ENC + 32)) = BitVec.ofNat 64 i
  regs : RegsExcept s0 u csRegs
  frame : Frame s0 u CsW

theorem TrialSt.step {b : Nat} {A : CsArgs} {s0 u u' : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {L : List Reg} (hr : RegsExcept u u' L)
    (hL : L.all (fun r => decide (r ∈ csRegs ∧ r ≠ .x19)) = true) (hf : Frame u u' (fun _ => False)) :
    TrialSt b A s0 i u' := by
  have hL' : ∀ r ∈ L, r ∈ csRegs ∧ r ≠ .x19 := fun r hr => by simpa using List.all_eq_true.1 hL r hr
  have hnot : ∀ r, r ∉ csRegs → r ∉ L := fun r h1 h2 => h1 (hL' r h2).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr.get (fun h' => (hL' _ h').2 rfl), h.x19]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h16]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.h24]
  · rw [hf.get (by simp only [ENC]; omega) (by simp), h.c32]
  · exact (h.regs.trans hr).mono (fun r hr' => by
      rcases List.mem_append.1 hr' with h1 | h1
      · exact h1
      · exact (hL' r h1).1)
  · exact (h.frame.trans hf).mono (fun A _ h' => by simp only [or_false] at h'; exact h')

theorem TrialSt.reg {b : Nat} {A : CsArgs} {s0 u : MachineState} {i : Nat} (h : TrialSt b A s0 i u)
    {r : Reg} (hr : r ∉ csRegs) : u.getReg r = s0.getReg r := h.regs.get hr

section trial
variable {image : Image} {b : Nat} {sk : BitVec 256}

/-- A failing trial ends at `cs_next`: `I += 1` and the loop invariant for `i + 1`. -/
theorem cs_next {A : CsArgs} {s0 u : MachineState} {i F W : Nat} {Q : Option (BitVec 32 × List Nat) → MachineState → Prop}
    (hK : KernAt image b) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 468)) (hi : i < 2 ^ 22)
    (ih : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t W (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q) :
    TBSim image sk u (2 + W) (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) Q := by
  obtain ⟨t1, s1, p1, h19, r1, f1⟩ := cs468_spec hK u hpc i hu.x19
  refine TBSim.steps s1 (ih t1 ⟨p1, by omega, h19, ?_, ?_, ⟨i, by omega, ?_⟩, ?_, ?_⟩)
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h16]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.h24]
  · rw [f1.get (by simp only [ENC]; omega) (by simp), hu.c32]
  · exact (hu.regs.trans r1).mono (by decide)
  · exact (hu.frame.trans f1).mono (fun A _ h' => by simp only [or_false] at h'; exact h')

theorem chainCount_eq (lay : Layer) : T3.chainCount lay = if lay = 0 then 54 else 43 := by
  fin_cases lay <;> rfl

theorem target_lt (lay : Layer) : T3.target lay < 2 ^ 63 := by
  fin_cases lay <;> decide

theorem getD_map_range {f : Nat → Nat} {n j : Nat} (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

/-- A lower-layer successful trial writes the original binary-radix digit bytes. -/
theorem cs_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 438)) (hi : i < 2 ^ 22) (hlz : A.lay ≠ 0)
    (v : Digest) (S : Nat) (ds : List Nat) (hdec : T3.decode A.lay v = some ds)
    (hds : ds = lowDigits v ++ [T3.target A.lay - S]) (hS : S ≤ T3.target A.lay)
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h25 : u.getReg .x25 = BitVec.ofNat 64 S) :
    TBSim image sk u 810 (pure (some (BitVec.ofNat 32 i, ds))) (CsPost image b A s0) := by
  have hl0 : A.lay.val ≠ 0 := fun h => hlz (Fin.ext h)
  obtain ⟨k, t, st, kle, tpc, tdig, tchk, tr, tf⟩ := cs_tail hK u hpc v A.lay.val
    (T3.target A.lay) S A.ret A.lay.isLt (target_lt _) (fun _ => hS)
    (by rw [hu.reg (by decide), hpre.x1]) (by rw [hu.reg (by decide), hpre.x8])
    (by rw [hu.reg (by decide), hpre.x17]) h25
    (by rw [hu.reg (by decide), hpre.x26, chainCount_eq]; simp [hlz, hl0])
    (by rw [hu.reg (by decide), hpre.x27, csN4]; simp [hlz, hl0]) h6 h7
  rw [if_neg hl0] at kle tdig
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine (TBSim.steps st (TBSim.pure ?_)).mono kle (fun _ _ h => h)
  refine ⟨tpc, by rw [hc]; exact hi, by rw [hc, tr.get (by decide), hu.x19], ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc, tf.get (by simp only [ENC]; omega) (by simp only [DigW, DIGITS, ENC]; omega), hu.c32]
  · rw [hds, chainCount_eq, if_neg hlz]
    simp [lowDigits_length]
  · intro j hj
    rw [chainCount_eq, if_neg hlz] at hj
    rw [hds]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [List.getD_append _ _ _ _ (by rw [lowDigits_length]; exact hj), lowDigits_eq, getD_map_range hj]
      simpa only [if_neg hl0] using tdig j hj
    · rw [List.getD_append_right _ _ _ _ (by rw [lowDigits_length]), lowDigits_length]
      simpa using tchk hl0
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, BitVec.toNat_ofNat]
    have := target_lt A.lay
    omega

/-- The immutable lookup table survives every counter-search write. -/
theorem TrialSt.table {A : CsArgs} {s0 u : MachineState} {i : Nat}
    (hu : TrialSt b A s0 i u) (ht : TableOK s0) : TableOK u :=
  ht.frame hu.frame (by intro j hj; unfold CsW DigW TOP_DATA ENC EOUT DIGITS; omega)

/-- A successful mixed-radix trial writes the 54 decoded digit bytes. -/
theorem cs_top_success {A : CsArgs} {s0 u : MachineState} {i : Nat} (hK : KernAt image b)
    (hpre : CsPre b A s0) (hu : TrialSt b A s0 i u) (hpc : u.pc = pcOf (b + 362))
    (hi : i < 2 ^ 22) (hlz : A.lay = 0) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hvalid : T3.topRanksValid v = true) (hdec : T3.decode A.lay v = some (topDigits v))
    (h6 : u.getReg .x6 = v.extractLsb' 0 64) (h7 : u.getReg .x7 = v.extractLsb' 64 64)
    (h30 : u.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (h25 : u.getReg .x25 = 126#64) :
    TBSim image sk u 302 (pure (some (BitVec.ofNat 32 i, topDigits v))) (CsPost image b A s0) := by
  obtain ⟨t, st, tpc, tdig, tr, tf⟩ := topUnpack_spec hK u v hv hvalid (hu.table hpre.table) hpc h6 h7 h30
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine TBSim.steps st (TBSim.pure ?_)
  refine ⟨?_, by rw [hc]; exact hi, ?_, ?_, ⟨v, hdec⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tpc, hu.reg (by decide), hpre.x1, pcOf_and_not1]
  · rw [hc, tr.get (by decide), hu.x19]
  · rw [hc, tf.get (by unfold ENC; omega) (by unfold TopUnpack.Writes DIGITS ENC; omega), hu.c32]
  · rw [hlz, topDigits_length]; rfl
  · intro j hj
    rw [hlz] at hj
    change j < 54 at hj
    rw [tdig j hj]
    simp only [topDigits, getD_map_range hj]
  · exact (hu.regs.trans tr).mono (by decide)
  · exact (hu.frame.trans tf).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inr h))))
  · rw [tr.get (by decide), h25, hlz]; decide

/-- The answer state after the HASH of trial `i`: the trial state, the answer at `EOUT`. -/
theorem cs_answer {A : CsArgs} {s0 t : MachineState} {i : Nat} (hK : KernAt image b) (hpre : CsPre b A s0)
    (hI : CsInv b A s0 i t) (hi : i < 2 ^ 22) :
    ∃ t2, Steps image t 10 10 t2 ∧ t2.pc = pcOf (b + 123) ∧ fetch image t2 = some (.base .ECALL) ∧
      t2.getReg .x5 = 0 ∧ hashArgumentsValid t2 = true ∧
      hashInput t2 = toQ (T3.pad64 (T3.encodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i))) ∧
      t2.getReg .x12 = BitVec.ofNat 64 EOUT ∧ TrialSt b A s0 i t2 := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
  rw [if_neg (by omega)] at p1
  obtain ⟨x, hx, hx32⟩ := hI.c32
  obtain ⟨t2, s2, p2, c32, h10, h11, h12, r2, f2⟩ := cs115_spec hK t1 p1 i x (by omega) hx
    (by rw [r1.get (by decide), hI.x19]) (by rw [f1.get (by simp only [ENC]; omega) (by simp), hx32])
  have fr : Frame s0 t2 CsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
    simp only [or_false] at h; rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inl h)))
  have mem : ∀ A, A < 2 ^ 64 → ¬ CsW A → t2.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => fr.get hA hn
  have hT : TrialSt b A s0 i t2 := by
    refine ⟨?_, ?_, ?_, c32, ((hI.regs.trans r1).trans r2).mono (by decide), fr⟩
    · rw [r2.get (by decide), r1.get (by decide), hI.x19]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h16]
    · rw [f2.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), f1.get (by simp only [ENC]; omega) (by simp),
        hI.h24]
  refine ⟨t2, s1.trans s2, p2, (codeAt_k_123 hK).fetch _ p2, by rw [hT.reg (by decide), hpre.x5],
    hashArgs_const t2 ENC 64 EOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide),
    ?_, h12, hT⟩
  have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
  refine hashInput_toQ t2 _ 0 ENC (encodingInput_length _ _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [readWords_eight, wordsOf_encodingInput, hc]
  have nw : ∀ A, A = ENC ∨ A = ENC + 8 ∨ A = ENC + 40 ∨ A = ENC + 48 ∨ A = ENC + 56 → ¬ CsW A := by
    intro A hA; simp only [CsW, DigW, ENC, EOUT, DIGITS] at hA ⊢; omega
  rw [mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hT.h16, hT.h24, c32, mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    mem _ (by simp only [ENC]; omega) (nw _ (by omega)), mem _ (by simp only [ENC]; omega) (nw _ (by omega)),
    hpre.m0, hpre.m8, hpre.z40, hpre.z48, hpre.z56]

theorem TrialSt.hash {A : CsArgs} {s0 t2 : MachineState} {i : Nat} (hT : TrialSt b A s0 i t2)
    (h12 : t2.getReg .x12 = BitVec.ofNat 64 EOUT) (a : BitVec 256) : TrialSt b A s0 i (writeHash t2 a) := by
  have fw := Frame.writeHash t2 a EOUT h12 (by decide)
  refine ⟨by rw [getReg_writeHash, hT.x19], ?_, ?_, ?_, ?_, ?_⟩
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h16]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.h24]
  · rw [fw.get (by simp only [ENC]; omega) (by simp only [ENC, EOUT]; omega), hT.c32]
  · intro r hr; rw [getReg_writeHash]; exact hT.regs r hr
  · exact (hT.frame.trans fw).mono (fun A _ h => by
      rcases h with h | h
      · exact h
      · exact Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- **The search loop**: from `cs_loop` at trial `i` with `F = 2^22 - i` trials left. -/
theorem cs_loop {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    ∀ F i t, i + F = 2 ^ 22 → CsInv b A s0 i t →
      TBSim image sk t (F * csT A.lay + csOk A.lay) (T3.counterSearch A.lay A.tree A.leaf A.msg i F)
        (CsPost image b A s0) := by
  have hl0 : (A.lay.val = 0) ↔ A.lay = 0 := by
    constructor
    · intro h; exact Fin.ext h
    · intro h; rw [h]; rfl
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := cs113_spec hK t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, hf⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := CsPost image b A s0) (a := none) ⟨p2, h5, h10, hf⟩)
    exact this.mono (by unfold csOk; split_ifs <;> omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 22 := by omega
    obtain ⟨t2, s2, p2, hf, h5, hv, hq, h12, hT⟩ := cs_answer hK hpre hI hi
    have prog : T3.counterSearch A.lay A.tree A.leaf A.msg i (F + 1) =
        (T3.shortHash (T3.encodingInput A.lay A.tree A.leaf A.msg (BitVec.ofNat 32 i)) >>= fun answer =>
          match T3.decode A.lay answer with
          | none => T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F
          | some digits => pure (some (BitVec.ofNat 32 i, digits))) := rfl
    have ih' : ∀ t, CsInv b A s0 (i + 1) t → TBSim image sk t (F * csT A.lay + csOk A.lay)
        (T3.counterSearch A.lay A.tree A.leaf A.msg (i + 1) F) (CsPost image b A s0) :=
      fun t ht => ih (i + 1) t (by omega) ht
    rw [prog]
    refine (TBSim.steps s2 (TBSim.shortHash_bind hf h5 hv hq
      (W := F * csT A.lay + csOk A.lay + (csT A.lay - 18)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_encodingInput, Nat.succ_mul]; unfold csT; split_ifs <;> omega
    set v := a.extractLsb' 0 128 with hvdef
    have hT3 := hT.hash h12 a
    have p3 : (writeHash t2 a).pc = pcOf (b + 124) := by rw [pc_writeHash, p2, pcOf_add4]
    have hd := DigAt.writeHash_lo t2 a EOUT h12 (by decide)
    obtain ⟨t4, s4, p4, h6, h7, h25, r4, f4⟩ := cs124_spec hK (writeHash t2 a) p3 A.lay.val A.lay.isLt
      (by rw [hT3.reg (by decide), hpre.x8])
    rw [hd.1] at h6
    rw [hd.2] at h7
    have hT4 := hT3.step r4 (by decide) f4
    by_cases hlz : A.lay = 0
    · rw [if_pos (hl0.2 hlz)] at p4
      have hdec := decode_top_lookup v
      rw [← hlz] at hdec
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs263_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 125
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', h30', r6, f6⟩ := topCheck_spec hK t5 v hr p5
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7])
          (by rw [hT5.reg (by decide), hpre.x17, hlz]; rfl) (hT5.table hpre.table).sum
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : topLookupSum v = 126
        · rw [if_pos hs] at p6
          have hd' : T3.decode A.lay v = some (topDigits v) := by rw [hdec, if_pos ⟨hr, hs⟩]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_top_success hK hpre hT6 p6 hi hlz v hr
            ((topLookupSum_eq_iff v).mp hs).1 hd'
            (by rw [r6.get (by decide), r5.get (by decide), h6])
            (by rw [r6.get (by decide), r5.get (by decide), h7]) h30' (by simpa only [hs] using h25'))).mono ?_ (fun _ _ h => h)
          unfold csT csOk; rw [if_pos hlz, if_pos hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_pos hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd']
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_pos hlz]; omega
    · rw [if_neg (fun h => hlz (hl0.1 h))] at p4
      have hdec := decode_low A.lay hlz v
      obtain ⟨t5, s5, p5, r5, f5⟩ := cs130_spec hK t4 p4 v h7
      have hT5 := hT4.step r5 (by decide) f5
      by_cases hr : v.toNat < 2 ^ 126
      · rw [if_pos hr] at p5
        obtain ⟨t6, s6, p6, h25', r6, f6⟩ := cs132_spec hK t5 p5 v (T3.target A.lay) (target_lt _)
          (by rw [r5.get (by decide), h6]) (by rw [r5.get (by decide), h7]) (by rw [r5.get (by decide), h25])
          (by rw [hT5.reg (by decide), hpre.x17])
        have hT6 := hT5.step r6 (by decide) f6
        by_cases hs : (lowDigits v).sum ≤ T3.target A.lay ∧ T3.target A.lay - (lowDigits v).sum < 8
        · rw [if_pos hs] at p6
          obtain ⟨t7, s7, p7, r7, f7⟩ := cs262_spec hK t6 p6
          have hT7 := hT6.step r7 (by decide) f7
          have hd' : T3.decode A.lay v = some (lowDigits v ++ [T3.target A.lay - (lowDigits v).sum]) := by
            rw [hdec, if_pos ⟨hr, hs⟩]
          rw [hd']
          refine (TBSim.steps (((s4.trans s5).trans s6).trans s7) (cs_success hK hpre hT7 p7 hi hlz v _ _ hd' rfl hs.1
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h6])
            (by rw [r7.get (by decide), r6.get (by decide), r5.get (by decide), h7])
            (by rw [r7.get (by decide), h25']))).mono ?_ (fun _ _ h => h)
          unfold csT csOk; rw [if_neg hlz, if_neg hlz]; omega
        · rw [if_neg hs] at p6
          have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hs h.2)]
          rw [hd']
          refine (TBSim.steps ((s4.trans s5).trans s6) (cs_next hK hT6 p6 hi ih')).mono ?_ (fun _ _ h => h)
          unfold csT; rw [if_neg hlz]; omega
      · rw [if_neg hr] at p5
        have hd' : T3.decode A.lay v = none := by rw [hdec, if_neg (fun h => hr h.1)]
        rw [hd']
        refine (TBSim.steps (s4.trans s5) (cs_next hK hT5 p5 hi ih')).mono ?_ (fun _ _ h => h)
        unfold csT; rw [if_neg hlz]; omega

/-- **`counter_search` refines Core's `counterSearch`**: from the entry (`b + 103`) with `CsPre`, the machine runs
`counterSearch lay tree leaf M 0 counterLimit` query for query within `10 + 2^22 · csT lay + csOk lay` cycles
(failing trials at most `csT lay` = 158 / 201 cycles), ending in `CsPost`. -/
theorem counterSearch_tbsim {A : CsArgs} {s0 : MachineState} (hK : KernAt image b) (hpre : CsPre b A s0) :
    TBSim image sk s0 (10 + 2 ^ 22 * csT A.lay + csOk A.lay)
      (T3.counterSearch A.lay A.tree A.leaf A.msg 0 T3.counterLimit) (CsPost image b A s0) := by
  obtain ⟨t, st, pt, h16, h24, h19, rt, ft⟩ := cs103_spec hK s0 hpre.pc A.lay.val A.tree A.leaf A.lay.isLt
    hpre.htree hpre.hleaf hpre.x8 hpre.x9 hpre.x18
  have hI : CsInv b A s0 0 t := by
    refine ⟨pt, by norm_num, h19, h16, h24, ?_, rt.mono (by decide), ft.mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h))⟩
    obtain ⟨x, hx, hx32⟩ := hpre.c32
    exact ⟨x, hx, by rw [ft.get (by simp only [ENC]; omega) (by simp only [ENC]; omega), hx32]⟩
  have := TBSim.steps st (cs_loop (sk := sk) hK hpre (2 ^ 22) 0 t (by norm_num) hI)
  exact this.mono (le_of_eq (by ring)) (fun _ _ h => h)

end trial

/-! ## The interface shape of stream S (`Sign/Kernels.lean`, `CounterSearchSpec`)

The same statement in the exact shape of t3m/s `Sign/Kernels.lean` at any base `b` (sign: `b = 543`,
entry 646, `fail` `ECALL` 545): `CsPreS` is S's `CsPre` (with `csN4 = Keygen.n4` by `rfl`),
`CsPostS` is S's `CsPost` (with `FailedAt b` for S's `Failed`), `csCostS` is S's `csCost`. -/

/-- `HALT(1)` reached at the kernel's `fail` `ECALL` (`b + 2`; S's `Failed` at `b = 543`). -/
structure FailedAt (b : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 2)
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1

/-- Entry of `counter_search` (`b + 103`), called with `ra = ret` (S's `CsPre`). -/
structure CsPreS (b : Nat) (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat) :
    Prop where
  pc : s.pc = pcOf (b + 103)
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 tree
  x18 : s.getReg .x18 = BitVec.ofNat 64 leaf
  x17 : s.getReg .x17 = BitVec.ofNat 64 (T3.target lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (T3.chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  htree : tree < 2 ^ 32
  hleaf : leaf < 2 ^ 32
  msg : DigAt s ENC msg
  c32 : (s.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32
  z40 : s.getMem (BitVec.ofNat 64 (ENC + 40)) = 0
  z48 : s.getMem (BitVec.ofNat 64 (ENC + 48)) = 0
  z56 : s.getMem (BitVec.ofNat 64 (ENC + 56)) = 0
  table : TableOK s

/-- Exit of `counter_search` (S's `CsPost`): `fail` on exhaustion, else back at `ret` with the digits
at `DIGITS` and `s9 ≤ target`. -/
def CsPostS (b : Nat) (s : MachineState) (lay : Layer) (ret : Nat) :
    Option (BitVec 32 × List Nat) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, ds), t => t.pc = pcOf ret ∧ t.getReg .x5 = 0 ∧ (∃ v, T3.decode lay v = some ds) ∧
      (∀ i < T3.chainCount lay, t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (ds.getD i 0)) ∧
      (t.getMem (BitVec.ofNat 64 (ENC + 32))).toNat < 2 ^ 32 ∧ RegsExcept s t csRegs ∧ Frame s t CsW ∧
      (t.getReg .x25).toNat ≤ T3.target lay

/-- S's all-oracle cycle bound of `counter_search` (≤ 160 / 205 cycles per lower / top trial). -/
def csCostS (lay : Layer) : Nat := T3.counterLimit * (if lay = 0 then 205 else 160) + 2000

theorem CsPreS.toCsPre {b : Nat} {s : MachineState} {lay : Layer} {tree leaf : Nat} {msg : Digest} {ret : Nat}
    (h : CsPreS b s lay tree leaf msg ret) : CsPre b ⟨lay, tree, leaf, msg, ret⟩ s :=
  ⟨h.pc, h.x1, h.x5, h.x8, h.x9, h.x18, h.x17, h.x26, h.x27, h.htree, h.hleaf, h.msg.1, h.msg.2,
    ⟨_, h.c32, (BitVec.ofNat_toNat _ _).trans (BitVec.setWidth_eq _)|>.symm⟩, h.z40, h.z48, h.z56, h.table⟩

/-- **`counter_search` at any base, in S's shape** (`CounterSearchSpec` at `b = 543`). -/
theorem counterSearch_spec {image : Image} {b : Nat} {sk : BitVec 256} (hK : KernAt image b)
    (s : MachineState) (lay : Layer) (tree leaf : Nat) (msg : Digest) (ret : Nat)
    (h : CsPreS b s lay tree leaf msg ret) :
    TBSim image sk s (csCostS lay) (T3.counterSearch lay tree leaf msg 0 T3.counterLimit) (CsPostS b s lay ret) := by
  refine (counterSearch_tbsim (sk := sk) hK h.toCsPre).mono ?_ (fun r t ht => ?_)
  · show 10 + 2 ^ 22 * csT lay + csOk lay ≤ 2 ^ 22 * (if lay = 0 then 205 else 160) + 2000
    unfold csT csOk
    split_ifs <;> omega
  · rcases r with _ | ⟨c, ds⟩
    · exact ⟨ht.1, ht.2.1, ht.2.2.1⟩
    · obtain ⟨tpc, hc, _, h32, hdec, _, hdig, hr, hf, h25⟩ := ht
      refine ⟨tpc, ?_, hdec, hdig, ?_, hr, hf, h25⟩
      · rw [hr.get (by decide), h.x5]
      · rw [h32, BitVec.toNat_ofNat]
        omega

end SigGolfCandidate.T3M.Search
