import SigGolfCandidate.Expand.Blocks
import SigGolfCandidate.Sign.Layer

/-!
# `expand`, phase 2 (the queries after the partial witness): shared definitions

Phase 2 of the expand image (instructions 316 .. 672) runs verify's PORS stack machine on the
partial witness (`pors_init` 495 .. `pors_ok` 639), then the counter phase: per layer the sign's
header and least-counter search (instructions 316 .. 381, the sign's words, see
`Sign.HeadCode`), then below the top layer verify's chains, leaf and folds (382 .. 477), and at
layer 0 the counter write-out and HALT(0) (478 .. 494).

The proofs use the sign's `Sim` judgment (namespace `Sign`) on the expand image `eimg`.

* `FailSt t` : a HALT(1) state; `OPost G` : `FailSt` for `none`, `G a` for `some a`.
* `wword w o` : the dword of the witness bytes `o .. o+7` (zero beyond the list);
  `WitMem w t` : the witness buffer `0x800 .. 0x4800` holds `w` (zero padded).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- The expand image. -/
abbrev eimg : Image := Expand.image

/-- The expand image carries the sign's layer header and counter search (words 316 .. 381). -/
theorem eHeadCode : HeadCode eimg :=
  { c346 := Expand.codeAt_346, c351 := Expand.codeAt_351, c355 := Expand.codeAt_355,
    c375 := Expand.codeAt_375, c2887 := Expand.codeAt_2887,
    c376 := Expand.codeAt_376, c377 := Expand.codeAt_377, c379 := Expand.codeAt_379,
    c316 := Expand.codeAt_316, c318 := Expand.codeAt_318, c321 := Expand.codeAt_321,
    c322 := Expand.codeAt_322, c329 := Expand.codeAt_329, c331 := Expand.codeAt_331 }

/-! ## Failure -/

/-- A HALT(1) state of the expand image. -/
def FailSt (t : MachineState) : Prop :=
  fetch eimg t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1

/-- Postcondition of an optional result: HALT(1) for `none`. -/
def OPost {α : Type} (G : α → MachineState → Prop) : Option α → MachineState → Prop
  | none, t => FailSt t
  | some a, t => G a t

/-- `fail` (instructions 284 .. 286): HALT(1). -/
theorem fail_steps (t : MachineState) (h : t.pc = pcOf 284) :
    ∃ t', Steps eimg t 2 2 t' ∧ FailSt t' := by
  have hs := symRun_sound Expand.blk284 Expand.codeAt_284 t h (by simp only [Expand.blk284.res, rv_simp])
  refine ⟨_, hs, symRun_ecall Expand.blk284 Expand.codeAt_284 t (by simp only [Expand.blk284.res, rv_simp]) rfl,
    ?_, ?_⟩
  · simp only [Expand.blk284.res, rv_simp]
  · simp only [Expand.blk284.res, rv_simp]

theorem fail_sim {α : Type} {G : α → MachineState → Prop} (t : MachineState) (h : t.pc = pcOf 284) :
    Sim eimg t 2 (pure none) (OPost G) := by
  obtain ⟨t', hs, hf⟩ := fail_steps t h
  exact Sim.pure_steps hs hf

/-- The failure `none` of an `Option`-valued step after `k` more steps. -/
theorem fail_sim_steps {α : Type} {G : α → MachineState → Prop} {s t : MachineState} {k c : Nat}
    (hs : Steps eimg s k c t) (h : t.pc = pcOf 284) :
    Sim eimg s (c + 2) (pure none) (OPost G) :=
  Sim.steps hs (fail_sim t h)

/-! ## The witness buffer -/

/-- The dword of witness bytes `o .. o+7` (zero beyond the list). -/
def wword (w : List Byte) (o : Nat) : Word := BitVec.ofNat 64 (leNat (wbytes w o 8))

/-- The buffer `0x800 .. 0x4800` holds the witness `w`, zero padded. -/
def WitMem (w : List Byte) (t : MachineState) : Prop :=
  ∀ k < 2048, t.getMem (BitVec.ofNat 64 (0x800 + 8 * k)) = wword w (8 * k)

/-- Addresses of the witness buffer. -/
def witA (a : Nat) : Prop := 0x800 ≤ a ∧ a < 0x4800

theorem WitMem.frame {w : List Byte} {s t : MachineState} {W : Nat → Prop} (h : WitMem w s)
    (hf : Frame s t W) (hW : ∀ a, witA a → ¬ W a) : WitMem w t := by
  intro k hk
  rw [hf.getMem (by omega) (hW _ (by unfold witA; omega)), h k hk]

theorem WitMem.get {w : List Byte} {t : MachineState} (h : WitMem w t) (o : Nat) (ho : o % 8 = 0)
    (ho' : o < 0x4000) : t.getMem (BitVec.ofNat 64 (0x800 + o)) = wword w o := by
  have := h (o / 8) (by omega)
  rwa [show 8 * (o / 8) = o by omega] at this

theorem length_wbytes (w : List Byte) (o n : Nat) : (wbytes w o n).length = n := by
  simp [wbytes]

theorem wbytes_add (w : List Byte) (o m n : Nat) : wbytes w o (m + n) = wbytes w o m ++ wbytes w (o + m) n := by
  unfold wbytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro i _; simp [Nat.add_assoc]

/-- A 16-byte witness field as two dwords. -/
theorem wordsOf_wbytes16 (w : List Byte) (o : Nat) : wordsOf (wbytes w o 16) = [wword w o, wword w (o + 8)] := by
  rw [show (16 : Nat) = 8 + 8 from rfl, wbytes_add, wordsOf_append _ _ (by rw [length_wbytes]),
    wordsOf_eight _ (length_wbytes _ _ _), wordsOf_eight _ (length_wbytes _ _ _)]
  rfl

/-- Two witness dwords as a 16-byte field. -/
theorem WitMem.readWords16 {w : List Byte} {t : MachineState} (h : WitMem w t) (o : Nat) (ho : o % 8 = 0)
    (ho' : o + 8 < 0x4000) :
    t.readWords (BitVec.ofNat 64 (0x800 + o)) 2 = wordsOf (wbytes w o 16) := by
  rw [readWords_ofNat_two, wordsOf_wbytes16, h.get o ho (by omega),
    show 0x800 + o + 8 = 0x800 + (o + 8) by omega, h.get (o + 8) (by omega) ho']

/-- A slice inside the list is the zero-padded read. -/
theorem slice_eq_wbytes (w : List Byte) (o n : Nat) (h : o + n ≤ w.length) : slice w o n = wbytes w o n := by
  apply List.ext_getElem (by simp [slice, wbytes]; omega)
  intro i h1 h2
  simp only [slice, wbytes, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp [slice] at h1; omega)]

/-- The low byte of a witness dword. -/
theorem lbu_wword (w : List Byte) (o : Nat) :
    (extractByte (wword w o) 0).zeroExtend 64 = BitVec.ofNat 64 (wbyte w o) := by
  apply BitVec.eq_of_toNat_eq
  have h8 : leNat (wbytes w o 8) < 2 ^ 64 := by
    have := leNat_lt (wbytes w o 8); rw [length_wbytes] at this; simpa using this
  simp only [wword, extractByte, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h8, Nat.zero_mul, Nat.shiftRight_zero, BitVec.truncate_eq_setWidth,
    BitVec.zeroExtend_eq_setWidth]
  have hb : (w.getD o 0).toNat < 256 := (w.getD o 0).isLt
  have e : wbytes w o 8 = w.getD o 0 :: wbytes w (o + 1) 7 := by
    have := wbytes_add w o 1 7
    simp only [Nat.reduceAdd] at this
    rw [this]; simp [wbytes]
  rw [e, leNat]
  unfold wbyte
  simp only [Nat.reducePow]
  omega

/-! ## Block helpers -/

/-- `RegsEq` of a block result, by evaluation (the registers outside `l` are `.reg r`). -/
macro "pregs" : tactic =>
  `(tactic| (apply SigGolfCandidate.Sign.regsEq_toState; intro x hx; cases x <;> first | (simp at hx; done) | rfl))

/-- Numeric normalization of block results: `ofNat` sums, literal address comparisons, `ite`. -/
macro "pnum" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, SigGolfCandidate.Sign.ofNat_add_ofNat, Nat.reduceAdd, Nat.reduceMul,
      SigGolfCandidate.Sign.ofNat_eq_iff, Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, reduceIte,
      ite_true, ite_false, if_true, if_false, $ts',*])

/-- Side conditions of a block (access validity, alias freedom) by `omega`. -/
macro "pobl" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| (simp only [rv_simp, SigGolfCandidate.Sign.ofNat_add_ofNat, SigGolfCandidate.Sign.accessValid_ofNat,
      ne_eq, SigGolfCandidate.Sign.ofNat_eq_iff, BitVec.toNat_ofNat, $ts',*] <;>
    (try simp (disch := omega) only [Nat.reducePow, Nat.mod_eq_of_lt, and_true, true_and]) <;> omega))

theorem frame_nil {r : Result} (h : r.st.mem = []) (s : MachineState) (W : Nat → Prop) :
    Frame s (r.toState s) W := by
  intro a _ _; rw [Result.toState_getMem, h, memEval_nil]

theorem getMem_nil {r : Result} (h : r.st.mem = []) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = s.getMem a := by
  rw [Result.toState_getMem, h, memEval_nil]

theorem readWords8 (t : MachineState) (a : Nat) :
    t.readWords (BitVec.ofNat 64 a) 8 = [t.getMem (BitVec.ofNat 64 a), t.getMem (BitVec.ofNat 64 (a + 8)),
      t.getMem (BitVec.ofNat 64 (a + 16)), t.getMem (BitVec.ofNat 64 (a + 24)),
      t.getMem (BitVec.ofNat 64 (a + 32)), t.getMem (BitVec.ofNat 64 (a + 40)),
      t.getMem (BitVec.ofNat 64 (a + 48)), t.getMem (BitVec.ofNat 64 (a + 56))] := by
  rw [show (8 : Nat) = 2 + 2 + 2 + 2 from rfl, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
    readWords_ofNat_two, readWords_ofNat_two, readWords_ofNat_two, readWords_ofNat_two]
  simp only [List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceMul, Nat.reduceAdd]

theorem and_one (n : Nat) : n &&& 1 = n % 2 := Nat.and_two_pow_sub_one_eq_mod n 1

theorem and_15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem ofNat_beq_zero (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0#64) = decide (n = 0) := by
  rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_beq_ofNat, Nat.mod_eq_of_lt h]; rfl

/-- The tweak words of a PORS input (`lay = 0`, `p = 0`, instance `idx < 2^34`). -/
theorem twWords_pors (tg idx j : Nat) (ht : tg < 256) (hidx : idx < 2 ^ 34) (hj : j < 2 ^ 32) :
    twWords tg 0 idx 0 j =
      [BitVec.ofNat 64 (1 + 256 * tg + 2 ^ 24 * (idx / 2 ^ 32)), BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * j)] := by
  unfold twWords
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (by omega : idx / 2 ^ 32 < 256), Nat.mod_eq_of_lt hj]
  simp

end SigGolfCandidate.ExP
