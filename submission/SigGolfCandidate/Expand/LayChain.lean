import SigGolfCandidate.Expand.LayBlk2
import SigGolfCandidate.Sign.AddressHash

/-!
# `expand`, phase 2: a layer's chains and OTS leaf (`Ref.verifyLeaf`, instructions 408 .. 441)

`chains_sim` : from `ch_loop` (408) with chain 0's digit word `d0` in `s3`, `d1` in `sp`, the
machine refines verify's 42 chains `chainFrom lay tau e i x_i (witChain w lay i)` (the ends
collected at `LF + 32`), then `leaf_sim` the OTS leaf hash into `NO`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- The constant part of the layer phase: `t0 = 0`, `t2 = 2^22`, `s6 = idx`, `s9 = X`, the SWAR
masks; the zero P slot of the encoding block, the zero words of `CB`, `LF`, `NB`; the witness. -/
structure LCtx (w : List Byte) (idx : Nat) (t : MachineState) : Prop where
  hidx : idx < 2 ^ 34
  x5 : t.getReg .x5 = 0
  x7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x22 : t.getReg .x22 = BitVec.ofNat 64 idx
  x25 : t.getReg .x25 = BitVec.ofNat 64 0x30000
  x26 : t.getReg .x26 = swM1
  x27 : t.getReg .x27 = swM2
  ebP : t.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  cbz : t.readWords (BitVec.ofNat 64 0x30150) 4 = [0, 0, 0, 0]
  lfz : t.readWords (BitVec.ofNat 64 0x30250) 2 = [0, 0]
  nbz : t.readWords (BitVec.ofNat 64 0x301D0) 2 = [0, 0]
  wit : WitMem w t

/-- Addresses `LCtx` reads. -/
def lctxA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x30150 ≤ a ∧ a < 0x30170) ∨ (0x30250 ≤ a ∧ a < 0x30260) ∨
    (0x301D0 ≤ a ∧ a < 0x301E0) ∨ witA a

/-- Registers `LCtx` reads. -/
def lctxRegs : List Reg := [.x5, .x7, .x22, .x25, .x26, .x27]

theorem LCtx.frame {w : List Byte} {idx : Nat} {s t : MachineState} {W : Nat → Prop} {l : List Reg}
    (h : LCtx w idx s) (hf : Frame s t W) (hr : RegsEq s t l) (hW : ∀ a, lctxA a → ¬ W a)
    (hl : ∀ r ∈ lctxRegs, r ∉ l := by decide) : LCtx w idx t := by
  refine ⟨h.hidx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h.wit.frame hf (fun a ha => hW a (by
    unfold lctxA; simp only [ha, or_true]))⟩
  · rw [hr.get .x5 (hl _ (by decide)), h.x5]
  · rw [hr.get .x7 (hl _ (by decide)), h.x7]
  · rw [hr.get .x22 (hl _ (by decide)), h.x22]
  · rw [hr.get .x25 (hl _ (by decide)), h.x25]
  · rw [hr.get .x26 (hl _ (by decide)), h.x26]
  · rw [hr.get .x27 (hl _ (by decide)), h.x27]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by unfold lctxA; omega)), h.ebP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by unfold lctxA; omega)), h.cbz]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by unfold lctxA; omega)), h.lfz]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by unfold lctxA; omega)), h.nbz]

theorem LCtx.frame_nil {w : List Byte} {idx : Nat} {s t : MachineState} {l : List Reg}
    (h : LCtx w idx s) (hm : ∀ x, t.getMem x = s.getMem x) (hr : RegsEq s t l)
    (hl : ∀ r ∈ lctxRegs, r ∉ l := by decide) : LCtx w idx t :=
  h.frame (W := fun _ => False) (fun x _ _ => hm _) hr (fun _ _ h => h) hl

/-- The chain tweak words (`p < 2^32`: position `mu - 1 + 256 i`). -/
theorem twWords_chain (lay tau p e : Nat) (hl : lay < 256) (htau : tau < 2 ^ 32) (hp : p < 2 ^ 32)
    (he : e < 2 ^ 32) :
    twWords 1 lay tau p e = [BitVec.ofNat 64 (257 + 65536 * lay + 2 ^ 32 * p),
      BitVec.ofNat 64 (tau + 2 ^ 32 * e)] := by
  unfold twWords
  rw [Nat.mod_eq_of_lt hl, Nat.div_eq_of_lt htau, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt htau,
    Nat.mod_eq_of_lt he]
  simp

theorem blocks_fmt_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) (hmu : 1 ≤ mu)
    (hmu' : mu ≤ 8) (hi : i < 2 ^ 24) : (fmt (chainInput lay tau e i mu v)).blocks = 1 := by
  rw [fmt_chainInput _ _ _ _ _ _ hv hmu hmu' hi]; rfl

/-! ## The steps of one chain -/

/-- Registers a chain writes. -/
def chRegs : List Reg := [.x10, .x11, .x12, .x14, .x15, .x18, .x19, .x20, .x23, .x24, .x28]

/-- Addresses the chains write: `CB` word 0, `CB + 48 .. + 80` (the answers), the ends. -/
def chW (a : Nat) : Prop := a = 0x30140 ∨ (0x30170 ≤ a ∧ a < 0x30190) ∨ (0x30260 ≤ a ∧ a < 0x30500)

theorem lctx_chW : ∀ a, lctxA a → ¬ chW a := by
  intro a h1 h2; unfold lctxA witA at h1; unfold chW at h2; omega

/-- The step loop of chain `i` from digit `x`, after `j` steps (value `v` at `CB + 48`). -/
def StepInv (w : List Byte) (idx : Nat) (u : MachineState) (x j : Nat) (v : Val) (t : MachineState) : Prop :=
  t.pc = pcOf 417 ∧ LCtx w idx t ∧ t.getReg .x28 = BitVec.ofNat 64 (x + j) ∧ x + j ≤ 7 ∧ v.length = 16 ∧
  t.readWords (BitVec.ofNat 64 0x30170) 2 = wordsOf v ∧
  RegsEq u t [.x10, .x11, .x12, .x14, .x28] ∧ Frame u t (fun a => a = 0x30140 ∨ (0x30170 ≤ a ∧ a < 0x30190))

theorem step_body (w : List Byte) (idx : Nat) (u : MachineState) (lay tau e i x : Nat) (hl : lay < 5)
    (htau : tau < 2 ^ 30) (he : e < 2048) (hi : i < 42) (hx : x < 8)
    (u20 : u.getReg .x20 = BitVec.ofNat 64 (257 + 65536 * lay + 2 ^ 40 * i))
    (u148 : u.getMem (BitVec.ofNat 64 0x30148) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)) :
    ∀ j < 7 - x, ∀ (v : Val) (t : MachineState), StepInv w idx u x j v t →
      Sim eimg t 44 ((fun v mu => hash16 (chainInput lay tau e i mu v)) v (x + 1 + j))
        (StepInv w idx u x (j + 1)) := by
  intro j hj v t ⟨tpc, tc, t28, hxj, hv, tv, tregs, tframe⟩
  obtain ⟨t1, hs1, p1, r1, m1⟩ := blk417_run t tpc (x + j) (by omega) t28
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, hs2, p2, x10, x11, x12, m140, r2, f2, x14⟩ := blk419_run t1 p1 (x + j)
    (257 + 65536 * lay + 2 ^ 40 * i) (by omega) (by omega) (by rw [r1.get .x28, t28])
    (by rw [r1.get .x20, tregs.get .x20, u20]) (by rw [r1.get .x25, tc.x25])
  have c2 : LCtx w idx t2 := (tc.frame_nil m1 r1).frame f2 r2 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
  have f12 : Frame t t2 (fun a => a = 0x30140) := fun a ha hW => by rw [f2 a ha hW, m1]
  have hq : hashInput t2 = fmt (chainInput lay tau e i (x + 1 + j) v) := by
    refine hashInput_eq_chain t2 lay tau e i (x + 1 + j) v hv (by omega) (by omega) (by omega) x11
      (by rw [x10]; decide) ?_
    rw [x10, show x + 1 + j - 1 + 256 * i = x + j + 256 * i by omega,
      twWords_chain _ _ _ _ (by omega) (by omega) (by omega) (by omega),
      show (8 : Nat) = 2 + (4 + 2) from rfl, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_two]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [f12.readWords _ _ (by norm_num) (fun i hi => by omega), tc.cbz,
      f12.readWords _ _ (by norm_num) (fun i hi => by omega), tv, m140,
      f12.getMem (by norm_num) (by norm_num), tframe.getMem (by norm_num) (by omega), u148]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    exact ofNat_congr (by ring)
  have hw : t2.getMem (BitVec.ofNat 64 0x30140) =
      BitVec.ofNat 64 (AddressFormat.oldHeader lay 0 i (x + j)) := by
    rw [m140]
    unfold AddressFormat.oldHeader
    congr 1
    norm_num
    omega
  have aq := expand_address_query t2 (pcOf 804) (pcOf 824) (pcOf 825)
    Expand.addrHead425 Expand.addrTail425 (Expand.jumpAddress425 t2 p2)
    (fun z hp => by simpa only [p2, show pcOf 425 + 4 = pcOf 426 from rfl] using Expand.returnAddress425 z hp)
    (by rfl) (by rfl) 0x30140 lay i (x + j) (by omega) hi (by omega)
    (by norm_num) (by norm_num) x10 x11 x12 (x14.trans (m140.symm.trans hw)) c2.x5 hw _ hq
    (blocks_fmt_chainInput _ _ _ _ _ _ hv (by omega) (by omega) (by omega))
  refine (Sim.steps hs1 (Sim.steps hs2 (Sim.of_eq (expand_address_hash16_bindF
    (f := pure) (W := 2) aq (fun ans => ?_)) (bind_pure _)))).mono (by norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 ans with ht3
  have p3 : t3.pc = pcOf 426 := by rw [ht3, writeHash_pc, p2]; rfl
  obtain ⟨t4, hs4, p4, y28, r4, m4⟩ := blk426_run t3 p3 (x + j) (by rw [ht3, writeHash_getReg, r2.get .x28,
    r1.get .x28, t28])
  have f3 : Frame t2 t3 (fun a => 0x30170 ≤ a ∧ a < 0x30170 + 32) := frame_writeHash t2 ans _ x12 (by norm_num)
  refine Sim.pure_steps hs4 ⟨p4, (c2.frame f3 (regsEq_writeHash t2 ans []) (fun a h1 h2 => by
      unfold lctxA witA at h1; omega)).frame_nil m4 r4, by rw [y28]; exact ofNat_congr (by omega), by omega,
    by simp [answerBytes], ?_, ?_, ?_⟩
  · rw [readWords_ofNat_two, m4, m4, ← readWords_ofNat_two, ht3, writeHash_readWords_val t2 ans _ x12 (by norm_num)]
  · exact ((((tregs.trans r1).trans r2).trans (regsEq_writeHash t2 ans [])).trans r4).mono (by decide)
  · have f4 : Frame t3 t4 (fun _ => False) := fun a _ _ => m4 _
    exact ((tframe.trans f12).trans (f3.trans f4)).mono (by
      intro a ha; simp only [or_false] at ha; omega)

/-! ## The 42 chains -/

theorem digits_getD (d0 d1 i : Nat) (hi : i < 42) :
    (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 = if i < 21 then d0 / 8 ^ i % 8 else d1 / 8 ^ (i - 21) % 8 := by
  have hl : (digitsOfWord d0).length = 21 := by simp [digitsOfWord]
  by_cases h : i < 21
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    simp [digitsOfWord, List.getD_eq_getElem?_getD, h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hl]
    simp [digitsOfWord, List.getD_eq_getElem?_getD, show i - 21 < 21 by omega]

/-- The digit word of chain `i` (in `s3` at `ch_loop`). -/
def digWord (d0 d1 i : Nat) : Nat := if i ≤ 20 then d0 / 8 ^ i else d1 / 8 ^ (i - 21)

/-- The body of `verifyLeaf`'s chain loop. -/
def leafF (w : List Byte) (lay tau e : Nat) (x : List Nat) (ends : List Val) (i : Nat) :
    OracleComp HashSpec (List Val) := do
  let v ← chainFrom lay tau e i (x.getD i 0) (witChain w lay i)
  pure (ends ++ [v])

theorem verifyLeaf_eq (w : List Byte) (lay tau e : Nat) (x : List Nat) :
    verifyLeaf w lay tau e x = ((List.range 42).foldlM (leafF w lay tau e x) [] >>= fun ends =>
      hash16 (leafInput lay tau e ends)) := rfl

/-- The chain loop invariant after `i` chains (`u`: the state at the loop's start). -/
structure ChInv (w : List Byte) (idx : Nat) (u : MachineState) (lay d0 d1 i : Nat) (ends : List Val)
    (t : MachineState) : Prop where
  pc : t.pc = if i < 42 then pcOf 408 else pcOf 438
  ctx : LCtx w idx t
  hi : i ≤ 42
  len : ends.length = i
  vlen : ∀ v ∈ ends, v.length = 16
  slots : Slots t 0x30260 ends
  x18 : t.getReg .x18 = BitVec.ofNat 64 i
  x19 : i < 42 → t.getReg .x19 = BitVec.ofNat 64 (digWord d0 d1 i)
  x20 : t.getReg .x20 = BitVec.ofNat 64 (257 + 65536 * lay + 2 ^ 40 * i)
  x23 : t.getReg .x23 = BitVec.ofNat 64 (0x800 + (2992 + 2688 * lay) + 64 * i)
  x24 : t.getReg .x24 = BitVec.ofNat 64 (0x30260 + 16 * i)
  regs : RegsEq u t chRegs
  frame : Frame u t chW

/-- W1a: the value slot of chain block `(lay, i)` is `blockOff lay i + 48 = 2992 + 2688 lay + 64 i`. -/
theorem chainOff_eq (lay i : Nat) : blockOff lay i + 48 = 2992 + 2688 * lay + 64 * i := by
  rw [blockOff_eq]; omega

theorem chain_body (w : List Byte) (idx : Nat) (u : MachineState) (lay tau e d0 d1 : Nat) (hl : lay < 5)
    (htau : tau < 2 ^ 30) (he : e < 2048) (hd0 : d0 < 2 ^ 63) (hd1 : d1 < 2 ^ 63) (hw : w.length = 16384)
    (u2 : u.getReg .x2 = BitVec.ofNat 64 d1) (u21 : u.getReg .x21 = BitVec.ofNat 64 (2 ^ 40))
    (u148 : u.getMem (BitVec.ofNat 64 0x30148) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)) :
    ∀ i < 42, ∀ (ends : List Val) (t : MachineState), ChInv w idx u lay d0 d1 i ends t →
      Sim eimg t 335 (leafF w lay tau e (digitsOfWord d0 ++ digitsOfWord d1) ends i)
        (ChInv w idx u lay d0 d1 (i + 1)) := by
  intro i hi ends t hinv
  have hlen := hinv.len
  have tpc : t.pc = pcOf 408 := by rw [hinv.pc, if_pos hi]
  have hq : digWord d0 d1 i < 2 ^ 64 := by
    unfold digWord; split
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  obtain ⟨t1, hs1, p1, y28, y19, r1, m1⟩ := blk408_run t tpc i _ hi hq hinv.x18 (hinv.x19 hi)
  have hdig : digWord d0 d1 i % 8 = (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 := by
    rw [digits_getD _ _ _ hi]; unfold digWord; split <;> split <;> first | rfl | omega
  -- 412 (chain 20 switches to `d1`), 413 (the chain value)
  obtain ⟨t2, k2, hs2, hk2, p2, z19, r2, m2⟩ : ∃ t2 k2, Steps eimg t1 k2 k2 t2 ∧ k2 ≤ 1 ∧ t2.pc = pcOf 413 ∧
      (i + 1 < 42 → t2.getReg .x19 = BitVec.ofNat 64 (digWord d0 d1 (i + 1))) ∧ RegsEq t1 t2 [.x19] ∧
      ∀ x, t2.getMem x = t1.getMem x := by
    by_cases h20 : i = 20
    · rw [if_pos h20] at p1
      obtain ⟨t2, hs2, p2, z19, r2, m2⟩ := blk412_run t1 p1
      refine ⟨t2, 1, hs2, le_refl _, p2, fun _ => ?_, r2, m2⟩
      rw [z19, r1.get .x2, hinv.regs.get .x2, u2]; subst h20; unfold digWord; simp
    · rw [if_neg h20] at p1
      refine ⟨t1, 0, Steps.refl _, by norm_num, p1, fun _ => ?_, RegsEq.refl _ _, fun _ => rfl⟩
      rw [y19]; congr 1; unfold digWord
      by_cases h1 : i + 1 ≤ 20
      · rw [if_pos (by omega), if_pos h1, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · rw [if_neg h1, if_neg (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ]
        congr 2; omega
  have c2 := (hinv.ctx.frame_nil m1 r1).frame_nil m2 r2
  obtain ⟨t3, hs3, p3, v3, r3, f3⟩ := blk413_run w t2 p2 (2992 + 2688 * lay + 64 * i) (by omega) (by omega) c2.wit
    (by rw [r2.get .x23, r1.get .x23, hinv.x23]; exact ofNat_congr (by omega)) c2.x25
  have c3 := c2.frame f3 r3 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
  set x := (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 with hx
  have hx8 : x < 8 := by rw [← hdig]; omega
  have hchain : witChain w lay i = wbytes w (2992 + 2688 * lay + 64 * i) 16 := by
    unfold witChain; rw [chainOff_eq, slice_eq_wbytes _ _ _ (by omega)]
  have R3 := (r1.trans r2).trans r3
  have hstep := Sim.foldlM_range' (image := eimg) (x + 1) (7 - x) (fun v mu => hash16 (chainInput lay tau e i mu v))
    (witChain w lay i) (StepInv w idx t3 x) 44
    (step_body w idx t3 lay tau e i x hl htau he hi hx8
      (by rw [R3.get .x20 (by decide), hinv.x20])
      (by rw [f3.getMem (by norm_num) (by omega), m2, m1, hinv.frame.getMem (by norm_num) (by unfold chW; omega),
        u148]))
    ⟨p3, c3, by rw [r3.get .x28, r2.get .x28, y28, hdig, Nat.add_zero], by omega,
      by rw [hchain, length_wbytes], by rw [v3, hchain], RegsEq.refl _ _, Frame.refl _ _⟩
  unfold leafF
  refine (Sim.steps hs1 (Sim.steps hs2 (Sim.steps hs3 (Sim.bind hstep (W₂ := 12) (fun v t4 h4 => ?_))))).mono
    (by omega) (fun _ _ h => h)
  obtain ⟨p4, c4, y28', hx7, hv4, v4, r4, f4⟩ := h4
  obtain ⟨t5, hs5, p5, r5, m5⟩ := blk417_run t4 p4 (x + (7 - x)) (by omega) y28'
  rw [if_pos (by omega)] at p5
  have R4 := (R3.trans r4).trans r5
  obtain ⟨t6, hs6, p6, w6, y18, y20, y23, y24, r6, f6⟩ := blk428_run t5 p5 i (0x800 + (2992 + 2688 * lay) + 64 * i)
    (257 + 65536 * lay + 2 ^ 40 * i) hi (by omega) (by omega) (by rw [R4.get .x18 (by decide), hinv.x18])
    (by rw [R4.get .x20 (by decide), hinv.x20])
    (by rw [R4.get .x21 (by decide), hinv.regs.get .x21, u21])
    (by rw [R4.get .x23 (by decide), hinv.x23]) (by rw [R4.get .x24 (by decide), hinv.x24])
    (by rw [r5.get .x25, c4.x25])
  have F6 : Frame t t6 (fun a => (a = 0x30140 ∨ (0x30170 ≤ a ∧ a < 0x30190)) ∨
      (a = 0x30260 + 16 * i ∨ a = 0x30260 + 16 * i + 8)) := by
    have f12 : Frame t t2 (fun _ => False) := fun a _ _ => by rw [m2, m1]
    have f5 : Frame t4 t5 (fun _ => False) := fun a _ _ => m5 _
    exact (((f12.trans f3).trans f4).trans (f5.trans f6)).mono (by
      intro a ha; simp only [or_false, false_or] at ha; omega)
  refine Sim.pure_steps (hs5.trans hs6) ⟨?_, ?_, by omega, by simp [hinv.len], ?_, ?_, y18, ?_,
    by rw [y20]; exact ofNat_congr (by ring), by rw [y23]; exact ofNat_congr (by ring), y24, ?_, ?_⟩
  · rw [p6]; split <;> split <;> first | rfl | omega
  · exact (c4.frame_nil m5 r5).frame f6 r6 (fun a h1 h2 => by unfold lctxA witA at h1; omega)
  · intro v' hv'; rcases List.mem_append.mp hv' with h | h
    · exact hinv.vlen v' h
    · simp at h; rw [h]; exact hv4
  · refine (hinv.slots.frame F6 (by omega) (fun j hj => ?_)).snoc ?_
    · rw [hinv.len] at hj; constructor <;> omega
    · rw [hinv.len, w6, readWords_ofNat_two, m5, m5, ← readWords_ofNat_two, v4]
  · intro h; rw [r6.get .x19 (by decide), r5.get .x19, r4.get .x19 (by decide), r3.get .x19, z19 h]
  · exact ((hinv.regs.trans R4).trans r6).mono (by decide)
  · exact (hinv.frame.trans F6).mono (by intro a ha; simp only [chW] at ha ⊢; omega)

end SigGolfCandidate.ExP
