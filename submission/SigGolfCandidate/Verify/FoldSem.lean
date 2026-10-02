import SigGolfCandidate.Verify.FoldRuns
import SigGolfCandidate.Verify.FoldCheck
import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.Common
import SigGolfCandidate.Verify.ChainSem
import Mathlib.Data.Nat.Bitwise
set_option Elab.async false

/-! # Merkle fold levels (M4 shape blocks): semantics -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000


namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Node format `tw(t, f2, tau, lam, j) | P | l | r` (`nodeInput`, `ftsNodeInput`). -/
def nodeF (t f2 tau : Nat) : NodeFmt := fun lam j l r => thInput (tweak t f2 tau lam j) (l ++ r)

theorem nodeInput_eq (lay tau : Nat) : nodeInput lay tau = nodeF 3 lay tau := rfl

theorem pad64_nodeF (t f2 tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (nodeF t f2 tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo t f2 tau lam), BitVec.ofNat 64 (twHi tau j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold nodeF
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

structure FCtx where
  wl : List Byte
  pk : List Byte
  E : Nat
  h : Nat
  lay : Nat
  t : Nat
  f2 : Nat
  tau : Nat
  sibOff : Nat
  dst : Nat

def FCtx.ok (fc : FCtx) : Prop :=
  2 ≤ fc.h ∧ fc.h ≤ 11 ∧ fc.E < 2 ^ fc.h ∧ fc.t < 256 ∧ fc.f2 < 256 ∧ fc.wl.length = 16384 ∧
  fc.sibOff % 8 = 0 ∧ fc.sibOff + pathStrideL fc.lay * fc.h ≤ 2944 ∧ safeDest fc.dst = true ∧
  (fc.dst + 32 ≤ 0x340 ∨ 0x390 ≤ fc.dst) ∧ fc.lay < 5 ∧ fc.h = heightL fc.lay ∧
  fc.sibOff = pathOffL fc.lay ∧ fc.dst = dstOf fc.lay

def FCtx.lo0 (fc : FCtx) : Nat := Ref.MaskHeader.header 0 (1 + 256 * fc.t + 65536 * fc.f2 + 2 ^ 24 * (fc.tau / 2 ^ 32 % 256))

/-- The leaf index with the heap sentinel, `E + 2^h` (register `x23`). -/
def FCtx.U (fc : FCtx) : Nat := if fc.lay = 0 then 4095 - fc.E else fc.E + 2 ^ fc.h

def FCtx.path (fc : FCtx) : List Val := (List.range fc.h).map fun l => slice fc.wl (fc.sibOff + pathStrideL fc.lay * l) 16

def FCtx.node (fc : FCtx) : NodeFmt := nodeF fc.t fc.f2 fc.tau

def bitOf (E lam : Nat) : Nat := E / 2 ^ lam % 2

/-- The chunk of level `lam`, its index in the chunk, the block (chunk value) and the level's
`li a2` pc. -/
def FCtx.ci (fc : FCtx) (lam : Nat) : Nat := chOf fc.lay lam
def FCtx.kk (fc : FCtx) (lam : Nat) : Nat := lam - chB0 fc.lay (chOf fc.lay lam)
def FCtx.blk (fc : FCtx) (ci : Nat) : Nat := fc.E / 2 ^ chB0 fc.lay ci % 2 ^ chBits fc.lay ci
def FCtx.X (fc : FCtx) (lam : Nat) : Nat := m4Pc fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)

def FrameOK (s0 s : MachineState) : Prop :=
  (∀ r ∈ fkeep false, s.getReg r = s0.getReg r) ∧
  (∀ A, A < 2 ^ 64 → (A + 8 ≤ 0x120 ∨ 0x390 ≤ A) → s.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A))

/-- Tweak word 0 of the node inputs (`p = 0`) at NB (= LB): before level 0 it still holds the leaf
tweak, whose byte 1 (the tag 2) level 0 overwrites with 3. -/
def NBhdr (fc : FCtx) (lam : Nat) (s : MachineState) : Prop :=
  (lam = 0 → StoreKind.merge .b (s.getMem (BitVec.ofNat 64 0x340)) (if fc.lay < 4 then 2 else 1) (BitVec.ofNat 64 (if fc.lay < 4 then fc.lay else 3)) = BitVec.ofNat 64 fc.lo0) ∧
  (lam ≠ 0 → s.getMem (BitVec.ofNat 64 0x340) = BitVec.ofNat 64 fc.lo0)

/-- Where the path node of level `lam` is (the output address of the hash that made it, still in `a2`). -/
def FCtx.vA (fc : FCtx) (lam : Nat) : Nat := nodeDst fc.lay lam (bitOf fc.E lam)

theorem FCtx.vA_cases (fc : FCtx) (lam : Nat) :
    fc.vA lam = 0x120 + 16 * bitOf fc.E lam ∨ fc.vA lam = 0x360 + 16 * bitOf fc.E lam := by
  unfold FCtx.vA nodeDst; split <;> simp

theorem FCtx.vA_zero (fc : FCtx) (h0 : fc.lay = 0) (lam : Nat) :
    fc.vA lam = 0x360 + 16 * bitOf fc.E lam := by
  unfold FCtx.vA nodeDst; rw [if_neg (by omega)]

def TopLink (fc : FCtx) (s : MachineState) : Prop :=
  fc.lay = 0 → s.getReg .x16 = pcOf (topSlotPc fc.E + 1)

def FoldInv (fc : FCtx) (s0 : MachineState) (lam : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob gkL fc.wl fc.pk s ∧ KnownOK (lvlK fc.lay lam) s ∧
  s.getReg .x23 = BitVec.ofNat 64 fc.U ∧ NBhdr fc lam s ∧
  (s.getMem (BitVec.ofNat 64 0x348)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 (fc.vA lam)) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (fc.vA lam + 8)) = vw1 v ∧ v.length = 16 ∧
  FrameOK s0 s ∧ s.pc = pcOf (fc.X lam + 2) ∧ Fresh fc.wl fc.lay 42 s ∧
  s.getReg .x12 = BitVec.ofNat 64 (fc.vA lam) ∧ TopLink fc s

theorem FCtx.vA_lt (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 < fc.h) :
    fc.vA lam = 0x360 + 16 * bitOf fc.E lam := by
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  unfold FCtx.vA nodeDst; rw [if_neg (by omega)]

def FoldEnd (fc : FCtx) (s0 : MachineState) (u : MachineState) : Prop :=
  Glob gkL fc.wl fc.pk u ∧ KnownOK (foldK fc.lay 64 ++ [(.x12, BitVec.ofNat 64 fc.dst)]) u ∧
  FrameOK s0 u ∧ u.pc = pcOf (fc.X (fc.h - 1) + 8) ∧
  fetch image u = some (.base .ECALL) ∧
  (u.getMem (BitVec.ofNat 64 0x348)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32

/-! ## Chunks -/

theorem chunk_facts (lay lam : Nat) (hl : lay < 5) (hlam : lam < heightL lay) :
    chOf lay lam < nCh lay ∧ chB0 lay (chOf lay lam) + (lam - chB0 lay (chOf lay lam)) = lam ∧
    lam - chB0 lay (chOf lay lam) < chBits lay (chOf lay lam) ∧
    chB0 lay (chOf lay lam) + chBits lay (chOf lay lam) ≤ heightL lay ∧
    (lam + 1 < heightL lay → lam - chB0 lay (chOf lay lam) + 1 < chBits lay (chOf lay lam) →
      chOf lay (lam + 1) = chOf lay lam) ∧
    (lam + 1 < heightL lay → ¬ lam - chB0 lay (chOf lay lam) + 1 < chBits lay (chOf lay lam) →
      lay = 0 ∧ lam = 5) ∧
    (isConstLvl lay lam = true → chB0 lay (chOf lay lam) + chBits lay (chOf lay lam) = heightL lay) := by
  interval_cases lay <;> simp only [heightL, List.getD_cons_succ, List.getD_cons_zero] at hlam ⊢ <;>
    interval_cases lam <;> decide

theorem blk_bit (E b n k : Nat) (hk : k < n) : E / 2 ^ b % 2 ^ n / 2 ^ k % 2 = E / 2 ^ (b + k) % 2 := by
  rw [← Nat.toNat_testBit, ← Nat.toNat_testBit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hk, Nat.add_comm]

theorem blk_top (E b n k : Nat) (hE : E < 2 ^ (b + n)) : E / 2 ^ b % 2 ^ n / 2 ^ k = E / 2 ^ (b + k) := by
  rw [Nat.mod_eq_of_lt (by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.add_comm]; exact hE),
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem blk_lt (fc : FCtx) (ci : Nat) : fc.blk ci < 2 ^ chBits fc.lay ci := Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The dispatch value: `(idx << sh) + doff`, even. -/
def dispVal (lay ci : Nat) (x : Word) : Word :=
  let idx := if nCh lay = 1 then x else if ci = 0 then x &&& BitVec.ofNat 64 63 else x &&& BitVec.ofNat 64 (2 ^ 64 - 64)
  let sh := if nCh lay = 2 ∧ ci = 1 then m4Sh lay ci + 2 - 6 else m4Sh lay ci + 2
  ((idx <<< (sh % 64)) + BitVec.ofNat 64 (m4Doff lay ci)) &&& ~~~1#64

theorem add_hi_sub (a h d : Word) : a + h + (d - h) = a + d := by
  apply BitVec.eq_of_toNat_eq
  have := a.isLt; have := h.isLt; have := d.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  omega

theorem dispTgt_eval (lay ci : Nat) (s : MachineState) :
    (dispTgt lay ci).eval s = dispVal lay ci (s.getReg .x23) := by
  have hsh : ∀ n, (BitVec.ofNat 64 n).toNat % 64 = n % 64 := fun n => by
    rw [BitVec.toNat_ofNat]; omega
  unfold dispTgt dispGp dispVal
  split_ifs <;> simp only [mkBin_eval, mkAdd_eval, BinOp.eval, E.eval, cw, hsh, add_hi_sub]

theorem dispVal_tab4 : ∀ E, E < 32 → dispVal 4 0 (BitVec.ofNat 64 (E + 32)) =
    pcOf (m4Pc 4 0 (E / 2 ^ chB0 4 0 % 2 ^ chBits 4 0) 0) := by decide +kernel
theorem dispVal_tab3 : ∀ E, E < 64 → dispVal 3 0 (BitVec.ofNat 64 (E + 64)) =
    pcOf (m4Pc 3 0 (E / 2 ^ chB0 3 0 % 2 ^ chBits 3 0) 0) := by decide +kernel
theorem dispVal_tab2 : ∀ E, E < 64 → dispVal 2 0 (BitVec.ofNat 64 (E + 64)) =
    pcOf (m4Pc 2 0 (E / 2 ^ chB0 2 0 % 2 ^ chBits 2 0) 0) := by decide +kernel
theorem dispVal_tab1 : ∀ E, E < 64 → dispVal 1 0 (BitVec.ofNat 64 (E + 64)) =
    pcOf (m4Pc 1 0 (E / 2 ^ chB0 1 0 % 2 ^ chBits 1 0) 0) := by decide +kernel
theorem dispVal_tab00 : ∀ E, E < 2048 → dispVal 0 0 (BitVec.ofNat 64 (4095 - E)) =
    pcOf (m4Pc 0 0 (E / 2 ^ chB0 0 0 % 2 ^ chBits 0 0) 0) := by decide +kernel
theorem dispVal_tab01 : ∀ E, E < 2048 → dispVal 0 1 (BitVec.ofNat 64 (4095 - E)) =
    pcOf (m4Pc 0 1 (E / 2 ^ chB0 0 1 % 2 ^ chBits 0 1) 0) := by decide +kernel

/-- The chunk dispatch lands on the entry of the block of the leaf index. -/
theorem disp_eval (lay ci : Nat) (hl : lay < 5) (hci : ci < nCh lay) (E : Nat) (hE : E < 2 ^ heightL lay)
    (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 (heapU lay E)) :
    (dispTgt lay ci).eval s = pcOf (m4Pc lay ci (E / 2 ^ chB0 lay ci % 2 ^ chBits lay ci) 0) := by
  rw [dispTgt_eval, h23]
  interval_cases lay
  · simp only [nCh, if_true] at hci
    interval_cases ci
    · exact dispVal_tab00 E hE
    · exact dispVal_tab01 E hE
  · simp only [nCh, show (1 : Nat) ≠ 0 by decide, if_false] at hci
    interval_cases ci; exact dispVal_tab1 E hE
  · simp only [nCh, show (2 : Nat) ≠ 0 by decide, if_false] at hci
    interval_cases ci; exact dispVal_tab2 E hE
  · simp only [nCh, show (3 : Nat) ≠ 0 by decide, if_false] at hci
    interval_cases ci; exact dispVal_tab3 E hE
  · simp only [nCh, show (4 : Nat) ≠ 0 by decide, if_false] at hci
    interval_cases ci; exact dispVal_tab4 E hE

/-! ## Bits -/

theorem land16 (n : Nat) : n &&& 16 = 16 * (n / 16 % 2) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.and_two_pow, Nat.toNat_testBit, Nat.mul_comm]

theorem srl_eval (u b : Nat) (hE : u < 2 ^ 12) (hb : b ≤ 12) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    (Rv.E.bin .srl (.reg .x23) (cw b)).eval s = BitVec.ofNat 64 (u / 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Rv.E.eval, BinOp.eval, cw, h23, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : u / 2 ^ b ≤ u := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 64 by omega), Nat.mod_eq_of_lt (show u / 2 ^ b < 2 ^ 64 by omega)]

theorem stW_eval (a : Nat) (v : Rv.E) (s : MachineState) :
    (stW a v).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 4 (v.eval s) := rfl

theorem bitOf_lt (u lam : Nat) : bitOf u lam < 2 := Nat.mod_lt _ (by decide)

/-! ## Family facts -/

theorem okFold_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)}
    (h : okFold false o e post = true) :
    o = some e ∧ resOK gkL e = true ∧ knownB post e = true ∧ keepB (fkeep false) e = true := by
  simp only [okFold, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem blockCheck_lvl {lay ci v : Nat} (h : blockCheck lay ci v = true) (kk : Nat) (hkk : kk < lvlN lay ci) :
    okFold false (runAt (lvlK lay (chB0 lay ci + kk)) [] (m4Pc lay ci v kk + 2) (lvlDirs lay ci kk))
      (lvlExp lay ci v kk) (lvlPost lay ci v kk) = true := by
  simp only [blockCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 kk hkk

theorem blockCheck_ent {lay ci v : Nat} (h : blockCheck lay ci v = true) :
    okFold false (runAt (lvlK lay (chB0 lay ci)) [] (m4Pc lay ci v 0) []) (entExp lay ci v) (entPost lay ci v) = true := by
  simp only [blockCheck, Bool.and_eq_true] at h; exact h.1

theorem FrameOK.trans {s0 s t : MachineState} (h1 : FrameOK s0 s)
    (hr : ∀ r ∈ fkeep false, t.getReg r = s.getReg r)
    (hm : ∀ A, A < 2 ^ 64 → (A + 8 ≤ 0x120 ∨ 0x390 ≤ A) →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : FrameOK s0 t :=
  ⟨fun r hr' => (hr r hr').trans (h1.1 r hr'), fun A hA hA' => (hm A hA hA').trans (h1.2 A hA hA')⟩

def FCtx.sib (fc : FCtx) (lam : Nat) : Val := slice fc.wl (fc.sibOff + pathStrideL fc.lay * lam) 16

theorem sib_words (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (s : MachineState)
    (hG : Glob gkL fc.wl fc.pk s) (_hF : Fresh fc.wl fc.lay 42 s) :
    s.getMem (BitVec.ofNat 64 (sibAddr fc.lay lam)) = vw0 (fc.sib lam) ∧
    s.getMem (BitVec.ofNat 64 (sibAddr fc.lay lam + 8)) = vw1 (fc.sib lam) := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -, -, -, -, hso, -⟩ := hfc
  unfold pathStrideL at hsz
  unfold sibAddr FCtx.sib pathStrideL
  rw [vw0_slice, vw1_slice, ← hso, show 0x800 + fc.sibOff + 16 * lam = 0x800 + (fc.sibOff + 16 * lam) by omega,
    show 0x800 + (fc.sibOff + 16 * lam) + 8 = 0x800 + (fc.sibOff + 16 * lam + 8) by omega]
  exact ⟨wit_word hG.2.1 _ (by omega) (by omega), wit_word hG.2.1 _ (by omega) (by omega)⟩

/-- The spec's input of fold level `lam` with current value `v`. -/
def FCtx.input (fc : FCtx) (lam : Nat) (v : Val) : List Byte :=
  if fc.E / 2 ^ lam % 2 = 1 then fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) (fc.sib lam) v
  else fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) v (fc.sib lam)

theorem length_sib (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) :
    (fc.sib lam).length = 16 := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -⟩ := hfc
  unfold FCtx.sib; apply length_slice16
  unfold pathStrideL at hsz ⊢
  omega

/-- The heap index of the output node of level `lam`. -/
def FCtx.heap (fc : FCtx) (lam : Nat) : Nat :=
  let base := 2 ^ (fc.h - (lam + 1))
  if fc.lay = 0 then 3 * base - 1 - (base + fc.E / 2 ^ (lam + 1))
  else base + fc.E / 2 ^ (lam + 1)

/-- The oracle block of level `lam` (`addrFmt`): the node tweak with `p = 0` and the heap index. -/
def FCtx.hinput (fc : FCtx) (lam : Nat) (v : Val) : Query := queryOfWords 0
  [BitVec.ofNat 64 fc.lo0, BitVec.ofNat 64 (twHi fc.tau (fc.heap lam)), 0, 0,
    if bitOf fc.E lam = 1 then vw0 (fc.sib lam) else vw0 v,
    if bitOf fc.E lam = 1 then vw1 (fc.sib lam) else vw1 v,
    if bitOf fc.E lam = 1 then vw0 v else vw0 (fc.sib lam),
    if bitOf fc.E lam = 1 then vw1 v else vw1 (fc.sib lam)]

theorem blk_eq_pad64 (l : List Byte) (hl : l.length = 64) : (⟨0, ofList _ l⟩ : Query) = pad64 l := by
  unfold pad64 padTo64 padBlocks
  rw [hl]
  simp [zeros]

theorem heap_lt (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) : fc.heap lam < 2 ^ 32 := by
  have := hfc.2.1
  have h1 : 2 ^ (fc.h - (lam + 1)) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : fc.E / 2 ^ (lam + 1) ≤ fc.E := Nat.div_le_self _ _
  have h3 : fc.E < 2 ^ 11 := lt_of_lt_of_le hfc.2.2.1 (Nat.pow_le_pow_right (by decide) hfc.2.1)
  unfold FCtx.heap
  split
  · change 3 * 2 ^ (fc.h - (lam + 1)) - 1 - (2 ^ (fc.h - (lam + 1)) + fc.E / 2 ^ (lam + 1)) < _
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  · change 2 ^ (fc.h - (lam + 1)) + fc.E / 2 ^ (lam + 1) < _
    omega

/-- A node's tree height as the oracle format reads it (hypertree nodes, tag 3). -/
def NodeH (fc : FCtx) : Prop := fc.t = 3 ∧ fc.f2 = fc.lay ∧ fc.tau < 2 ^ 32

theorem mirror_band (d j : Nat) (hd : d ≤ 10) (hj : j < 2 ^ d) :
    TopHeap.mirror (2 ^ d + j) = 3 * 2 ^ d - 1 - (2 ^ d + j) := by
  interval_cases d
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_pos (show (1 + j : Nat) < 2 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (2 + j : Nat) < 2 by omega), if_pos (show (2 + j : Nat) < 4 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (4 + j : Nat) < 2 by omega), if_neg (show ¬ (4 + j : Nat) < 4 by omega), if_pos (show (4 + j : Nat) < 8 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (8 + j : Nat) < 2 by omega), if_neg (show ¬ (8 + j : Nat) < 4 by omega), if_neg (show ¬ (8 + j : Nat) < 8 by omega), if_pos (show (8 + j : Nat) < 16 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (16 + j : Nat) < 2 by omega), if_neg (show ¬ (16 + j : Nat) < 4 by omega), if_neg (show ¬ (16 + j : Nat) < 8 by omega), if_neg (show ¬ (16 + j : Nat) < 16 by omega), if_pos (show (16 + j : Nat) < 32 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (32 + j : Nat) < 2 by omega), if_neg (show ¬ (32 + j : Nat) < 4 by omega), if_neg (show ¬ (32 + j : Nat) < 8 by omega), if_neg (show ¬ (32 + j : Nat) < 16 by omega), if_neg (show ¬ (32 + j : Nat) < 32 by omega), if_pos (show (32 + j : Nat) < 64 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (64 + j : Nat) < 2 by omega), if_neg (show ¬ (64 + j : Nat) < 4 by omega), if_neg (show ¬ (64 + j : Nat) < 8 by omega), if_neg (show ¬ (64 + j : Nat) < 16 by omega), if_neg (show ¬ (64 + j : Nat) < 32 by omega), if_neg (show ¬ (64 + j : Nat) < 64 by omega), if_pos (show (64 + j : Nat) < 128 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (128 + j : Nat) < 2 by omega), if_neg (show ¬ (128 + j : Nat) < 4 by omega), if_neg (show ¬ (128 + j : Nat) < 8 by omega), if_neg (show ¬ (128 + j : Nat) < 16 by omega), if_neg (show ¬ (128 + j : Nat) < 32 by omega), if_neg (show ¬ (128 + j : Nat) < 64 by omega), if_neg (show ¬ (128 + j : Nat) < 128 by omega), if_pos (show (128 + j : Nat) < 256 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (256 + j : Nat) < 2 by omega), if_neg (show ¬ (256 + j : Nat) < 4 by omega), if_neg (show ¬ (256 + j : Nat) < 8 by omega), if_neg (show ¬ (256 + j : Nat) < 16 by omega), if_neg (show ¬ (256 + j : Nat) < 32 by omega), if_neg (show ¬ (256 + j : Nat) < 64 by omega), if_neg (show ¬ (256 + j : Nat) < 128 by omega), if_neg (show ¬ (256 + j : Nat) < 256 by omega), if_pos (show (256 + j : Nat) < 512 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (512 + j : Nat) < 2 by omega), if_neg (show ¬ (512 + j : Nat) < 4 by omega), if_neg (show ¬ (512 + j : Nat) < 8 by omega), if_neg (show ¬ (512 + j : Nat) < 16 by omega), if_neg (show ¬ (512 + j : Nat) < 32 by omega), if_neg (show ¬ (512 + j : Nat) < 64 by omega), if_neg (show ¬ (512 + j : Nat) < 128 by omega), if_neg (show ¬ (512 + j : Nat) < 256 by omega), if_neg (show ¬ (512 + j : Nat) < 512 by omega), if_pos (show (512 + j : Nat) < 1024 by omega)]
    all_goals omega
  · norm_num only [Nat.reducePow, Nat.reduceMul] at hj ⊢
    simp only [TopHeap.mirror, if_neg (show ¬ (1024 + j : Nat) < 2 by omega), if_neg (show ¬ (1024 + j : Nat) < 4 by omega), if_neg (show ¬ (1024 + j : Nat) < 8 by omega), if_neg (show ¬ (1024 + j : Nat) < 16 by omega), if_neg (show ¬ (1024 + j : Nat) < 32 by omega), if_neg (show ¬ (1024 + j : Nat) < 64 by omega), if_neg (show ¬ (1024 + j : Nat) < 128 by omega), if_neg (show ¬ (1024 + j : Nat) < 256 by omega), if_neg (show ¬ (1024 + j : Nat) < 512 by omega), if_neg (show ¬ (1024 + j : Nat) < 1024 by omega), if_pos (show (1024 + j : Nat) < 2048 by omega)]
    all_goals omega


theorem heapW1_twHi (tau j : Nat) (hj : j < 2 ^ 32) :
    TopHeap.heapW1 (BitVec.ofNat 64 (twHi tau j)) =
      BitVec.ofNat 64 (twHi tau (TopHeap.mirror j)) := by
  have hm := TopHeap.mirror_lt j hj
  unfold TopHeap.heapW1 twHi
  simp only [BitVec.toNat_ofNat]
  rw [show (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) % 2 ^ 64 = tau % 2 ^ 32 + 2 ^ 32 * j by omega,
    show (tau % 2 ^ 32 + 2 ^ 32 * j) % 4294967296 = tau % 2 ^ 32 by omega,
    show (tau % 2 ^ 32 + 2 ^ 32 * j) / 4294967296 = j by omega,
    Nat.mod_eq_of_lt (show TopHeap.mirror j < 2 ^ 32 from hm)]
  rfl


theorem addrFmt_nodeInput_words (lay tau lam j : Nat) (l r : Val)
    (hl : l.length = 16) (hr : r.length = 16) (hlay : lay < 5) (htau : tau < 2 ^ 32)
    (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32)
    (hh : heapIndex (height (lay % 256)) lam j < 2 ^ 32) :
    addrFmt (nodeInput lay tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (Ref.MaskHeader.nodeHeader lay),
        BitVec.ofNat 64 (twHi tau (if lay = 0 then TopHeap.mirror (heapIndex (height (lay % 256)) lam j)
          else heapIndex (height (lay % 256)) lam j)), 0, 0, vw0 l, vw1 l, vw0 r, vw1 r] := by
  rw [addrFmt_nodeInput]
  change Ref.MaskHeader.query (EncodingRotate.query (Ref.LeafCarry.query (TopHeap.query (fmt (thInput (tweak 3 lay tau lam j) (l ++ r)))))) = _
  rw [fmt_thInput_node _ _ _ _ _ (by simp [hl, hr]) hlam hj,
    blk_eq_pad64 _ (by simp [hl, hr])]
  change Ref.MaskHeader.query (EncodingRotate.query (Ref.LeafCarry.query (TopHeap.query (pad64 (nodeF 3 lay tau 0 _ l r))))) = _
  rw [pad64_nodeF _ _ _ _ _ _ _ hl hr]
  rw [Ref.LeafCarry.query_fixed_length _ (by simp only [TopHeap.query, queryOfWords]; split <;> exact (by decide : (0 : Nat) ≠ 10))]
  rw [TopHeap.query_words _ _ _ rfl]
  have hw : (BitVec.ofNat 64 (twLo 3 lay tau 0)).toNat = 769 + 65536 * lay := by
    simp only [BitVec.toNat_ofNat]; unfold twLo; omega
  have hrot (w : Word) : EncodingRotate.query (queryOfWords 0
      [BitVec.ofNat 64 (twLo 3 lay tau 0), w, 0, 0, vw0 l, vw1 l, vw0 r, vw1 r]) =
      queryOfWords 0 [BitVec.ofNat 64 (twLo 3 lay tau 0), w, 0, 0, vw0 l, vw1 l, vw0 r, vw1 r] := by
    apply EncodingRotate.query_fixed
    have hh := AddressFormat.queryOfWords_class (BitVec.ofNat 64 (twLo 3 lay tau 0)) [w, 0, 0, vw0 l, vw1 l, vw0 r, vw1 r]
    rw [hw] at hh
    omega
  by_cases h0 : lay = 0
  · subst lay
    rw [if_pos (by simpa [hw]), if_pos rfl, heapW1_twHi tau _ hh, hrot, Ref.MaskHeader.query_words 0 _ _ rfl, hw, Ref.MaskHeader.header_node 0 (by omega)]
  · rw [if_neg (by rw [hw]; omega), if_neg h0, hrot, Ref.MaskHeader.query_words 0 _ _ rfl, hw, Ref.MaskHeader.header_node lay hlay]

theorem fmt_input (fc : FCtx) (hfc : fc.ok) (hn : NodeH fc) (lam : Nat) (hlam : lam < fc.h) (v : Val)
    (hv : v.length = 16) : addrFmt (fc.input lam v) = fc.hinput lam v := by
  have hs := length_sib fc hfc lam hlam
  have hl : fc.lay < 5 := hfc.2.2.2.2.2.2.2.2.2.2.1
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  have hH : height (fc.lay % 256) = fc.h := by
    rw [Nat.mod_eq_of_lt (by omega), hh]
    interval_cases fc.lay <;> rfl
  have hj : fc.E / 2 ^ (lam + 1) < 2 ^ (fc.h - (lam + 1)) := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    exact hfc.2.2.1
  have hp : 2 ^ (fc.h - (lam + 1)) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) (by have := hfc.2.1; omega)
  have hheap : heapIndex (height (fc.lay % 256)) (lam + 1) (fc.E / 2 ^ (lam + 1)) < 2 ^ 32 := by
    unfold heapIndex; rw [hH]; omega
  have heq : (if fc.lay = 0 then TopHeap.mirror (heapIndex (height (fc.lay % 256)) (lam + 1) (fc.E / 2 ^ (lam + 1)))
      else heapIndex (height (fc.lay % 256)) (lam + 1) (fc.E / 2 ^ (lam + 1))) = fc.heap lam := by
    unfold heapIndex FCtx.heap
    rw [hH]
    split_ifs
    · exact mirror_band _ _ (by have := hfc.2.1; omega) hj
    · rfl
  obtain ⟨ht, hf, htau⟩ := hn
  have key (l r : Val) (hlv : l.length = 16) (hrv : r.length = 16) :=
    addrFmt_nodeInput_words fc.lay fc.tau (lam + 1) (fc.E / 2 ^ (lam + 1)) l r hlv hrv hl htau
      (by have := hfc.2.1; omega) (by omega) hheap
  unfold FCtx.input FCtx.node FCtx.hinput bitOf
  rw [ht, hf]
  change addrFmt (if fc.E / 2 ^ lam % 2 = 1 then nodeInput _ _ _ _ _ _ else nodeInput _ _ _ _ _ _) = _
  split_ifs
  · rw [key _ _ hs hv, heq]
    have hlo : Ref.MaskHeader.nodeHeader fc.lay = fc.lo0 := by
      unfold FCtx.lo0
      rw [ht,hf,Nat.div_eq_of_lt htau]
      convert (Ref.MaskHeader.header_node fc.lay hl).symm using 2 <;> omega
    rw [hlo]
  · rw [key _ _ hv hs, heq]
    have hlo : Ref.MaskHeader.nodeHeader fc.lay = fc.lo0 := by
      unfold FCtx.lo0
      rw [ht,hf,Nat.div_eq_of_lt htau]
      convert (Ref.MaskHeader.header_node fc.lay hl).symm using 2 <;> omega
    rw [hlo]

theorem pad64_hinput (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (v : Val)
    (hv : v.length = 16) :
    fc.hinput lam v = queryOfWords 0
      [BitVec.ofNat 64 fc.lo0,
        BitVec.ofNat 64 (twHi fc.tau (fc.heap lam)), 0, 0,
        if bitOf fc.E lam = 1 then vw0 (fc.sib lam) else vw0 v,
        if bitOf fc.E lam = 1 then vw1 (fc.sib lam) else vw1 v,
        if bitOf fc.E lam = 1 then vw0 v else vw0 (fc.sib lam),
        if bitOf fc.E lam = 1 then vw1 v else vw1 (fc.sib lam)] := rfl

theorem complement_div (e b : Nat) (he : e < 2048) (hb : b ≤ 11) :
    (4095 - e) / 2 ^ b = 3 * 2 ^ (11 - b) - 1 - (2 ^ (11 - b) + e / 2 ^ b) := by
  interval_cases b <;> norm_num <;> omega


theorem U_div (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 ≤ fc.h) :
    fc.U / 2 ^ (lam + 1) = fc.heap lam := by
  unfold FCtx.U FCtx.heap
  by_cases h0 : fc.lay = 0
  · have hh : fc.h = 11 := by
      simpa [h0, heightL] using hfc.2.2.2.2.2.2.2.2.2.2.2.1
    rw [if_pos h0, if_pos h0, hh]
    exact complement_div fc.E (lam + 1) (by simpa [hh] using hfc.2.2.1) (by omega)
  · rw [if_neg h0, if_neg h0]
    have e : 2 ^ fc.h = 2 ^ (fc.h - (lam + 1)) * 2 ^ (lam + 1) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.add_comm, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _)]

theorem U_lt (fc : FCtx) (hfc : fc.ok) : fc.U < 2 ^ 12 := by
  have h1 := hfc.2.1
  have h2 : 2 ^ fc.h ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) h1
  have h3 := hfc.2.2.1
  unfold FCtx.U; split <;> omega

theorem lo0_lt (fc : FCtx) (hfc : fc.ok) : fc.lo0 < 2 ^ 64 := by
  obtain ⟨-, -, -, ht, hf2, -⟩ := hfc
  unfold FCtx.lo0
  apply Ref.MaskHeader.header_lt
  omega

/-! ## The memory of a level run -/

theorem lvlExp_mem (lay ci v kk : Nat) :
    (lvlExp lay ci v kk).st.mem = lvlMem lay (chB0 lay ci + kk) (v / 2 ^ kk % 2) (lvlNb lay ci v kk) := by
  simp only [lvlExp]; split_ifs <;> rfl

theorem lvlMem_1C8 (lay lam t : Nat) (nb : E) (s : MachineState) :
    memEval s (lvlMem lay lam t nb) (BitVec.ofNat 64 0x348) =
      StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0x348)) 4 (nb.eval s) := by
  unfold lvlMem; rw [List.cons_append]; rw [memEval_cons_eq _ _ _ _ _ rfl, stW_eval]

theorem lvlMem_340 (lay lam t : Nat) (ht : t < 2) (hl : lam = 0) (nb : E) (s : MachineState) :
    memEval s (lvlMem lay lam t nb) (BitVec.ofNat 64 0x340) =
      StoreKind.merge .b (s.getMem (BitVec.ofNat 64 0x340)) (if lay < 4 then 2 else 1) (BitVec.ofNat 64 (if lay < 4 then lay else 3)) := by
  unfold lvlMem
  rw [if_pos hl, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
    memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
  rfl

theorem lvlMem_sib (lay lam t : Nat) (ht : t < 2) (nb : E) (s : MachineState) :
    memEval s (lvlMem lay lam t nb) (BitVec.ofNat 64 (0x370 - 16 * t)) =
      s.getMem (BitVec.ofNat 64 (sibAddr lay lam)) ∧
    memEval s (lvlMem lay lam t nb) (BitVec.ofNat 64 (0x370 - 16 * t + 8)) =
      s.getMem (BitVec.ofNat 64 (sibAddr lay lam + 8)) := by
  unfold lvlMem
  rw [List.cons_append, List.cons_append, List.cons_append]
  constructor
  · rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]; rfl

theorem lvlMem_frame (lay lam t : Nat) (nb : E) (s : MachineState) (A : Nat) (hA : A < 2 ^ 64)
    (h0 : lam ≠ 0 ∨ A ≠ 0x340) (h1 : A ≠ 0x348) (h3 : A ≠ 0x370 - 16 * t + 8) (h4 : A ≠ 0x370 - 16 * t) :
    memEval s (lvlMem lay lam t nb) (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame_ofNat _ _ _ hA
  unfold lvlMem
  by_cases hl : lam = 0
  · rw [if_pos hl]
    have h0' : A ≠ 0x340 := by omega
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega
  · rw [if_neg hl]
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl) <;> simp <;> omega

/-! ## One level -/

theorem lvlExp_brs (lay ci v kk : Nat) : (lvlExp lay ci v kk).brs = [] := by
  simp only [lvlExp]; split_ifs <;> rfl

/-- What a level run gives: the checked run's result at the level's block. -/
theorem level_run (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h)
    (hlv : fc.lay = 0 ∨ lam + 1 < fc.h)
    (hchk : blockCheck fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    Steps image s (lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).steps
        (lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).cycles
        ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s) ∧
      ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).ecall = true →
        fetch image ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s) =
          some (.base .ECALL)) ∧
      KnownOK (lvlPost fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam))
        ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s) ∧
      (∀ x ∈ fkeep false, ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s).getReg x =
        s.getReg x) ∧
      Glob gkL fc.wl fc.pk ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s) ∧
      (∀ A, ((lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).toState s).getMem A =
        memEval s (lvlMem fc.lay lam (bitOf fc.E lam) (lvlNb fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam))) A) := by
  have hl := hfc.2.2.2.2.2.2.2.2.2.2.1
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hci, hsum, hkb, -, -, -, -⟩ := chunk_facts fc.lay lam hl (by omega)
  have hbit : fc.blk (fc.ci lam) / 2 ^ fc.kk lam % 2 = bitOf fc.E lam := by
    unfold FCtx.blk FCtx.kk FCtx.ci bitOf
    rw [blk_bit _ _ _ _ hkb, hsum]
  have hkn' : fc.kk lam < lvlN fc.lay (fc.ci lam) := by
    unfold lvlN
    split
    · exact hkb
    · rename_i h0
      have e1 : chBits fc.lay (fc.ci lam) = heightL fc.lay := by simp [chBits, h0]
      have e2 : fc.kk lam ≤ lam := Nat.sub_le _ _
      rcases hlv with h | h
      · exact absurd h h0
      · rw [e1]; omega
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec (blockCheck_lvl hchk (fc.kk lam) hkn')
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc, hFresh, -, hlink⟩ := hs
  have hK' : KnownOK (lvlK fc.lay (chB0 fc.lay (fc.ci lam) + fc.kk lam)) s := by
    unfold FCtx.kk FCtx.ci; rw [hsum]; exact hK
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK' (by
    intro b hb; rw [lvlExp_brs] at hb; simp at hb)
  refine ⟨hst, hec, knownB_ok hkn s, keepB_ok hkeep s, hglob _ _ hG, ?_⟩
  intro A
  rw [PRes.toState_getMem, lvlExp_mem, hbit]
  unfold FCtx.kk FCtx.ci
  rw [hsum]

theorem level_frame {fc : FCtx} {lam : Nat} {nb : E} {s t : MachineState}
    (hm : ∀ A, t.getMem A = memEval s (lvlMem fc.lay lam (bitOf fc.E lam) nb) A) (A : Nat) (hA : A < 2 ^ 64)
    (h0 : lam ≠ 0 ∨ A ≠ 0x340) (h1 : A ≠ 0x348) (h3 : A ≠ 0x370 - 16 * bitOf fc.E lam + 8)
    (h4 : A ≠ 0x370 - 16 * bitOf fc.E lam) :
    t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  rw [hm]; exact lvlMem_frame _ _ _ _ _ A hA h0 h1 h3 h4

/-- The NB+12 value of a non-root level: the parent's heap index. -/
theorem lvlNb_eval (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 < fc.h) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 fc.U) :
    (lvlNb fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).eval s = BitVec.ofNat 64 (fc.heap lam) := by
  have hl := hfc.2.2.2.2.2.2.2.2.2.2.1
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hci, hsum, hkb, hle, -, -, hcon⟩ := chunk_facts fc.lay lam hl (by omega)
  have hU := U_lt fc hfc
  have hsum' : chB0 fc.lay (fc.ci lam) + fc.kk lam = lam := hsum
  have h11 := hfc.2.1
  unfold lvlNb
  simp only [hsum', if_neg (show ¬ (lam + 1 = heightL fc.lay) by omega)]
  split
  · rename_i hc
    obtain ⟨-, hc⟩ := hc
    have htop := hcon hc
    simp only [cw, E.eval]
    congr 1
    unfold FCtx.heap FCtx.blk FCtx.ci FCtx.kk
    rw [blk_top _ _ _ _ (by rw [htop, ← hh]; exact hfc.2.2.1), ← hh,
      show chB0 fc.lay (chOf fc.lay lam) + (lam - chB0 fc.lay (chOf fc.lay lam) + 1) = lam + 1 by omega]
  · rw [srl_eval fc.U (lam + 1) hU (by omega) s h23, U_div fc hfc lam (by omega)]

theorem blk_entry_run (lay ci v : Nat) (hc : blockCheck lay ci v = true) (s : MachineState)
    (hpc : s.pc = pcOf (m4Pc lay ci v 0)) (hK : KnownOK (lvlK lay (chB0 lay ci)) s) :
    ∃ t, Steps image s 1 1 t ∧ fetch image t = some (.base .ECALL) ∧ KnownOK (entPost lay ci v) t ∧
      (∀ x ∈ fkeep false, t.getReg x = s.getReg x) ∧ (∀ wl pk, Glob gkL wl pk s → Glob gkL wl pk t) ∧
      (∀ A, t.getMem A = s.getMem A) ∧ t.pc = pcOf (m4Pc lay ci v 0 + 1) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec (blockCheck_ent hc)
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by intro b hb; simp [entExp] at hb)
  refine ⟨_, hst, hec rfl, knownB_ok hkn s, keepB_ok hkeep s, hglob, fun A => ?_, ?_⟩
  · rw [PRes.toState_getMem]; rfl
  · rw [PRes.toState_pc _ _ rfl]; rfl

def slotEnterSpec (E : Nat) : Spec :=
  ⟨[(.x16, cw (0x1000 + 4 * (topSlotPc E + 1)))], [], m4Pc 0 0 (E % 64) 0, false, 1, [], none, 1⟩
def slotReturnSpec (E : Nat) : Spec :=
  ⟨[], [], m4Pc 0 1 (E / 64) 0, false, 1, [], none, 1⟩
def slotEnterKeep : List Reg := [.x14, .x17, .x23, .x27, .x30, .x31]

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem slotSpecsChecks : (List.range 2048).all (fun E =>
    specB gkL (some (topSlotEnterExp E)) (slotEnterSpec E) (foldK 0 704) slotEnterKeep &&
    specB gkL (some (topSlotReturnExp E)) (slotReturnSpec E) (foldK 0 64) (fkeep false)) = true := by
  decide +kernel

theorem slotSpecsCheck_at (E : Nat) (hE : E < 2048) :
    specB gkL (some (topSlotEnterExp E)) (slotEnterSpec E) (foldK 0 704) slotEnterKeep = true ∧
    specB gkL (some (topSlotReturnExp E)) (slotReturnSpec E) (foldK 0 64) (fkeep false) = true := by
  have h := List.all_eq_true.mp slotSpecsChecks E (List.mem_range.mpr hE)
  simpa only [Bool.and_eq_true] using h

theorem slotEnter_run (E : Nat) (hE : E < 2048) (s : MachineState)
    (hpc : s.pc = pcOf (topSlotPc E)) (hK : KnownOK (foldK 0 704) s) :
    ∃ u, SpecRes gkL (slotEnterSpec E) (foldK 0 704) slotEnterKeep s u := by
  have hc := topSlotCheck_at E hE
  simp only [topSlotCheck, Bool.and_eq_true] at hc
  have hr := optBeq_eq hc.1
  apply spec_run (known := foldK 0 704) (stops := [m4Pc 0 0 (E % 64) 0]) (dirs := []) _ s hpc hK
  · intro b hb; simp [slotEnterSpec] at hb
  · rw [hr]; exact (slotSpecsCheck_at E hE).1

theorem slotReturn_run (E : Nat) (hE : E < 2048) (s : MachineState)
    (hpc : s.pc = pcOf (topSlotPc E + 1)) (hK : KnownOK (foldK 0 64) s) :
    ∃ u, SpecRes gkL (slotReturnSpec E) (foldK 0 64) (fkeep false) s u := by
  have hc := topSlotCheck_at E hE
  simp only [topSlotCheck, Bool.and_eq_true] at hc
  have hr := optBeq_eq hc.2
  apply spec_run (known := foldK 0 64) (stops := [m4Pc 0 1 (E / 64) 0]) (dirs := []) _ s hpc hK
  · intro b hb; simp [slotReturnSpec] at hb
  · rw [hr]; exact (slotSpecsCheck_at E hE).2

def levelCost (lay lam : Nat) : Nat :=
  if lam + 1 = heightL lay then 14
  else if lam - chB0 lay (chOf lay lam) + 1 < chBits lay (chOf lay lam) then
    (if lam = 0 then 2 else 0) + (if isConstLvl lay lam then 6 else 7) + 8
  else (if lam = 0 then 2 else 0) + 9 + 8

theorem levelCost_le (lay lam : Nat) : levelCost lay lam ≤ 22 := by
  unfold levelCost; split_ifs <;> omega

/-- A non-root level: the level run (and at the end of chunk 0 of layer 0 the dispatch and the
entry of the chunk-1 block) up to the next node hash. -/
theorem level_lt (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 < fc.h)
    (hchk : ∀ ci, ci < nCh fc.lay → ∀ v, v < 2 ^ chBits fc.lay ci → blockCheck fc.lay ci v = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t n, Steps image s n n t ∧ n + 8 = levelCost fc.lay lam ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = fc.hinput lam v ∧
      ∀ a, FoldInv fc s0 (lam + 1) (answerBytes 16 a) (writeHash t a) := by
  have hl := hfc.2.2.2.2.2.2.2.2.2.2.1
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hci, hsum, hkb, hle, hnext, hend, -⟩ := chunk_facts fc.lay lam hl (by omega)
  have hc0 := hchk _ hci _ (blk_lt fc _)
  obtain ⟨hst, hec, hK', hkeep', hglob, hmem⟩ :=
    level_run fc hfc lam (by omega) (Or.inr hlam) hc0 s0 v s hs
  set r := lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam) with hr
  set b := bitOf fc.E lam with hbdef
  set b' := bitOf fc.E (lam + 1) with hb'def
  have hb2 := bitOf_lt fc.E lam
  have hb2' := bitOf_lt fc.E (lam + 1)
  have hlo := lo0_lt fc hfc
  have hU := U_lt fc hfc
  have hhp := heap_lt fc hfc lam (by omega)
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc, hFresh, -, hlink⟩ := hs
  have hvA := fc.vA_lt hfc lam hlam
  rw [hvA] at hv0
  rw [hvA, show 0x360 + 16 * bitOf fc.E lam + 8 = 0x368 + 16 * bitOf fc.E lam by omega] at hv1
  have hd : fc.vA (lam + 1) = 0x120 + 16 * b' ∨ fc.vA (lam + 1) = 0x360 + 16 * b' := fc.vA_cases (lam + 1)
  have hd1 : 0x120 ≤ fc.vA (lam + 1) ∧ fc.vA (lam + 1) + 32 ≤ 0x390 ∧ fc.vA (lam + 1) % 8 = 0 ∧
      (fc.vA (lam + 1) + 32 ≤ 0x340 ∨ 0x360 ≤ fc.vA (lam + 1)) := by
    rcases hd with h | h <;> rw [h] <;> omega
  have hsd : safeDest (fc.vA (lam + 1)) = true := by
    rcases hd with h | h
    · rw [h]; rcases (show b' = 0 ∨ b' = 1 by omega) with h | h <;> rw [h] <;> decide
    · rw [h]; rcases (show b' = 0 ∨ b' = 1 by omega) with h | h <;> rw [h] <;> decide
  have hsl := sib_words fc hfc lam (by omega) s hG hFresh
  have hnb := lvlNb_eval fc hfc lam hlam s h23
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hroot : ¬ (chB0 fc.lay (fc.ci lam) + fc.kk lam + 1 = heightL fc.lay) := by
    simp only [FCtx.kk, FCtx.ci] at hsum ⊢; rw [hsum]; omega
  -- facts about the state after the level's hash call `t`, shared by both cases
  have key : ∀ t : MachineState, (∀ A, t.getMem A = (r.toState s).getMem A) →
      (∀ x ∈ fkeep false, t.getReg x = s.getReg x) → Glob gkL fc.wl fc.pk t →
      t.getReg .x10 = BitVec.ofNat 64 0x340 → t.getReg .x11 = BitVec.ofNat 64 64 →
      t.getReg .x12 = BitVec.ofNat 64 (fc.vA (lam + 1)) → KnownOK (foldK fc.lay 64) t →
      t.pc = pcOf (fc.X (lam + 1) + 1) →
      hashArgumentsValid t = true ∧ hashInput t = fc.hinput lam v ∧
      ∀ a, FoldInv fc s0 (lam + 1) (answerBytes 16 a) (writeHash t a) := by
    intro t htm htk htg h10 h11 h12 htK htpc
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x340 → A ≠ 0x348 → A ≠ 0x370 - 16 * b + 8 → A ≠ 0x370 - 16 * b →
        t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h0 h1 h3 h4 => by
      rw [htm]; exact level_frame hmem A hA (Or.inr h0) h1 h3 h4
    have m1C0 : t.getMem (BitVec.ofNat 64 0x340) = BitVec.ofNat 64 fc.lo0 := by
      by_cases hl0 : lam = 0
      · rw [htm, hmem, lvlMem_340 _ _ _ hb2 hl0]; exact hN0.1 hl0
      · rw [htm, level_frame hmem 0x340 (by omega) (Or.inl hl0) (by omega) (by omega) (by omega)]
        exact hN0.2 hl0
    have m1C8 : t.getMem (BitVec.ofNat 64 0x348) =
        BitVec.ofNat 64 (fc.tau % 2 ^ 32 + 2 ^ 32 * fc.heap lam) := by
      rw [htm, hmem, lvlMem_1C8, hnb, stMerge_eval _ _ _ hhp hN8]
    have msib0 : t.getMem (BitVec.ofNat 64 (0x370 - 16 * b)) = vw0 (fc.sib lam) := by
      rw [htm, hmem, (lvlMem_sib _ _ _ hb2 _ s).1]; exact hsl.1
    have msib1 : t.getMem (BitVec.ofNat 64 (0x370 - 16 * b + 8)) = vw1 (fc.sib lam) := by
      rw [htm, hmem, (lvlMem_sib _ _ _ hb2 _ s).2]; exact hsl.2
    have mv0 : t.getMem (BitVec.ofNat 64 (0x360 + 16 * b)) = vw0 v := by
      rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv0
    have mv1 : t.getMem (BitVec.ofNat 64 (0x368 + 16 * b)) = vw1 v := by
      rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv1
    refine ⟨?_, ?_, ?_⟩
    · exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
        (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
    · rw [hashInput_ofNat _ 0x340 0 h10 h11 (by decide) (by decide),
        pad64_hinput fc hfc lam (by omega) v hvl]
      congr 1
      simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero]
      have hhi : twHi fc.tau (fc.heap lam) = fc.tau % 2 ^ 32 + 2 ^ 32 * fc.heap lam := by
        unfold twHi; omega
      rw [hhi, m1C0, m1C8, mfr 0x350 (by omega) (by omega) (by omega) (by omega) (by omega),
        mfr 0x358 (by omega) (by omega) (by omega) (by omega) (by omega), hP 0x350 (by decide),
        hP 0x358 (by decide)]
      rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
      · rw [h0] at mv0 mv1 msib0 msib1
        simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
          Nat.reduceSub] at mv0 mv1 msib0 msib1
        rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
      · rw [h1] at mv0 mv1 msib0 msib1
        simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
        rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
    · intro a
      have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ fc.vA (lam + 1) ∨ fc.vA (lam + 1) + 32 ≤ A) =>
        writeHash_frame _ a _ A h12 hA (by omega) h
      refine ⟨Glob_writeHash htg a _ h12 hsd,
        ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rw [writeHash_getReg]
        simp only [lvlK, show lam + 1 ≠ 0 by omega, if_false] at hp
        exact htK p hp
      · rw [writeHash_getReg, htk .x23 (by simp [fkeep])]; exact h23
      · unfold NBhdr
        refine ⟨fun h => absurd h (by omega), fun _ => ?_⟩
        rw [wf 0x340 (by omega) (by omega), m1C0]
      · rw [wf 0x348 (by omega) (by omega), m1C8, BitVec.toNat_ofNat]; omega
      · rw [writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
      · rw [writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
      · refine FrameOK.trans (FrameOK.trans hF (fun r hr => htk r hr) (fun A hA hA' => ?_))
          (fun r _ => writeHash_getReg _ _ _) (fun A hA hA' => wf A hA (by omega))
        exact mfr A hA (by omega) (by omega) (by omega) (by omega)
      · rw [writeHash_pc, htpc, pcOf_add4]
      · refine Fresh_frame (Fresh_frame hFresh (fun A hA hA' =>
          mfr A hA (by omega) (by omega) (by omega) (by omega)))
          (fun A hA hA' => wf A hA (Or.inr (by omega)))
      · rw [writeHash_getReg]; exact h12
      · intro h0
        rw [writeHash_getReg, htk .x16 (by simp [fkeep])]
        exact hlink h0
  by_cases hmid : fc.kk lam + 1 < chBits fc.lay (fc.ci lam)
  · -- a level inside the chunk: one run up to the next level's hash
    have hnc : chOf fc.lay (lam + 1) = chOf fc.lay lam := hnext (by omega) hmid
    have hmid' : lam - chB0 fc.lay (chOf fc.lay lam) + 1 < chBits fc.lay (chOf fc.lay lam) := hmid
    have hbit' : fc.blk (fc.ci lam) / 2 ^ (fc.kk lam + 1) % 2 = b' := by
      rw [hb'def]
      unfold FCtx.blk FCtx.kk FCtx.ci bitOf
      rw [blk_bit _ _ _ _ hmid', ← Nat.add_assoc, hsum]
    have hn : r.steps = (if lam = 0 then 2 else 0) + (if isConstLvl fc.lay lam then 6 else 7) ∧
        r.cycles = r.steps ∧ r.ecall = true ∧ r.spc = none ∧
        r.pc = pcOf (m4Pc fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam + 1) + 1) := by
      have hsum' : chB0 fc.lay (fc.ci lam) + fc.kk lam = lam := hsum
      simp only [hr, lvlExp, hsum', if_neg (show ¬ (lam + 1 = heightL fc.lay) by omega), if_pos hmid, and_self]
    obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := hn
    have hKp := hK'
    simp only [lvlPost, if_neg hroot, if_pos hmid, hbit'] at hKp
    rw [show chB0 fc.lay (fc.ci lam) + fc.kk lam = lam from hsum] at hKp
    have hK2 := KnownOK_append.mp hKp
    refine ⟨r.toState s, r.steps, ?_, ?_, hec hn3, hKp (.x5, 0) (by simp [foldK, fk, gkOf, gkL, gkL0, baseK]), ?_⟩
    · rw [hn2] at hst; exact hst
    · rw [hn1]; unfold levelCost
      rw [if_neg (show ¬ (lam + 1 = heightL fc.lay) by omega), if_pos hmid']
    · obtain ⟨h1, h2, h3⟩ := key (r.toState s) (fun _ => rfl) hkeep' hglob
        (hK2.1 (.x10, _) (by simp [foldK, fk])) (hK2.1 (.x11, _) (by simp [foldK, fk]))
        (hK2.2 _ (List.mem_singleton_self _)) hK2.1 (by
          rw [PRes.toState_pc _ _ hn4, hn5]
          unfold FCtx.X FCtx.kk FCtx.ci FCtx.blk
          rw [hnc]
          congr 3
          omega)
      exact ⟨h1, h2, h3⟩
  · -- the end of chunk 0 of layer 0: dispatch into chunk 1, then the block entry
    obtain ⟨hl0, hlam5⟩ := hend (by omega) hmid
    have hci0 : fc.ci lam = 0 := by simp [FCtx.ci, chOf, hl0, hlam5]
    have hci1 : chOf fc.lay (lam + 1) = 1 := by simp [chOf, hl0, hlam5]
    have hn : r.steps = 7 ∧ r.cycles = 7 ∧ r.spc = some (mkBin .and (.reg .x16) (.c (~~~1#64))) := by
      have hsum' : chB0 fc.lay (fc.ci lam) + fc.kk lam = lam := hsum
      simp only [hr, lvlExp, hsum', if_neg (show ¬ (lam + 1 = heightL fc.lay) by omega), if_neg hmid,
        if_neg (show ¬ (lam = 0) by omega), Nat.zero_add, and_self]
    obtain ⟨hn1, hn2, hn3⟩ := hn
    have hKp := hK'
    simp only [lvlPost, if_neg hroot, if_neg hmid] at hKp
    have hE : fc.E < 2048 := by
      have := hfc.2.2.1
      simpa [hh, hl0, heightL] using this
    have hpcSlot : (r.toState s).pc = pcOf (topSlotPc fc.E + 1) := by
      have e1 : (r.toState s).pc = (mkBin .and (.reg .x16) (.c (~~~1#64))).eval s := by
        simp [PRes.toState, PRes.finalPc, hn3]
      rw [e1, mkBin_eval]
      simp only [BinOp.eval, E.eval, hlink hl0]
      have heven : pcOf (topSlotPc fc.E + 1) &&& ~~~1#64 = pcOf (topSlotPc fc.E + 1) := by
        show BitVec.ofNat 64 (0x1000 + 4 * (topSlotPc fc.E + 1)) &&& ~~~1#64 = BitVec.ofNat 64 (0x1000 + 4 * (topSlotPc fc.E + 1))
        exact even_andNot1 _ (by omega)
      exact heven
    have hfoldK : KnownOK (foldK 0 64) (r.toState s) := by simpa [hl0] using hKp
    obtain ⟨uSlot, hslot⟩ := slotReturn_run fc.E hE (r.toState s) hpcSlot hfoldK
    have hpc1 : uSlot.pc = pcOf (m4Pc fc.lay 1 (fc.blk 1) 0) := by
      rw [hslot.pc rfl]
      have hb : fc.blk 1 = fc.E / 64 := by
        simp [FCtx.blk, chB0, chBits, hl0]
        omega
      rw [hl0, hb]; rfl
    have hc1 := hchk 1 (by simp [nCh, hl0]) (fc.blk 1) (blk_lt fc 1)
    have hK6 : KnownOK (lvlK fc.lay (chB0 fc.lay 1)) uSlot := by
      have e : lvlK fc.lay (chB0 fc.lay 1) = foldK fc.lay 64 := by simp [lvlK, chB0, hl0]
      rw [e]; simpa [hl0] using hslot.known
    obtain ⟨t2, hst2, hec2, hK2, hkeep2, hglob2, hmem2, hpc2⟩ := blk_entry_run fc.lay 1 (fc.blk 1) hc1 _ hpc1 hK6
    have hb1 : fc.blk 1 % 2 = b' := by
      rw [hb'def]
      unfold FCtx.blk bitOf
      have := blk_bit fc.E (chB0 fc.lay 1) (chBits fc.lay 1) 0 (by simp [chBits, hl0])
      simp only [pow_zero, Nat.div_one, Nat.add_zero] at this
      rw [this]; simp [chB0, hl0, hlam5]
    have hK3 := KnownOK_append.mp hK2
    have e6 : lvlK fc.lay (chB0 fc.lay 1) = foldK fc.lay 64 := by simp [lvlK, chB0, hl0]
    rw [e6, hb1] at hK3
    refine ⟨t2, 9, ?_, ?_, hec2, hK3.1 (.x5, 0) (by simp [foldK, fk, gkOf, gkL, gkL0, baseK]), ?_⟩
    · have := hst.trans (hslot.steps.trans hst2)
      rw [hn1, hn2] at this; exact this
    · have hmid' : ¬ (lam - chB0 fc.lay (chOf fc.lay lam) + 1 < chBits fc.lay (chOf fc.lay lam)) := hmid
      unfold levelCost
      rw [if_neg (show ¬ (lam + 1 = heightL fc.lay) by omega), if_neg hmid', hlam5]; rfl
    · have hvA1 : fc.vA (lam + 1) = 0x360 + 16 * b' := fc.vA_zero hl0 (lam + 1)
      obtain ⟨h1, h2, h3⟩ := key t2 (fun A => (hmem2 A).trans (by rw [hslot.mem A]; rfl)) (fun x hx => (hkeep2 x hx).trans ((hslot.keep x hx).trans (hkeep' x hx))) (hglob2 _ _ (hslot.glob _ _ _ hglob))
        (hK3.1 (.x10, _) (by simp [foldK, fk])) (hK3.1 (.x11, _) (by simp [foldK, fk]))
        (by rw [hvA1]; exact hK3.2 _ (List.mem_singleton_self _)) hK3.1 (by
          rw [hpc2]
          unfold FCtx.X FCtx.kk FCtx.ci
          rw [hci1]
          simp [chB0, hl0, hlam5])
      exact ⟨h1, h2, h3⟩

theorem level_last (fc : FCtx) (hfc : fc.ok) (h0 : fc.lay = 0) (lam : Nat) (hlam : lam + 1 = fc.h)
    (hchk : ∀ ci, ci < nCh fc.lay → ∀ v, v < 2 ^ chBits fc.lay ci → blockCheck fc.lay ci v = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t, Steps image s 6 6 t ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = fc.hinput lam v ∧ FoldEnd fc s0 t := by
  have hl := hfc.2.2.2.2.2.2.2.2.2.2.1
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  have hdst : fc.dst = dstOf fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨hci, hsum, hkb, hle, -, -, -⟩ := chunk_facts fc.lay lam hl (by omega)
  have hc0 := hchk _ hci _ (blk_lt fc _)
  obtain ⟨hst, hec, hK', hkeep', hglob, hmem⟩ :=
    level_run fc hfc lam (by omega) (Or.inl h0) hc0 s0 v s hs
  set r := lvlExp fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam) with hr
  set b := bitOf fc.E lam with hbdef
  have hb2 := bitOf_lt fc.E lam
  have hlo := lo0_lt fc hfc
  have hl0 : lam ≠ 0 := by have := hfc.1; omega
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc, hFresh, -, hlink⟩ := hs
  have hvA := fc.vA_zero h0 lam
  rw [hvA] at hv0
  rw [hvA, show 0x360 + 16 * bitOf fc.E lam + 8 = 0x368 + 16 * bitOf fc.E lam by omega] at hv1
  have hsl := sib_words fc hfc lam (by omega) s hG hFresh
  have hsafe := hfc.2.2.2.2.2.2.2.2.1
  have hroot : chB0 fc.lay (fc.ci lam) + fc.kk lam + 1 = heightL fc.lay := by
    simp only [FCtx.kk, FCtx.ci] at hsum ⊢; rw [hsum]; omega
  have hn : r.steps = 6 ∧ r.cycles = 6 ∧ r.ecall = true ∧ r.spc = none ∧
      r.pc = pcOf (m4Pc fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam) + 8) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hr, lvlExp, if_pos hroot]
  obtain ⟨hn1, hn2, hn3, hn4, hn5⟩ := hn
  have hKp := hK'
  simp only [lvlPost, if_pos hroot, ← hdst] at hKp
  have hK2 := KnownOK_append.mp hKp
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x340 := hK2.1 (.x10, _) (by simp [foldK, fk])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK2.1 (.x11, _) (by simp [foldK, fk])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 fc.dst := hK2.2 _ (List.mem_singleton_self _)
  have hnb : (lvlNb fc.lay (fc.ci lam) (fc.blk (fc.ci lam)) (fc.kk lam)).eval s = BitVec.ofNat 64 1 := by
    simp only [lvlNb, if_pos hroot]; rfl
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x348 → A ≠ 0x370 - 16 * b + 8 → A ≠ 0x370 - 16 * b →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h3 h4 => level_frame hmem A hA (Or.inl hl0) h1 h3 h4
  have m1C8 : (r.toState s).getMem (BitVec.ofNat 64 0x348) = BitVec.ofNat 64 (fc.tau % 2 ^ 32 + 2 ^ 32 * 1) := by
    rw [hmem, lvlMem_1C8, hnb, stMerge_eval _ _ _ (by omega) hN8]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have msib0 : (r.toState s).getMem (BitVec.ofNat 64 (0x370 - 16 * b)) = vw0 (fc.sib lam) := by
    rw [hmem, (lvlMem_sib _ _ _ hb2 _ s).1]; exact hsl.1
  have msib1 : (r.toState s).getMem (BitVec.ofNat 64 (0x370 - 16 * b + 8)) = vw1 (fc.sib lam) := by
    rw [hmem, (lvlMem_sib _ _ _ hb2 _ s).2]; exact hsl.2
  have mv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x360 + 16 * b)) = vw0 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega)]; exact hv0
  have mv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x368 + 16 * b)) = vw1 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega)]; exact hv1
  refine ⟨r.toState s, ?_, hKp (.x5, 0) (by simp [foldK, fk, gkOf, gkL, gkL0, baseK]), ?_, ?_, ?_⟩
  · rw [hn1, hn2] at hst; exact hst
  · have hs' := hsafe
    simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq] at hs'
    exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0x340 0 h10 h11 (by decide) (by decide),
      pad64_hinput fc hfc lam (by omega) v hvl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    have hj : fc.E / 2 ^ (lam + 1) = 0 := Nat.div_eq_of_lt (by rw [hlam]; exact hfc.2.2.1)
    have hhi : twHi fc.tau (fc.heap lam) = fc.tau % 2 ^ 32 + 2 ^ 32 * 1 := by
      unfold twHi FCtx.heap; rw [hj, show fc.h - (lam + 1) = 0 by omega]; split <;> norm_num
    rw [hhi, mfr 0x340 (by omega) (by omega) (by omega) (by omega), hN0.2 hl0, m1C8,
      mfr 0x350 (by omega) (by omega) (by omega) (by omega),
      mfr 0x358 (by omega) (by omega) (by omega) (by omega), hP 0x350 (by decide),
      hP 0x358 (by decide)]
    rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
    · rw [h0] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
    · rw [h1] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
  · refine ⟨hglob, hKp, FrameOK.trans hF (fun r hr => hkeep' r hr) (fun A hA hA' => ?_), ?_,
      hec hn3, by rw [m1C8, BitVec.toNat_ofNat]; omega⟩
    · exact mfr A hA (by omega) (by omega) (by omega)
    · rw [PRes.toState_pc _ _ hn4, hn5]
      unfold FCtx.X
      rw [show fc.h - 1 = lam by omega]

/-! ## The whole fold -/

def FCtx.stepFn (fc : FCtx) : Val → Nat → OracleComp HashSpec Val := fun v lam =>
  let sib := fc.path.getD lam []
  let j := fc.E / 2 ^ (lam + 1)
  if fc.E / 2 ^ lam % 2 = 1 then hash16 (fc.node (lam + 1) j sib v)
  else hash16 (fc.node (lam + 1) j v sib)

theorem stepFn_eq (fc : FCtx) (lam : Nat) (hlam : lam < fc.h) (v : Val) :
    fc.stepFn v lam = hash16 (fc.input lam v) := by
  have : fc.path.getD lam [] = fc.sib lam := by
    simp [FCtx.path, FCtx.sib, List.getD_eq_getElem?_getD, List.getElem?_map, hlam]
  unfold FCtx.stepFn FCtx.input
  rw [this]
  split <;> rfl

theorem foldPath_eq (fc : FCtx) (v : Val) :
    foldPath fc.node fc.E v fc.path = (List.range' 0 fc.h).foldlM fc.stepFn v := by
  unfold foldPath
  rw [show fc.path.length = fc.h by simp [FCtx.path], List.range_eq_range']
  rfl

def foldCost (lay lam k : Nat) : Nat := ((List.range' lam k).map (levelCost lay)).sum

/-- The levels below `top` (under the top layer the fold stops under the root: `top = h - 1`). -/
theorem fold_steps (fc : FCtx) (hfc : fc.ok) (hn : NodeH fc)
    (hchk : ∀ ci, ci < nCh fc.lay → ∀ v, v < 2 ^ chBits fc.lay ci → blockCheck fc.lay ci v = true)
    (s0 : MachineState)
    (K : Val → OracleComp HashSpec Obs) (N C top : Nat) (htop : top < fc.h)
    (hK : ∀ v u, FoldInv fc s0 top v u → Good u N C (K v)) :
    ∀ k lam, lam + k = top → ∀ v s, FoldInv fc s0 lam v s →
      Good s (N + 20 * k) (C + foldCost fc.lay lam k)
        (cc ((List.range' lam k).foldlM fc.stepFn v) K) := by
  intro k
  induction k with
  | zero =>
    intro lam hk v s hs
    obtain rfl : lam = top := by omega
    simp only [List.range'_zero, List.foldlM_nil, cc_pure]
    exact (hK v s hs).mono (by omega) (by simp [foldCost])
  | succ k ih =>
    intro lam hk v s hs
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.1
    have hfm := fmt_input fc hfc hn lam (by omega) v hvl
    have hblk : (addrFmt (fc.input lam v)).blocks = 1 := by
      rw [hfm, pad64_hinput fc hfc lam (by omega) v hvl]; rfl
    rw [List.range'_succ, List.foldlM_cons, stepFn_eq fc lam (by omega), cc_bind]
    obtain ⟨t, n, hst, hn8, hf, h5, hv, hin, hpost⟩ := level_lt fc hfc lam (by omega) hchk s0 v s hs
    have h3 := Good.hash (K := fun v => cc ((List.range' (lam + 1) k).foldlM fc.stepFn v) K)
      hf h5 hv (hin.trans hfm.symm) (fun a => ih (lam + 1) (by omega) _ _ (hpost a))
    rw [hblk] at h3
    have hn20 : n ≤ 14 := by have := levelCost_le fc.lay lam; omega
    refine Good.steps' hst h3 (by omega) ?_
    simp only [foldCost, List.range'_succ, List.map_cons, List.sum_cons]
    omega

theorem fold_good (fc : FCtx) (hfc : fc.ok) (hn : NodeH fc) (h0 : fc.lay = 0)
    (hchk : ∀ ci, ci < nCh fc.lay → ∀ v, v < 2 ^ chBits fc.lay ci → blockCheck fc.lay ci v = true)
    (s0 : MachineState)
    (K : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ a u, FoldEnd fc s0 u → Good (writeHash u a) N C (K (answerBytes 16 a))) :
    ∀ k lam, lam + k = fc.h → 0 < k → ∀ v s, FoldInv fc s0 lam v s →
      Good s (N + 20 * k) (C + foldCost fc.lay lam k)
        (cc ((List.range' lam k).foldlM fc.stepFn v) K) := by
  have hh : fc.h = heightL fc.lay := hfc.2.2.2.2.2.2.2.2.2.2.2.1
  intro k
  induction k with
  | zero => intro lam _ h; omega
  | succ k ih =>
    intro lam hk _ v s hs
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.1
    have hfm := fmt_input fc hfc hn lam (by omega) v hvl
    have hblk : (addrFmt (fc.input lam v)).blocks = 1 := by
      rw [hfm, pad64_hinput fc hfc lam (by omega) v hvl]; rfl
    rw [List.range'_succ, List.foldlM_cons, stepFn_eq fc lam (by omega), cc_bind]
    by_cases hlast : lam + 1 = fc.h
    · obtain rfl : k = 0 := by omega
      obtain ⟨t, hst, h5, hv, hin, hend⟩ := level_last fc hfc h0 lam hlast hchk s0 v s hs
      simp only [List.range'_zero, List.foldlM_nil, cc_pure]
      have h3 := Good.hash (K := K) hend.2.2.2.2.1 h5 hv (hin.trans hfm.symm)
        (fun a => hK a t hend)
      rw [hblk] at h3
      refine Good.steps' hst h3 (by omega) ?_
      simp [foldCost, levelCost, ← hh, hlast]
    · obtain ⟨t, n, hst, hn8, hf, h5, hv, hin, hpost⟩ := level_lt fc hfc lam (by omega) hchk s0 v s hs
      have h3 := Good.hash (K := fun v => cc ((List.range' (lam + 1) k).foldlM fc.stepFn v) K)
        hf h5 hv (hin.trans hfm.symm) (fun a => ih (lam + 1) (by omega) (by omega) _ _ (hpost a))
      rw [hblk] at h3
      have hn20 : n ≤ 14 := by have := levelCost_le fc.lay lam; omega
      refine Good.steps' hst h3 (by omega) ?_
      simp only [foldCost, List.range'_succ, List.map_cons, List.sum_cons]
      omega

end SigGolfCandidate.Verify
