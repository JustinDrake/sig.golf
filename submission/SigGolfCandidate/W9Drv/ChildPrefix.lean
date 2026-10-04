import SigGolfCandidate.W9Machine.WctFetch
import SigGolfCandidate.W9Machine.WctChildContract
import SigGolfCandidate.T3M.Verify.Post
import SigGolfCandidate.W9Machine.WctJudg
import SigGolfCandidate.T3M.Verify.Common

section



namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def ChildGood : Prop := ∀ j : Fin 128, Child.Good Frozen.layout ⟨42, 99, 99⟩ j
def childBase (j : Nat) : Nat := 210432 + 64 * j
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def leafO : Nat := 880
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
def w0n (k index : Nat) : Nat := W9Machine.V3.nodeLow k index
def heapReg (h : Nat) : Reg :=
  match h with
  | 1 => .x9 | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def heapRegN (h : Nat) : Nat := [0,9,13,19,20,21,26,30].getD h 30
def encI (rd rs1 imm : Nat) : BitVec 32 := BitVec.ofNat 32 (imm % 4096 * 2 ^ 20 + rs1 * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
def encS (f3 rs2 off rs1 : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (off / 32 * 2 ^ 25 + rs2 * 2 ^ 20 + rs1 * 2 ^ 15 + f3 * 2 ^ 12 + off % 32 * 2 ^ 7 + 0x23)
def lvlTmpl (j l : Nat) : List (BitVec 32) :=
  [encI 10 8 (blkO l), encS 3 27 16 10] ++
    (if l ≤ 3 then [encI 3 0 (heapOf l j), encS 3 3 24 10]
     else [encS 3 (heapRegN (heapOf l j)) 24 10]) ++
    [if l = 5 then encI 12 9 (16 * bitAt j 6) else encI 12 8 (curO (l + 1) j), 0x00000073]
def encLoad (rd rs imm : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (imm * 2 ^ 20 + rs * 2 ^ 15 + 3 * 2 ^ 12 + rd * 2 ^ 7 + 3)
def childTmpl (j : Nat) : List (BitVec 32) :=
  [encI 12 8 (curO 0 j), 0x00000073, encI 11 0 64] ++ (List.range 6).flatMap (lvlTmpl j) ++
    [encLoad 3 8 (if bitAt j 6 = 0 then 48 else 0),
     encLoad 14 8 (if bitAt j 6 = 0 then 56 else 8),
     encS 3 3 (16 * (1 - bitAt j 6)) 9, encS 3 14 (16 * (1 - bitAt j 6) + 8) 9,
     0x00008067] ++ List.replicate 22 0x00000013
def childWords (j : Nat) : List (BitVec 32) := childTmpl j
def childLook (j n : Nat) : Option (BitVec 32) :=
  if childBase j ≤ n then (childWords j)[n - childBase j]? else none
def ecIdx (l : Nat) : Nat := [1,8,14,20,26,31,36].getD l 0
def lvlSt (l : Nat) : Nat := ecIdx (l + 1) - ecIdx l - 1
def childRun (j i : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 (childLook j) [] 64 (pcOf (childBase j + i)) dirs (σK []) []
def eX8 (off : Nat) : E := addC (.reg .x8) (BitVec.ofNat 64 off)
def aX8 (off : Nat) : Addr := ⟨some (.reg .x8), BitVec.ofNat 64 off⟩
def p0Res (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x12 (eX8 (curO 0 j)), [], []⟩, pcOf (childBase j + 1), true, 1, 1, [], none⟩
def lvlRegs (j l : Nat) : RegFile :=
  let rf := if l = 0 then RegFile.init.set .x11 (.c 64) else RegFile.init
  let rf := rf.set .x10 (eX8 (blkO l))
  let rf := if l ≤ 3 then rf.set .x3 (.c (BitVec.ofNat 64 (heapOf l j))) else rf
  rf.set .x12 (if l = 5 then addC (.reg .x9) (BitVec.ofNat 64 (16 * bitAt j 6)) else eX8 (curO (l + 1) j))
def hdr1E (j l : Nat) : E :=
  if l ≤ 3 then .c (BitVec.ofNat 64 (heapOf l j))
  else .reg (heapReg (heapOf l j))
def lvlMem (j l : Nat) : SymMem := [(aX8 (blkO l + 24), hdr1E j l), (aX8 (blkO l + 16), .reg .x27)]
def lvlObl (l : Nat) : List Oblig :=
  [.valid (aX8 (blkO l + 24)) 8, .valid (aX8 (blkO l + 16)) 8]
def lvlRes (j l : Nat) : PRes :=
  ⟨⟨lvlRegs j l, lvlMem j l, lvlObl l⟩, pcOf (childBase j + ecIdx (l + 1)), true, lvlSt l, lvlSt l, [], none⟩
def otherDest (j : Nat) : Nat := 16 * (1 - bitAt j 6)
def aX9 (off : Nat) : Addr := ⟨some (.reg .x9), BitVec.ofNat 64 off⟩
def retE : E := .bin .and (.reg .x1) (.c (~~~1#64))
def p7Res (j : Nat) : PRes :=
  ⟨⟨(RegFile.init.set .x3 (.ld (eX8 (sibO 6 j)))).set .x14 (.ld (eX8 (sibO 6 j + 8))),
    [(aX9 (otherDest j + 8), .ld (eX8 (sibO 6 j + 8))),
     (aX9 (otherDest j), .ld (eX8 (sibO 6 j)))],
    [.valid (aX9 (otherDest j + 8)) 8, .valid (aX9 (otherDest j)) 8,
     .valid (aX8 (sibO 6 j + 8)) 8, .valid (aX8 (sibO 6 j)) 8]⟩,
    0, false, 5, 5, [], some retE⟩
def childPiecesOK (j : Nat) : Bool :=
  optBeq (childRun j 0 []) (p0Res j) &&
    (List.range 6).all (fun l => optBeq (childRun j (ecIdx l + 1) []) (lvlRes j l)) &&
    optBeq (childRun j (ecIdx 6 + 1) [.jmp]) (p7Res j)
def childPiecesRange (lo n : Nat) : Bool := (List.range' lo n).all childPiecesOK
def childLinkedRange (lo n : Nat) : Bool :=
  (List.range' lo n).all (fun j => sliceChecked (childBase j) (childWords j))
end W9Drv.ChildProof
end

section

namespace W9Drv.ChildProof
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem childPieces_0 : childPiecesRange 0 16 = true := by decide +kernel
theorem childLinked_0 : childLinkedRange 0 16 = true := by decide +kernel
theorem childPieces_1 : childPiecesRange 16 16 = true := by decide +kernel
theorem childLinked_1 : childLinkedRange 16 16 = true := by decide +kernel
theorem childPieces_2 : childPiecesRange 32 16 = true := by decide +kernel
theorem childLinked_2 : childLinkedRange 32 16 = true := by decide +kernel
theorem childPieces_3 : childPiecesRange 48 16 = true := by decide +kernel
theorem childLinked_3 : childLinkedRange 48 16 = true := by decide +kernel
theorem childPieces_4 : childPiecesRange 64 16 = true := by decide +kernel
theorem childLinked_4 : childLinkedRange 64 16 = true := by decide +kernel
theorem childPieces_5 : childPiecesRange 80 16 = true := by decide +kernel
theorem childLinked_5 : childLinkedRange 80 16 = true := by decide +kernel
theorem childPieces_6 : childPiecesRange 96 16 = true := by decide +kernel
theorem childLinked_6 : childLinkedRange 96 16 = true := by decide +kernel
theorem childPieces_7 : childPiecesRange 112 16 = true := by decide +kernel
theorem childLinked_7 : childLinkedRange 112 16 = true := by decide +kernel
open SigGolfCandidate.T3M.Verify W9Machine
theorem childPiecesOK_at (j : Nat) (hj : j < 128) : childPiecesOK j = true := by
  have hall : ∀ lo n, childPiecesRange lo n = true → lo ≤ j → j < lo + n → childPiecesOK j = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 childPieces_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 childPieces_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 childPieces_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 childPieces_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 childPieces_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 childPieces_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 childPieces_6 (by omega) (by omega)
  exact hall 112 16 childPieces_7 (by omega) (by omega)
theorem childRun_p0 (j : Nat) (hj : j < 128) : childRun j 0 [] = some (p0Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem childRun_lvl (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6) :
    childRun j (ecIdx l + 1) [] = some (lvlRes j l) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq (List.all_eq_true.mp h.1.2 l (List.mem_range.mpr hl))
theorem childRun_p7 (j : Nat) (hj : j < 128) : childRun j (ecIdx 6 + 1) [.jmp] = some (p7Res j) := by
  have h := childPiecesOK_at j hj
  simp only [childPiecesOK, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem child_linked (j : Nat) (hj : j < 128) : sliceChecked (childBase j) (childWords j) = true := by
  have hall : ∀ lo n, childLinkedRange lo n = true → lo ≤ j → j < lo + n → sliceChecked (childBase j) (childWords j) = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact hall 0 16 childLinked_0 (by omega) (by omega)
  by_cases h1 : j < 32; · exact hall 16 16 childLinked_1 (by omega) (by omega)
  by_cases h2 : j < 48; · exact hall 32 16 childLinked_2 (by omega) (by omega)
  by_cases h3 : j < 64; · exact hall 48 16 childLinked_3 (by omega) (by omega)
  by_cases h4 : j < 80; · exact hall 64 16 childLinked_4 (by omega) (by omega)
  by_cases h5 : j < 96; · exact hall 80 16 childLinked_5 (by omega) (by omega)
  by_cases h6 : j < 112; · exact hall 96 16 childLinked_6 (by omega) (by omega)
  exact hall 112 16 childLinked_7 (by omega) (by omega)
end W9Drv.ChildProof
end

section



namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
def ChildCodeAt (im : Image) (j : Nat) : Prop :=
  ∀ i w, (childWords j)[i]? = some w → im.code[childBase j + i]? = some w
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def childWrites (j : Nat) : List Nat := (List.range 7).flatMap (stageW j)
structure ChildPre (j B k index : Nat) (leaf pads sibs : Nat → Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (childBase j)
  base8 : B % 8 = 0
  baseHi : B + 1024 ≤ MEMORY_BYTES
  t0 : u.getReg .x5 = 0
  s0 : u.getReg .x8 = BitVec.ofNat 64 B
  a0 : u.getReg .x10 = BitVec.ofNat 64 (B + leafO)
  a1 : u.getReg .x11 = BitVec.ofNat 64 128
  w0 : u.getReg .x27 = BitVec.ofNat 64 (w0n k index)
  s6 : u.getReg .x22 = BitVec.ofNat 64 index
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  leafAt : ∀ i, i < 8 → DigAt u (B + leafO + 16 * i) (leaf i)
  padAt : ∀ l, l < 6 → DigAt u (B + padO l) (pads l)
  sibAt : ∀ l, l < 6 → DigAt u (B + sibO l j) (sibs l)
theorem childLook_ok {im : Image} {j : Nat} (h : ChildCodeAt im j) : LookOK im (childLook j) := by
  intro n w hw
  unfold childLook at hw
  split at hw
  · rename_i hle
    have := h (n - childBase j) w hw
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem childRun_sound {im : Image} {j i : Nat} {dirs : List Dir} {r : PRes} (hcode : ChildCodeAt im j)
    (h : childRun j i dirs = some r) (s : MachineState) (hpc : s.pc = pcOf (childBase j + i))
    (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : r.brs = []) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h (childLook_ok hcode) s hpc (by intro p hp; cases hp) hobl
    (by rw [hbr]; intro b hb; cases hb)
theorem aX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (aX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  simp only [aX8, Addr.eval, E.eval, hB, ofNat_add_ofNat]
theorem eX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (eX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  rw [eX8, addC_eval]; simp only [E.eval, hB, ofNat_add_ofNat]
theorem valid_aX8 {s : MachineState} {B off w : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hal : (B + off) % w = 0) (hhi : B + off + w ≤ MEMORY_BYTES) : (Oblig.valid (aX8 off) w).holds s := by
  simp only [Oblig.holds, aX8_eval hB, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]
  exact ⟨hhi, hal⟩
theorem lvlObl_holds {s : MachineState} {B : Nat} (l : Nat) (hl : l ≤ 6)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0) (hhi : B + 1024 ≤ MEMORY_BYTES) :
    ∀ o ∈ lvlObl l, o.holds s := by
  have hb : blkO l % 64 = 0 ∧ blkO l ≤ 384 := by unfold blkO; omega
  intro o ho
  simp only [lvlObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact valid_aX8 hB (by omega) (by omega)
theorem lvlRegs_x12 (j l : Nat) (hl : l < 5) : (lvlRegs j l).get .x12 = eX8 (curO (l + 1) j) := by
  unfold lvlRegs; rw [RegFile.get_set_self _ _ (by decide), if_neg (by omega)]
theorem lvlRegs_x10 (j l : Nat) : (lvlRegs j l).get .x10 = eX8 (blkO l) := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x11 (j l : Nat) : (lvlRegs j l).get .x11 = if l = 0 then .c 64 else .reg .x11 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x3 (j l : Nat) :
    (lvlRegs j l).get .x3 = if l ≤ 3 then .c (BitVec.ofNat 64 (heapOf l j)) else .reg .x3 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_other (j l : Nat) (r : Reg) (h3 : r ≠ .x3) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h12 : r ≠ .x12) : (lvlRegs j l).get r = RegFile.init.get r := by
  unfold lvlRegs
  simp only
  split_ifs <;> simp only [RegFile.get_set_ne _ _ h3, RegFile.get_set_ne _ _ h10, RegFile.get_set_ne _ _ h11,
    RegFile.get_set_ne _ _ h12]
theorem heapReg_ne (h : Nat) : heapReg h ≠ .x3 ∧ heapReg h ≠ .x10 ∧ heapReg h ≠ .x11 ∧ heapReg h ≠ .x12 := by
  unfold heapReg; split <;> decide
theorem lvlMem_get {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B)
    (hb : B + 1024 < 2 ^ 64) (j l A : Nat) (hl : l ≤ 6) (hA : A < 2 ^ 64) :
    memEval s (lvlMem j l) (BitVec.ofNat 64 A) =
      if A = B + blkO l + 24 then (hdr1E j l).eval s
      else if A = B + blkO l + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) := by
  have hbl : blkO l ≤ 384 := by unfold blkO; omega
  unfold lvlMem
  rw [memEval_cons, memEval_cons, memEval_nil, aX8_eval hB, aX8_eval hB]
  simp only [← Nat.add_assoc, E.eval]
  simp only [ofNat_inj hA (show B + blkO l + 24 < 2 ^ 64 by omega),
    ofNat_inj hA (show B + blkO l + 16 < 2 ^ 64 by omega)]
theorem hdr1E_eval {s : MachineState} {j l : Nat} (hj : j < 128) (hl : l ≤ 5)
    (hheap : ∀ h, 2 ≤ h → h ≤ 7 → s.getReg (heapReg h) = BitVec.ofNat 64 h) :
    (hdr1E j l).eval s = BitVec.ofNat 64 (heapOf l j) := by
  unfold hdr1E
  split_ifs with h3
  · rfl
  · have hb : 2 ≤ heapOf l j ∧ heapOf l j ≤ 7 := by
      unfold heapOf
      have : l = 4 ∨ l = 5 := by omega
      rcases this with rfl | rfl <;> simp <;> omega
    exact hheap _ hb.1 hb.2
theorem frame_writeHash4 (t : MachineState) (a : BitVec 256) (d : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64) :
    Frame t (writeHash t a) (fun A => A = d ∨ A = d + 8 ∨ A = d + 16 ∨ A = d + 24) := by
  intro A hA hn
  simp only [not_or] at hn
  rw [getMem_writeHash t a d A h12 hd hA, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2.1, if_neg hn.2.2.2]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
theorem childWrites_eq (j : Nat) : childWrites j = stagesW j 7 := rfl
theorem mem_stagesW {j m n off : Nat} (hm : m < n) (h : off ∈ stageW j m) : off ∈ stagesW j n :=
  List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, h⟩
theorem bitAt_lt (j l : Nat) : bitAt j l < 2 := Nat.mod_lt _ (by decide)
theorem stagesW_free {j l off : Nat} (hl : l < 6) (h : off ∈ stagesW j (l + 1)) :
    off ≠ padO l ∧ off ≠ padO l + 8 ∧ off ≠ sibO l j ∧ off ≠ sibO l j + 8 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hbl := bitAt_lt j l
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold padO sibO
  by_cases hml : m = l
  · subst hml
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have : m < l := by omega
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem childWrites_free {j off : Nat} (h : off ∈ childWrites j) :
    off ≠ padO 6 ∧ off ≠ padO 6 + 8 ∧ off ≠ sibO 6 j ∧ off ≠ sibO 6 j + 8 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hb6 := bitAt_lt j 6
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold padO sibO
  by_cases hml : m = 6
  · subst hml
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · have : m < 6 := by omega
    unfold curO at ho; unfold blkO at ho ⊢
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem childWrites_bound {j off : Nat} (h : off ∈ childWrites j) : off % 8 = 0 ∧ off + 8 ≤ 464 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold curO at ho; unfold blkO at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
end W9Drv.ChildProof
end

section

namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
def nodeHeader (k index heap : Nat) : Digest :=
  BitVec.ofNat 64 heap ++ BitVec.ofNat 64 (w0n k index)
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevelP (k index j : Nat) (pads sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  shortHash (blk4 pair.1 (nodeHeader k index (heapOf l j)) (pads l) pair.2)
structure Mid (j B k index : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (childBase j + ecIdx l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  x3 : 4 ≤ l → s.getReg .x3 = BitVec.ofNat 64 (heapOf 3 j)
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + curO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)
def nodeIn (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) : List UInt8 :=
  let pair := if bitAt j l = 0 then (v, sibs l) else (sibs l, v)
  blk4 pair.1 (nodeHeader k index (heapOf l j)) (pads l) pair.2
theorem childLevelP_eq (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) :
    childLevelP k index j pads sibs v l = shortHash (nodeIn k index j pads sibs v l) := rfl
theorem nodeIn_blocks (k index j : Nat) (pads sibs : Nat → Digest) (v : Digest) (l : Nat) :
    (toQ (pad64 (nodeIn k index j pads sibs v l))).blocks = 1 := by
  unfold nodeIn; exact blocks_blk4 _ _ _ _
theorem hdr11_lo (k index heap : Nat) :
    (nodeHeader k index heap).extractLsb' 0 64 = BitVec.ofNat 64 (w0n k index) := by
  exact BitVec.extractLsb'_append_eq_right
theorem hdr11_hi (k index heap : Nat) :
    (nodeHeader k index heap).extractLsb' 64 64 = BitVec.ofNat 64 heap := by
  exact BitVec.extractLsb'_append_eq_left
theorem DigAt.of_eq {X Y : MachineState} {a : Nat} {d : Digest} (h : DigAt X a d)
    (h0 : Y.getMem (BitVec.ofNat 64 a) = X.getMem (BitVec.ofNat 64 a))
    (h1 : Y.getMem (BitVec.ofNat 64 (a + 8)) = X.getMem (BitVec.ofNat 64 (a + 8))) : DigAt Y a d :=
  ⟨h0.trans h.1, h1.trans h.2⟩
theorem hashInput_blk4 (t : MachineState) (A : Nat) (a b c d : Digest)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (hA : A % 8 = 0)
    (hA' : A + 64 < 2 ^ 64) (ha : DigAt t A a) (hb : DigAt t (A + 16) b) (hc : DigAt t (A + 32) c)
    (hd : DigAt t (A + 48) d) : hashInput t = toQ (pad64 (blk4 a b c d)) := by
  rw [pad64_blk4]
  apply hashInput_words8 t _ A (blk4_length _ _ _ _) h10 hA hA' h11
  rw [wordsOf_blk4, ha.1, ha.2, hb.1, hc.1, hd.1, show A + 24 = A + 16 + 8 by omega, hb.2,
    show A + 40 = A + 32 + 8 by omega, hc.2, show A + 56 = A + 48 + 8 by omega, hd.2]
theorem stagesW_mono {j n n' off : Nat} (h : off ∈ stagesW j n) (hn : n ≤ n') : off ∈ stagesW j n' := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  exact mem_stagesW (by have := List.mem_range.mp hm; omega) ho
theorem lvl_step {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u) (l : Nat) (hl : l < 5) (v : Digest) (s : MachineState)
    (hs : Mid j B k index u l v s) :
    ∃ t, Steps im s (lvlSt l) (lvlSt l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads sibs v l)) ∧
      ∀ a : BitVec 256, Mid j B k index u (l + 1) (a.extractLsb' 0 128) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (childBase j + (ecIdx l + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_lvl j hj l (by omega)) s hpc
    (lvlObl_holds l (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) rfl
  have hreg : ∀ x, ((lvlRes j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((lvlRes j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO l + 24 then (hdr1E j l).eval s
      else if A = B + blkO l + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j l A (by omega) hA)
  generalize ht : (lvlRes j l).toState s = t at hst hec hreg hmem
  have hbl : blkO l + 64 ≤ 384 + 64 := by unfold blkO; omega
  have hb := bitAt_lt j l
  have hb1 := bitAt_lt j (l + 1)
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, lvlRegs_x11]
    split_ifs with h0
    · rfl
    · exact hs.a1 h0
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO (l + 1) j) := by
    rw [hreg, lvlRegs_x12 j l hl, eX8_eval hx8]
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have hcur : curO (l + 1) j % 8 = 0 ∧ curO (l + 1) j + 32 ≤ 464 := by
    unfold curO blkO; omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO l) 64 (B + curO (l + 1) j) h10 h11 h12 (by unfold blkO; omega) (by decide)
      (by omega) (by omega) (by omega)
  have tS : ∀ o, o ≤ 1024 → o ≠ blkO l + 16 → o ≠ blkO l + 24 →
      t.getMem (BitVec.ofNat 64 (B + o)) = s.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho h16 h24
    rw [hmem _ (by omega), if_neg (by omega), if_neg (by omega)]
  have sU : ∀ o, o ≤ 1024 → o ∉ stagesW j (l + 1) →
      s.getMem (BitVec.ofNat 64 (B + o)) = u.getMem (BitVec.ofNat 64 (B + o)) := by
    intro o ho hn
    refine hs.frame (B + o) (by omega) ?_
    rintro ⟨off, hoff, he⟩
    have : off = o := by omega
    subst this; exact hn hoff
  have hpad : DigAt t (B + blkO l + 32) (pads l) := by
    have hP := hu.padAt l (by omega)
    unfold padO at hP
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) (by omega : l < 6) h
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO l + 32) + 8 = B + (blkO l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l (by omega)
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) (by omega : l < 6) h
    have hsb : sibO l j + 8 ≤ 1024 ∧ (sibO l j = blkO l ∨ sibO l j = blkO l + 48) := by
      unfold sibO blkO; omega
    refine DigAt.of_eq hS ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.1 rfl)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).2.2.2 rfl)]
  have hnode : DigAt t (B + curO l j) v := by
    have hcb : curO l j + 8 ≤ 1024 ∧ (curO l j = blkO l ∨ curO l j = blkO l + 48) := by
      unfold curO blkO; omega
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega)]
    · rw [Nat.add_assoc, tS _ (by omega) (by omega) (by omega)]
  have hhdr : DigAt t (B + blkO l + 16) (nodeHeader k index (heapOf l j)) := by
    constructor
    · rw [hmem _ (by omega), if_neg (by omega), if_pos rfl, hdr11_lo,
        hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
    · rw [show B + blkO l + 16 + 8 = B + blkO l + 24 by omega, hmem _ (by omega), if_pos rfl, hdr11_hi]
      apply hdr1E_eval hj (by omega)
      intro h h1 h7
      obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h
      rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7
  have hin : hashInput t = toQ (pad64 (nodeIn k index j pads sibs v l)) := by
    unfold nodeIn
    rcases Nat.lt_or_ge (bitAt j l) 1 with h0 | h1
    · have e0 : bitAt j l = 0 := by omega
      have ec : curO l j = blkO l := by unfold curO; omega
      have es : sibO l j = blkO l + 48 := by unfold sibO; omega
      simp only [e0, if_true]
      rw [ec] at hnode; rw [es, ← Nat.add_assoc] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by unfold blkO; omega) (by omega) hnode hhdr hpad hsib
    · have e1 : bitAt j l = 1 := by omega
      have ec : curO l j = blkO l + 48 := by unfold curO; omega
      have es : sibO l j = blkO l := by unfold sibO; omega
      simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [ec, ← Nat.add_assoc] at hnode; rw [es] at hsib
      exact hashInput_blk4 t _ _ _ _ _ h10 h11 (by unfold blkO; omega) (by omega) hsib hhdr hpad hnode
  refine ⟨t, hst, hec rfl, h5, hv, hin, fun a => ?_⟩
  have hpcT : t.pc = pcOf (childBase j + ecIdx (l + 1)) := by
    rw [← ht, PRes.toState_pc (lvlRes j l) s rfl]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · intro h4
    rw [writeHash_getReg, hreg, lvlRegs_x3]
    split_ifs with hl3
    · have : l = 3 := by omega
      subst this; rfl
    · exact hs.x3 (by omega)
  · intro _; rw [writeHash_getReg]; exact h11
  · rw [writeHash_getReg]; exact h12
  · exact DigAt.writeHash_lo t a _ h12 (by omega)
  · have hP : Frame s t (fun A => A = B + blkO l + 24 ∨ A = B + blkO l + 16) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    have hW := frame_writeHash4 t a (B + curO (l + 1) j) h12 (by omega)
    refine ((hs.frame.trans hP).trans hW).mono ?_
    intro A _ hA
    rcases hA with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | (rfl | rfl | rfl | rfl)
    · exact ⟨off, stagesW_mono hoff (by omega), rfl⟩
    · exact ⟨blkO l + 24, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨blkO l + 16, mem_stagesW (m := l) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), rfl⟩
    · exact ⟨curO (l + 1) j + 8, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 16, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨curO (l + 1) j + 24, mem_stagesW (m := l + 1) (by omega) (by simp [stageW]), by omega⟩
def fuelR : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => lvlSt l + 1 + fuelR (l + 1) n
def cycR : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => lvlSt l + 8 + cycR (l + 1) n
theorem fuelR_05 : fuelR 0 5 = 30 := rfl
theorem cycR_05 : cycR 0 5 = 65 := rfl
theorem child_rest {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u) (K : Digest → OracleComp HashSpec Obs) (N C A : Nat) (Q : Prop)
    (hK : ∀ v t, Mid j B k index u 5 v t → GoodQFor im t N C Q A (K v)) :
    ∀ n l v s, l + n = 5 → Mid j B k index u l v s →
      GoodQFor im s (N + fuelR l n) (C + cycR l n) Q (A + cycR l n)
        (ccM ((List.range' l n).foldlM (childLevelP k index j pads sibs) v) K) := by
  intro n
  induction n with
  | zero =>
    intro l v s hln hs
    have hl5 : l = 5 := by omega
    subst l
    simpa only [List.range'_zero, List.foldlM_nil, ccM_pure, fuelR, cycR, Nat.add_zero] using hK v s hs
  | succ m ih =>
    intro l v s hln hs
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_step hj hcode hidx hu l (by omega) v s hs
    rw [List.range'_succ, List.foldlM_cons, childLevelP_eq]
    have H : ∀ a : BitVec 256, GoodQFor im (writeHash t a) (N + fuelR (l + 1) m) (C + cycR (l + 1) m) Q
        (A + cycR (l + 1) m)
        (ccM ((fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads sibs) v')
          (a.extractLsb' 0 128)) K) :=
      fun a => ih (l + 1) _ _ (by omega) (hpost a)
    have hg := GoodQFor.shortHash_bind
      (f := fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads sibs) v') hf h5 hv hin H
    rw [nodeIn_blocks] at hg
    simp only [fuelR, cycR]
    exact GoodQFor.steps' hst hg (by omega) (by omega) (fun q => ⟨q, by omega⟩)
theorem leafBytes_length (leaf : Nat → Digest) : (leafBytes leaf).length = 128 := by
  simp [leafBytes, List.length_flatMap, bytesLE_length]
theorem leaf_blocks (leaf : Nat → Digest) : (toQ (pad64 (leafBytes leaf))).blocks = 2 := by
  rw [pad64_of_aligned _ (by rw [leafBytes_length]), blocks_toQ (by rw [Aligned, leafBytes_length]; omega),
    leafBytes_length]
theorem child_prefix_good (im : Image) (j : Nat) (hj : j < 128) (hcode : ChildCodeAt im j)
    (B k index : Nat) (leaf pads sibs : Nat → Digest) (u : MachineState)
    (N C A : Nat) (Q : Prop) (K : Digest → OracleComp HashSpec Obs) (hidx : index < 2 ^ 32)
    (hu : ChildPre j B k index leaf pads sibs u)
    (hK : ∀ v t, Mid j B k index u 5 v t → GoodQFor im t N C Q A (K v)) :
    GoodQFor im u (N + 32) (C + 82) Q (A + 82)
      (ccM (shortHash (leafBytes leaf) >>= fun v => (List.range 5).foldlM (childLevelP k index j pads sibs) v) K) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  obtain ⟨hst, hec⟩ := childRun_sound hcode (childRun_p0 j hj) u (by rw [hu.pc, Nat.add_zero]) (by intro o ho; cases ho) rfl
  have hreg : ∀ x, ((p0Res j).toState u).getReg x =
      ((RegFile.init.set .x12 (eX8 (curO 0 j))).get x).eval u := fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, ((p0Res j).toState u).getMem A = u.getMem A :=
    fun A => (PRes.toState_getMem _ _ _).trans (memEval_nil _ _)
  have hpcT : ((p0Res j).toState u).pc = pcOf (childBase j + 1) := PRes.toState_pc (p0Res j) u rfl
  generalize ht : (p0Res j).toState u = t at hst hec hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h12; rw [hreg, RegFile.get_set_ne _ _ h12, RegFile.init_get_eval]
  have hb0 := bitAt_lt j 0
  have hc0 : curO 0 j % 8 = 0 ∧ curO 0 j + 32 ≤ 464 := by unfold curO blkO; omega
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + leafO) := (hother .x10 (by decide)).trans hu.a0
  have h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := (hother .x11 (by decide)).trans hu.a1
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO 0 j) := by
    rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval hu.s0]
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide)).trans hu.t0
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + leafO) 128 (B + curO 0 j) h10 h11 h12 (by unfold leafO; omega) (by decide)
      (by unfold leafO; omega) (by omega) (by omega)
  have hin : hashInput t = toQ (pad64 (leafBytes leaf)) := by
    rw [pad64_of_aligned _ (by rw [leafBytes_length])]
    apply hashInput_toQ t _ 1 (B + leafO) (leafBytes_length leaf) h10 (by unfold leafO; omega)
      (by unfold leafO; omega) h11 (by norm_num)
    have hD : DigsAt t (B + leafO) ((List.range 8).map leaf) := by
      intro i hi
      simp only [List.length_map, List.length_range] at hi
      have e : ((List.range 8).map leaf).getD i 0 = leaf i := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
      rw [e]
      exact DigAt.of_eq (hu.leafAt i hi) (hmem _) (hmem _)
    have hw := hD.words
    simp only [List.length_map, List.length_range] at hw
    rw [hw]
    rfl
  have H : ∀ a : BitVec 256, GoodQFor im (writeHash t a) (N + fuelR 0 5) (C + cycR 0 5) Q (A + cycR 0 5)
      (ccM ((fun v => (List.range 5).foldlM (childLevelP k index j pads sibs) v) (a.extractLsb' 0 128)) K) := by
    intro a
    have hmid : Mid j B k index u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, fun h => absurd h (by decide), fun h => absurd rfl h, ?_, ?_, ?_⟩
      · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]; rfl
      · intro r _ _ _ h12'; rw [writeHash_getReg]; exact hother r h12'
      · rw [writeHash_getReg]; exact h12
      · exact DigAt.writeHash_lo t a _ h12 (by omega)
      · have hT : Frame u t (fun _ => False) := fun A _ _ => hmem _
        refine (hT.trans (frame_writeHash4 t a (B + curO 0 j) h12 (by omega))).mono ?_
        intro A _ hA
        rcases hA with h | (rfl | rfl | rfl | rfl)
        · exact absurd h id
        · exact ⟨curO 0 j, mem_stagesW (m := 0) (by omega) (by simp [stageW]), rfl⟩
        · exact ⟨curO 0 j + 8, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 16, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
        · exact ⟨curO 0 j + 24, mem_stagesW (m := 0) (by omega) (by simp [stageW]), by omega⟩
    show GoodQFor im (writeHash t a) (N + fuelR 0 5) (C + cycR 0 5) Q (A + cycR 0 5)
      (ccM ((List.range 5).foldlM (childLevelP k index j pads sibs) (a.extractLsb' 0 128)) K)
    rw [List.range_eq_range']
    exact child_rest hj hcode hidx hu K N C A Q hK 5 0 _ _ rfl hmid
  have hg := GoodQFor.shortHash_bind
    (f := fun v => (List.range 5).foldlM (childLevelP k index j pads sibs) v) (hec rfl) h5 hv hin H
  rw [leaf_blocks, fuelR_05, cycR_05] at hg
  exact GoodQFor.steps' hst hg (by simp only [p0Res]; omega) (by simp only [p0Res]; omega)
    (fun q => ⟨q, by simp only [p0Res]; omega⟩)
end W9Drv.ChildProof
end
