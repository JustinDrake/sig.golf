import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.DrvBits
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildDefs
import SigGolfCandidate.T3M.Verify.Post
import SigGolfCandidate.T3M.Verify.Common
import SigGolfCandidate.T3M.Expand.Basic

section



namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Merkle (bitAt blkO curO sibO heapOf heapReg)
def cbE (j : Nat) : Nat := cb0 + 64 * j
def ecIdx (l : Nat) : Nat := [1,8,14,20,26,31,36].getD l 0
def lvlSt (l : Nat) : Nat := ecIdx (l + 1) - ecIdx l - 1
def childRunE (j i : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 expLook [] 64 (pcOf (cbE j + i)) dirs (σK []) []
def eX8 (off : Nat) : E := addC (.reg .x8) (BitVec.ofNat 64 off)
def aX8 (off : Nat) : Addr := ⟨some (.reg .x8), BitVec.ofNat 64 off⟩
def eX9 (off : Nat) : E := addC (.reg .x9) (BitVec.ofNat 64 off)
def aX9 (off : Nat) : Addr := ⟨some (.reg .x9), BitVec.ofNat 64 off⟩
def p0E (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x12 (eX8 (curO 0 j)), [], []⟩, pcOf (cbE j + 1), true, 1, 1, [], none⟩
def a2E (j l : Nat) : E := if l < 5 then eX8 (curO (l + 1) j) else eX9 (16 * bitAt j 6)
def lvlRegs (j l : Nat) : RegFile :=
  let rf := if l = 0 then RegFile.init.set .x11 (.c 64) else RegFile.init
  let rf := rf.set .x10 (eX8 (blkO l))
  let rf := if l ≤ 3 then rf.set .x3 (.c (BitVec.ofNat 64 (heapOf l j))) else rf
  rf.set .x12 (a2E j l)
def hdr1E (j l : Nat) : E :=
  if l ≤ 3 then .c (BitVec.ofNat 64 (heapOf l j)) else .reg (heapReg (heapOf l j))
def lvlMem (j l : Nat) : SymMem := [(aX8 (blkO l + 24), hdr1E j l), (aX8 (blkO l + 16), .reg .x27)]
def lvlObl (l : Nat) : List Oblig := [.valid (aX8 (blkO l + 24)) 8, .valid (aX8 (blkO l + 16)) 8]
def lvlE (j l : Nat) : PRes :=
  ⟨⟨lvlRegs j l, lvlMem j l, lvlObl l⟩, pcOf (cbE j + ecIdx (l + 1)), true, lvlSt l, lvlSt l, [], none⟩
def retE : E := .bin .and (.reg .x1) (.c (~~~1#64))
def sibSrc (j : Nat) : Nat := if bitAt j 6 = 0 then 48 else 0
def sibDst (j : Nat) : Nat := if bitAt j 6 = 0 then 16 else 0
def p7E (j : Nat) : PRes :=
  ⟨⟨(RegFile.init.set .x3 (.ld (eX8 (sibSrc j)))).set .x14 (.ld (eX8 (sibSrc j + 8))),
    [(aX9 (sibDst j + 8), .ld (eX8 (sibSrc j + 8))), (aX9 (sibDst j), .ld (eX8 (sibSrc j)))],
    [.valid (aX9 (sibDst j + 8)) 8, .valid (aX9 (sibDst j)) 8, .valid (aX8 (sibSrc j + 8)) 8,
      .valid (aX8 (sibSrc j)) 8]⟩, 0, false, 5, 5, [], some retE⟩
def childOKE (j : Nat) : Bool :=
  optBeq (childRunE j 0 []) (p0E j) &&
    (List.range 6).all (fun l => optBeq (childRunE j (ecIdx l + 1) []) (lvlE j l)) &&
    optBeq (childRunE j (ecIdx 6 + 1) [.jmp]) (p7E j)
end ClaudeWCT.W9.Machine.Expand
end

section

namespace ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 100000
theorem childOKE_0 : (List.range' 0 16).all childOKE = true := by decide +kernel
theorem childOKE_16 : (List.range' 16 16).all childOKE = true := by decide +kernel
theorem childOKE_32 : (List.range' 32 16).all childOKE = true := by decide +kernel
theorem childOKE_48 : (List.range' 48 16).all childOKE = true := by decide +kernel
theorem childOKE_64 : (List.range' 64 16).all childOKE = true := by decide +kernel
theorem childOKE_80 : (List.range' 80 16).all childOKE = true := by decide +kernel
theorem childOKE_96 : (List.range' 96 16).all childOKE = true := by decide +kernel
theorem childOKE_112 : (List.range' 112 16).all childOKE = true := by decide +kernel
theorem childOKE_all (j : Nat) (hj : j < 128) : childOKE j = true := by
  have key : ∀ lo n, (List.range' lo n).all childOKE = true → lo ≤ j → j < lo + n → childOKE j = true :=
    fun lo n h h1 h2 => List.all_eq_true.mp h j (List.mem_range'_1.mpr ⟨h1, h2⟩)
  by_cases h0 : j < 16; · exact key 0 16 childOKE_0 (by omega) h0
  by_cases h16 : j < 32; · exact key 16 16 childOKE_16 (by omega) h16
  by_cases h32 : j < 48; · exact key 32 16 childOKE_32 (by omega) h32
  by_cases h48 : j < 64; · exact key 48 16 childOKE_48 (by omega) h48
  by_cases h64 : j < 80; · exact key 64 16 childOKE_64 (by omega) h64
  by_cases h80 : j < 96; · exact key 80 16 childOKE_80 (by omega) h80
  by_cases h96 : j < 112; · exact key 96 16 childOKE_96 (by omega) h96
  exact key 112 16 childOKE_112 (by omega) (by omega)
end ClaudeWCT.W9.Machine.Expand
end

section



namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Merkle
set_option linter.unusedSimpArgs false
theorem childOKE_p0 (j : Nat) (hj : j < 128) : childRunE j 0 [] = some (p0E j) := by
  have h := childOKE_all j hj
  simp only [childOKE, Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem childRunE_lvl (j : Nat) (hj : j < 128) (l : Nat) (hl : l < 6) :
    childRunE j (ecIdx l + 1) [] = some (lvlE j l) := by
  have h := childOKE_all j hj
  simp only [childOKE, Bool.and_eq_true] at h
  exact optBeq_eq (List.all_eq_true.mp h.1.2 l (List.mem_range.mpr hl))
theorem childRunE_p7 (j : Nat) (hj : j < 128) : childRunE j (ecIdx 6 + 1) [.jmp] = some (p7E j) := by
  have h := childOKE_all j hj
  simp only [childOKE, Bool.and_eq_true] at h
  exact optBeq_eq h.2
theorem aX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (aX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  simp only [aX8, Addr.eval, E.eval, hB, ofNat_add_ofNat]
theorem eX8_eval {s : MachineState} {B : Nat} (hB : s.getReg .x8 = BitVec.ofNat 64 B) (off : Nat) :
    (eX8 off).eval s = BitVec.ofNat 64 (B + off) := by
  rw [eX8, addC_eval]; simp only [E.eval, hB, ofNat_add_ofNat]
theorem aX9_eval {s : MachineState} {P : Nat} (hP : s.getReg .x9 = BitVec.ofNat 64 P) (off : Nat) :
    (aX9 off).eval s = BitVec.ofNat 64 (P + off) := by
  simp only [aX9, Addr.eval, E.eval, hP, ofNat_add_ofNat]
theorem eX9_eval {s : MachineState} {P : Nat} (hP : s.getReg .x9 = BitVec.ofNat 64 P) (off : Nat) :
    (eX9 off).eval s = BitVec.ofNat 64 (P + off) := by
  rw [eX9, addC_eval]; simp only [E.eval, hP, ofNat_add_ofNat]
theorem valid_ofNatA {s : MachineState} {a : Addr} {A w : Nat} (ha : a.eval s = BitVec.ofNat 64 A)
    (hal : A % w = 0) (hhi : A + w ≤ MEMORY_BYTES) : (Oblig.valid a w).holds s := by
  simp only [Oblig.holds, ha, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]
  exact ⟨hhi, hal⟩
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
theorem frame_writeHash4 (t : MachineState) (a : BitVec 256) (d : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 d) (hd : d + 32 < 2 ^ 64) :
    Frame t (writeHash t a) (fun A => A = d ∨ A = d + 8 ∨ A = d + 16 ∨ A = d + 24) := by
  intro A hA hn
  simp only [not_or] at hn
  rw [getMem_writeHash t a d A h12 hd hA, if_neg hn.1, if_neg hn.2.1, if_neg hn.2.2.1, if_neg hn.2.2.2]
theorem bitAt_lt (j l : Nat) : bitAt j l < 2 := Nat.mod_lt _ (by decide)
theorem mem_stagesW {j m n off : Nat} (hm : m < n) (h : off ∈ stageW j m) : off ∈ stagesW j n :=
  List.mem_flatMap.mpr ⟨m, List.mem_range.mpr hm, h⟩
theorem stagesW_mono {j n n' off : Nat} (h : off ∈ stagesW j n) (hn : n ≤ n') : off ∈ stagesW j n' := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  exact mem_stagesW (by have := List.mem_range.mp hm; omega) ho
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
theorem childWrites_sib6 {j off : Nat} (h : off ∈ childWrites j) : off ≠ sibO 6 j ∧ off ≠ sibO 6 j + 8 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hb6 := bitAt_lt j 6
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold sibO
  unfold curO at ho; unfold blkO at ho ⊢
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem childWrites_bound {j off : Nat} (h : off ∈ childWrites j) : off % 8 = 0 ∧ off + 8 ≤ 464 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hbm := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold curO at ho; unfold blkO at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem hdr0_nodeLo (k index : Nat) (hk : k < 252) (hidx : index < 2 ^ 32) :
    hdr0 3 (4 + k) index index = nodeLo k index := by
  simp only [hdr0, nodeLo]
  rw [Nat.div_eq_of_lt hidx, Nat.mod_eq_of_lt hidx]
  omega
theorem nodeHdr_lo (k index heap : Nat) (hk : k < 252) (hidx : index < 2 ^ 32) :
    (ClaudeWCT.WCT9.wctNodeHeader k index heap).extractLsb' 0 64 = BitVec.ofNat 64 (nodeLo k index) := by
  unfold ClaudeWCT.WCT9.wctNodeHeader ClaudeWCT.WCT9.nodeLayer
  rw [header_packed_lo_3, hdr0_nodeLo k index hk hidx]
theorem nodeHdr_hi (k index heap : Nat) (hh : heap < 2 ^ 32) :
    (ClaudeWCT.WCT9.wctNodeHeader k index heap).extractLsb' 64 64 = BitVec.ofNat 64 heap := by
  unfold ClaudeWCT.WCT9.wctNodeHeader ClaudeWCT.WCT9.nodeLayer
  rw [header_packed_hi_3]
  congr 1
  unfold hdr1; rw [Nat.mod_eq_of_lt hh]; simp
def nodeInC (k index j : Nat) (sibs : Nat → Digest) (v : Digest) (l : Nat) : List UInt8 :=
  let pair := if bitAt j l = 0 then (v, sibs l) else (sibs l, v)
  blk4 pair.1 (ClaudeWCT.WCT9.wctNodeHeader k index (heapOf l j)) 0 pair.2
theorem childLevel_eq (k index j : Nat) (sibs : Nat → Digest) (v : Digest) (l : Nat) :
    childLevel k index j sibs v l = shortHash (nodeInC k index j sibs v l) := by
  unfold childLevel nodeInC ClaudeWCT.WCT9.wctNodeHash SigGolfCandidate.T3.nodeHash
    ClaudeWCT.WCT9.wctNodeHeader blk4
  rw [bytesLE16_zero]
theorem nodeInC_blocks (k index j : Nat) (sibs : Nat → Digest) (v : Digest) (l : Nat) :
    (toQ (pad64 (nodeInC k index j sibs v l))).blocks = 1 := by
  unfold nodeInC; exact blocks_blk4 _ _ _ _
theorem leafBytes_length (leaf : Nat → Digest) : (Merkle.leafBytes leaf).length = 128 := by
  simp [Merkle.leafBytes, List.length_flatMap, bytesLE_length]
theorem leaf_blocks (leaf : Nat → Digest) : (toQ (pad64 (Merkle.leafBytes leaf))).blocks = 2 := by
  rw [pad64_of_aligned _ (by rw [leafBytes_length]), blocks_toQ (by rw [Aligned, leafBytes_length]; omega),
    leafBytes_length]
theorem lvlObl_holds {s : MachineState} {B : Nat} (l : Nat) (hl : l ≤ 6)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (h8 : B % 8 = 0) (hhi : B + 1024 ≤ MEMORY_BYTES) :
    ∀ o ∈ lvlObl l, o.holds s := by
  have hb : blkO l % 64 = 0 ∧ blkO l ≤ 384 := by unfold blkO; omega
  intro o ho
  simp only [lvlObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact valid_ofNatA (aX8_eval hB _) (by omega) (by omega)
  · exact valid_ofNatA (aX8_eval hB _) (by omega) (by omega)
theorem lvlRegs_x12 (j l : Nat) : (lvlRegs j l).get .x12 = a2E j l := by
  unfold lvlRegs; exact RegFile.get_set_self _ _ (by decide)
theorem lvlRegs_x10 (j l : Nat) : (lvlRegs j l).get .x10 = eX8 (blkO l) := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_x11 (j l : Nat) : (lvlRegs j l).get .x11 = if l = 0 then .c 64 else .reg .x11 := by
  unfold lvlRegs; simp only; split_ifs <;> rfl
theorem lvlRegs_other (j l : Nat) (r : Reg) (h3 : r ≠ .x3) (h10 : r ≠ .x10) (h11 : r ≠ .x11)
    (h12 : r ≠ .x12) : (lvlRegs j l).get r = RegFile.init.get r := by
  unfold lvlRegs
  simp only
  split_ifs <;> simp only [RegFile.get_set_ne _ _ h3, RegFile.get_set_ne _ _ h10, RegFile.get_set_ne _ _ h11,
    RegFile.get_set_ne _ _ h12]
theorem heapReg_ne (h : Nat) : heapReg h ≠ .x3 ∧ heapReg h ≠ .x10 ∧ heapReg h ≠ .x11 ∧ heapReg h ≠ .x12 ∧
    heapReg h ≠ .x14 := by
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
theorem heapOf_le (j l : Nat) (hj : j < 128) (hl : l < 6) : heapOf l j < 128 := by
  unfold heapOf
  interval_cases l <;> simp <;> omega
theorem hdr1E_eval {s : MachineState} {j l : Nat} (hj : j < 128) (hl : l < 6)
    (hheap : ∀ h, 2 ≤ h → h ≤ 7 → s.getReg (heapReg h) = BitVec.ofNat 64 h) :
    (hdr1E j l).eval s = BitVec.ofNat 64 (heapOf l j) := by
  unfold hdr1E
  split_ifs with h3
  · rfl
  · have hb : 2 ≤ heapOf l j ∧ heapOf l j ≤ 7 := by
      unfold heapOf
      have : l = 4 ∨ l = 5 := by omega
      rcases this with rfl | rfl <;> simp <;> omega
    simp only [E.eval]
    exact hheap _ hb.1 hb.2
structure ChildPreE (j B k index P : Nat) (leaf sibs : Nat → Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (cbE j)
  base8 : B % 8 = 0
  baseHi : B + 1024 ≤ MEMORY_BYTES
  p16 : P % 16 = 0
  sep : P + 48 ≤ B
  hk : k < 252
  hidx : index < 2 ^ 32
  t0 : u.getReg .x5 = 0
  s0 : u.getReg .x8 = BitVec.ofNat 64 B
  a0 : u.getReg .x10 = BitVec.ofNat 64 (B + leafO)
  a1 : u.getReg .x11 = BitVec.ofNat 64 128
  w0 : u.getReg .x27 = BitVec.ofNat 64 (nodeLo k index)
  heaps : ∀ h, 2 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 h
  x9 : u.getReg .x9 = BitVec.ofNat 64 P
  leafAt : ∀ i, i < 8 → DigAt u (B + leafO + 16 * i) (leaf i)
  padAt : ∀ l, l < 6 → DigAt u (B + padO l) 0
  sibAt : ∀ l, l < 7 → DigAt u (B + sibO l j) (sibs l)
structure MidE (j B : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (cbE j + ecIdx l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + curO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)
structure TopE (j B P : Nat) (u : MachineState) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (cbE j + ecIdx 6 + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  a1 : s.getReg .x11 = BitVec.ofNat 64 64
  node : DigAt s (P + 16 * bitAt j 6) v
  frame : Frame u s (fun A => (∃ off ∈ childWrites j, A = B + off) ∨
    (P + 16 * bitAt j 6 ≤ A ∧ A < P + 16 * bitAt j 6 + 32))
structure ChildPostE (j B P : Nat) (u : MachineState) (pr : Digest × Digest) (t : MachineState) : Prop where
  pc : t.pc = u.getReg .x1 &&& ~~~1#64
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → t.getReg r = u.getReg r
  a1 : t.getReg .x11 = BitVec.ofNat 64 64
  pair : DigAt t P pr.1 ∧ DigAt t (P + 16) pr.2
  frame : Frame u t (fun A => (∃ off ∈ childWrites j, A = B + off) ∨ (P ≤ A ∧ A < P + 48))
theorem lvl_piece {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) (l : Nat) (hl : l < 6) (v : Digest) (s : MachineState)
    (hs : MidE j B u l v s) :
    ∃ t, Steps im s (lvlSt l) (lvlSt l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      t.getReg .x10 = BitVec.ofNat 64 (B + blkO l) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = (a2E j l).eval s ∧ t.pc = pcOf (cbE j + ecIdx (l + 1)) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      hashInput t = toQ (pad64 (nodeInC k index j sibs v l)) ∧
      Frame s t (fun A => A = B + blkO l + 24 ∨ A = B + blkO l + 16) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (cbE j + (ecIdx l + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, hec⟩ := expRun_sound hcode (childRunE_lvl j hj l hl) s hpc
    (lvlObl_holds l (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) (fun b hb => by cases hb)
  have hreg : ∀ x, ((lvlE j l).toState s).getReg x = ((lvlRegs j l).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((lvlE j l).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO l + 24 then (hdr1E j l).eval s
      else if A = B + blkO l + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j l A (by omega) hA)
  have hpcT : ((lvlE j l).toState s).pc = pcOf (cbE j + ecIdx (l + 1)) := PRes.toState_pc (lvlE j l) s rfl
  generalize ht : (lvlE j l).toState s = t at hst hec hreg hmem hpcT
  have hbl : blkO l + 64 ≤ 384 + 64 := by unfold blkO; omega
  have hb := bitAt_lt j l
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, lvlRegs_x11]
    split_ifs with h0
    · rfl
    · exact hs.a1 h0
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
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
  have hpad : DigAt t (B + blkO l + 32) 0 := by
    have hP := hu.padAt l hl
    unfold padO at hP
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hl h
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO l + 32) + 8 = B + (blkO l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l (by omega)
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hl h
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
  have hheap := heapOf_le j l hj hl
  have hhdr : DigAt t (B + blkO l + 16) (ClaudeWCT.WCT9.wctNodeHeader k index (heapOf l j)) := by
    constructor
    · rw [hmem _ (by omega), if_neg (by omega), if_pos rfl, nodeHdr_lo k index _ hu.hk hu.hidx,
        hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
    · rw [show B + blkO l + 16 + 8 = B + blkO l + 24 by omega, hmem _ (by omega), if_pos rfl,
        nodeHdr_hi k index _ (by omega)]
      apply hdr1E_eval hj hl
      intro h h1 h7
      obtain ⟨n3, n10, n11, n12, -⟩ := heapReg_ne h
      rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7
  have hin : hashInput t = toQ (pad64 (nodeInC k index j sibs v l)) := by
    unfold nodeInC
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
  refine ⟨t, hst, hec rfl, h5, h10, h11, by rw [hreg, lvlRegs_x12], hpcT, hother, hin, ?_⟩
  intro A hA hn
  simp only [not_or] at hn
  rw [hmem A hA, if_neg hn.1, if_neg hn.2]
theorem lvl_stepE {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) (l : Nat) (hl : l < 5) (v : Digest) (s : MachineState)
    (hs : MidE j B u l v s) :
    ∃ t, Steps im s (lvlSt l) (lvlSt l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeInC k index j sibs v l)) ∧
      ∀ a : BitVec 256, MidE j B u (l + 1) (a.extractLsb' 0 128) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, hin, hP⟩ := lvl_piece hj hcode hu l (by omega) v s hs
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B :=
    (hs.keep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (B + curO (l + 1) j) := by
    rw [h12']; unfold a2E; rw [if_pos hl, eX8_eval hx8]
  have hb1 := bitAt_lt j (l + 1)
  have hcur : curO (l + 1) j % 8 = 0 ∧ curO (l + 1) j + 32 ≤ 464 := by unfold curO blkO; omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO l) 64 (B + curO (l + 1) j) h10 h11 h12 (by unfold blkO; omega) (by decide)
      (by unfold blkO; omega) (by omega) (by omega)
  refine ⟨t, hst, hec, h5, hv, hin, fun a => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · intro _; rw [writeHash_getReg]; exact h11
  · rw [writeHash_getReg]; exact h12
  · exact DigAt.writeHash_lo t a _ h12 (by omega)
  · have hW := frame_writeHash4 t a (B + curO (l + 1) j) h12 (by omega)
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
theorem lvl5_stepE {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) (v : Digest) (s : MachineState) (hs : MidE j B u 5 v s) :
    ∃ t, Steps im s (lvlSt 5) (lvlSt 5) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeInC k index j sibs v 5)) ∧
      ∀ a : BitVec 256, TopE j B P u (a.extractLsb' 0 128) (writeHash t a) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  have hsep := hu.sep
  have hp16 := hu.p16
  unfold MEMORY_BYTES at hhi
  obtain ⟨t, hst, hec, h5, h10, h11, h12', hpcT, hother, hin, hP⟩ := lvl_piece hj hcode hu 5 (by omega) v s hs
  have hx9 : s.getReg .x9 = BitVec.ofNat 64 P :=
    (hs.keep .x9 (by decide) (by decide) (by decide) (by decide)).trans hu.x9
  have hb6 := bitAt_lt j 6
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (P + 16 * bitAt j 6) := by
    rw [h12']; unfold a2E; rw [if_neg (by omega), eX9_eval hx9]
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO 5) 64 (P + 16 * bitAt j 6) h10 h11 h12 (by unfold blkO; omega) (by decide)
      (by unfold blkO; omega) (by omega) (by omega)
  refine ⟨t, hst, hec, h5, hv, hin, fun a => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [writeHash_pc, hpcT, SigGolfCandidate.T3M.pcOf_add4]
  · intro r h3 h10' h11' h12'; rw [writeHash_getReg]; exact hother r h3 h10' h11' h12'
  · rw [writeHash_getReg]; exact h11
  · exact DigAt.writeHash_lo t a _ h12 (by omega)
  · have hW := frame_writeHash4 t a (P + 16 * bitAt j 6) h12 (by omega)
    refine ((hs.frame.trans hP).trans hW).mono ?_
    intro A _ hA
    rcases hA with (⟨off, hoff, rfl⟩ | (rfl | rfl)) | (rfl | rfl | rfl | rfl)
    · exact Or.inl ⟨off, hoff, rfl⟩
    · exact Or.inl ⟨blkO 5 + 24, mem_stagesW (m := 5) (by omega) (by simp [stageW]), by omega⟩
    · exact Or.inl ⟨blkO 5 + 16, mem_stagesW (m := 5) (by omega) (by simp [stageW]), by omega⟩
    · exact Or.inr ⟨le_refl _, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
theorem p7_stepE {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) (v : Digest) (s : MachineState) (hs : TopE j B P u v s) :
    ∃ t, Steps im s 5 5 t ∧ ChildPostE j B P u (pairOf j v (sibs 6)) t := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  have hsep := hu.sep
  have hp16 := hu.p16
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hx9 : s.getReg .x9 = BitVec.ofNat 64 P := (hkeep .x9 (by decide) (by decide) (by decide) (by decide)).trans hu.x9
  have hb6 := bitAt_lt j 6
  have hsrc : sibSrc j = sibO 6 j ∧ sibSrc j + 8 ≤ 64 ∧ sibSrc j % 16 = 0 := by
    unfold sibSrc sibO blkO; split_ifs <;> omega
  have hdst : sibDst j + 16 * bitAt j 6 = 16 ∧ sibDst j % 16 = 0 ∧ sibDst j ≤ 16 := by
    unfold sibDst; split_ifs <;> omega
  have hpc : s.pc = pcOf (cbE j + (ecIdx 6 + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, -⟩ := expRun_sound hcode (childRunE_p7 j hj) s hpc (by
      intro o ho
      simp only [p7E, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl | rfl
      · exact valid_ofNatA (aX9_eval hx9 _) (by omega) (by unfold MEMORY_BYTES; omega)
      · exact valid_ofNatA (aX9_eval hx9 _) (by omega) (by unfold MEMORY_BYTES; omega)
      · exact valid_ofNatA (aX8_eval hx8 _) (by omega) (by unfold MEMORY_BYTES; omega)
      · exact valid_ofNatA (aX8_eval hx8 _) (by omega) (by unfold MEMORY_BYTES; omega))
    (fun b hb => by cases hb)
  have hreg : ∀ x, ((p7E j).toState s).getReg x =
      (((RegFile.init.set .x3 (.ld (eX8 (sibSrc j)))).set .x14 (.ld (eX8 (sibSrc j + 8)))).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((p7E j).toState s).getMem (BitVec.ofNat 64 A) =
      if A = P + (sibDst j + 8) then s.getMem (BitVec.ofNat 64 (B + (sibSrc j + 8)))
      else if A = P + sibDst j then s.getMem (BitVec.ofNat 64 (B + sibSrc j)) else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [PRes.toState_getMem]
    simp only [p7E]
    rw [memEval_cons, memEval_cons, memEval_nil, aX9_eval hx9, aX9_eval hx9]
    simp only [E.eval, eX8_eval hx8]
    simp only [ofNat_inj hA (show P + (sibDst j + 8) < 2 ^ 64 by omega),
      ofNat_inj hA (show P + sibDst j < 2 ^ 64 by omega)]
  have hpcT : ((p7E j).toState s).pc = s.getReg .x1 &&& ~~~1#64 := rfl
  generalize ht : (p7E j).toState s = t at hst hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x14 → t.getReg r = s.getReg r := by
    intro r h3 h14; rw [hreg, RegFile.get_set_ne _ _ h14, RegFile.get_set_ne _ _ h3, RegFile.init_get_eval]
  have hsib : DigAt s (B + sibSrc j) (sibs 6) := by
    have hS := hu.sibAt 6 (by decide)
    rw [← hsrc.1] at hS
    have hf : ∀ o, o = sibSrc j ∨ o = sibSrc j + 8 → s.getMem (BitVec.ofNat 64 (B + o)) =
        u.getMem (BitVec.ofNat 64 (B + o)) := by
      intro o ho
      refine hs.frame (B + o) (by omega) ?_
      rintro (⟨off, hoff, he⟩ | ⟨h1, h2⟩)
      · have := childWrites_sib6 hoff; rw [hsrc.1] at ho; omega
      · omega
    refine DigAt.of_eq hS (hf _ (Or.inl rfl)) ?_
    rw [Nat.add_assoc]; exact hf _ (Or.inr rfl)
  refine ⟨t, hst, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcT, hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
  · intro r h3 h10 h11 h12 h14; rw [hother r h3 h14]; exact hkeep r h3 h10 h11 h12
  · rw [hother .x11 (by decide) (by decide)]; exact hs.a1
  ·
    have hcopy : DigAt t (P + sibDst j) (sibs 6) := by
      constructor
      · rw [hmem _ (by omega), if_neg (by omega), if_pos rfl]; exact hsib.1
      · rw [show P + sibDst j + 8 = P + (sibDst j + 8) by omega, hmem _ (by omega), if_pos rfl,
          ← Nat.add_assoc]; exact hsib.2
    have hnode : DigAt t (P + 16 * bitAt j 6) v := by
      refine DigAt.of_eq hs.node ?_ ?_
      · rw [hmem _ (by omega), if_neg (by omega), if_neg (by omega)]
      · rw [hmem _ (by omega), if_neg (by omega), if_neg (by omega)]
    unfold pairOf
    rcases Nat.lt_or_ge (bitAt j 6) 1 with h0 | h1
    · have e0 : bitAt j 6 = 0 := by omega
      have ed : sibDst j = 16 := by unfold sibDst; rw [if_pos e0]
      simp only [e0, if_true]
      rw [e0, Nat.mul_zero, Nat.add_zero] at hnode
      rw [ed] at hcopy
      exact ⟨hnode, hcopy⟩
    · have e1 : bitAt j 6 = 1 := by omega
      have ed : sibDst j = 0 := by unfold sibDst; rw [if_neg (by omega)]
      simp only [e1, show (1 : Nat) ≠ 0 by decide, if_false]
      rw [e1, Nat.mul_one] at hnode
      rw [ed, Nat.add_zero] at hcopy
      exact ⟨hcopy, hnode⟩
  · have hP : Frame s t (fun A => A = P + (sibDst j + 8) ∨ A = P + sibDst j) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    refine (hs.frame.trans hP).mono ?_
    intro A _ hA
    rcases hA with (h | ⟨h1, h2⟩) | (rfl | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, by omega⟩
def cycL : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => lvlSt l + 8 + cycL (l + 1) n
theorem cycL_05 : cycL 0 5 = 65 := rfl
theorem child_levelsE {im : Image} {sk : BitVec 256} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) :
    ∀ n l v s, l + n = 5 → MidE j B u l v s →
      TBSim im sk s (cycL l n) ((List.range' l n).foldlM (childLevel k index j sibs) v) (MidE j B u 5) := by
  intro n
  induction n with
  | zero =>
    intro l v s hln hs
    have hl5 : l = 5 := by omega
    subst hl5
    simp only [List.range'_zero, List.foldlM_nil, cycL]
    exact TBSim.pure hs
  | succ m ih =>
    intro l v s hln hs
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_stepE hj hcode hu l (by omega) v s hs
    rw [List.range'_succ, List.foldlM_cons, childLevel_eq]
    have hg := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk)
      (f := fun v' => (List.range' (l + 1) m).foldlM (childLevel k index j sibs) v') hf h5 hv hin
      (fun a => ih (l + 1) _ _ (by omega) (hpost a))
    rw [nodeInC_blocks] at hg
    simp only [cycL]
    exact (TBSim.steps hst hg).mono (by omega) (fun _ _ h => h)
theorem range6_split {α : Type} (f : α → Nat → M α) (v : α) :
    (List.range 6).foldlM f v = ((List.range' 0 5).foldlM f v >>= fun w => f w 5) := by
  rw [show List.range 6 = List.range' 0 5 ++ [5] from rfl, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
theorem child_tbE {im : Image} {sk : BitVec 256} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index P : Nat} {leaf sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPreE j B k index P leaf sibs u) :
    TBSim im sk u 99 (childProgC k index j leaf sibs) (ChildPostE j B P u) := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  obtain ⟨hst, hec⟩ := expRun_sound hcode (childOKE_p0 j hj) u (by rw [hu.pc]; rfl)
    (by intro o ho; cases ho) (fun b hb => by cases hb)
  have hreg : ∀ x, ((p0E j).toState u).getReg x =
      ((RegFile.init.set .x12 (eX8 (curO 0 j))).get x).eval u := fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, ((p0E j).toState u).getMem A = u.getMem A :=
    fun A => (PRes.toState_getMem _ _ _).trans (memEval_nil _ _)
  have hpcT : ((p0E j).toState u).pc = pcOf (cbE j + 1) := PRes.toState_pc (p0E j) u rfl
  generalize ht : (p0E j).toState u = t at hst hec hreg hmem hpcT
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
  have hin : hashInput t = toQ (pad64 (Merkle.leafBytes leaf)) := by
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
  have H : ∀ a : BitVec 256, TBSim im sk (writeHash t a) (cycL 0 5 + (lvlSt 5 + 8 + 5))
      ((fun v => (List.range 6).foldlM (childLevel k index j sibs) v >>= fun top => pure (pairOf j top (sibs 6)))
        (a.extractLsb' 0 128)) (ChildPostE j B P u) := by
    intro a
    have hmid : MidE j B u 0 (a.extractLsb' 0 128) (writeHash t a) := by
      refine ⟨?_, ?_, fun h => absurd rfl h, ?_, ?_, ?_⟩
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
    show TBSim im sk (writeHash t a) (cycL 0 5 + (lvlSt 5 + 8 + 5))
      ((List.range 6).foldlM (childLevel k index j sibs) (a.extractLsb' 0 128) >>= fun top =>
        pure (pairOf j top (sibs 6))) (ChildPostE j B P u)
    rw [range6_split, bind_assoc]
    refine TBSim.bind (child_levelsE hj hcode hu 5 0 _ _ rfl hmid) (fun w s5 h5' => ?_)
    obtain ⟨t6, hst6, hf6, h56, hv6, hin6, hpost6⟩ := lvl5_stepE hj hcode hu w s5 h5'
    rw [childLevel_eq]
    have hg := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk) (W := 5)
      (f := fun top => pure (pairOf j top (sibs 6))) hf6 h56 hv6 hin6 (fun a6 => by
        obtain ⟨t7, hst7, hpost7⟩ := p7_stepE hj hcode hu _ (writeHash t6 a6) (hpost6 a6)
        exact (TBSim.steps hst7 (TBSim.pure hpost7)).mono (by omega) (fun _ _ h => h))
    rw [nodeInC_blocks] at hg
    exact (TBSim.steps hst6 hg).mono (by omega) (fun _ _ h => h)
  have hg := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk)
    (f := fun v => (List.range 6).foldlM (childLevel k index j sibs) v >>= fun top => pure (pairOf j top (sibs 6)))
    (hec rfl) h5 hv hin H
  rw [leaf_blocks, cycL_05] at hg
  unfold childProgC
  exact (TBSim.steps hst hg).mono (by simp only [p0E, lvlSt, ecIdx]; norm_num) (fun _ _ h => h)
end ClaudeWCT.W9.Machine.Expand
end
