import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineData
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Merkle.ChildMain

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Merkle (curO blkO lvlRegs lvlMem lvlObl retE eX8 ecIdx lvlSt)
def cbE (j : Nat) : Nat := cb0 + 64 * j
def childRunE (j i : Nat) (dirs : List Dir) : Option PRes :=
  pathAux cfg0 expLook [] 64 (pcOf (cbE j + i)) dirs (σK []) []
def p0E (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x12 (eX8 (curO 0 j)), [], []⟩, pcOf (cbE j + 1), true, 1, 1, [], none⟩
def lvlE (j l : Nat) : PRes :=
  ⟨⟨lvlRegs j l, lvlMem j l, lvlObl l⟩, pcOf (cbE j + ecIdx (l + 1)), true, lvlSt l, lvlSt l, [], none⟩
def p7E (j : Nat) : PRes :=
  ⟨⟨RegFile.init.set .x10 (eX8 (blkO 6)), lvlMem j 6, lvlObl 6⟩, 0, false, 4, 4, [], some retE⟩
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
structure ChildPreE (j B k index : Nat) (leaf pads sibs : Nat → Digest) (u : MachineState) : Prop where
  pc : u.pc = pcOf (cbE j)
  base8 : B % 8 = 0
  baseHi : B + 1024 ≤ MEMORY_BYTES
  t0 : u.getReg .x5 = 0
  s0 : u.getReg .x8 = BitVec.ofNat 64 B
  a0 : u.getReg .x10 = BitVec.ofNat 64 (B + leafO)
  a1 : u.getReg .x11 = BitVec.ofNat 64 128
  w0 : u.getReg .x27 = BitVec.ofNat 64 (w0n k index)
  s6 : u.getReg .x22 = BitVec.ofNat 64 index
  heaps : ∀ h, 1 ≤ h → h ≤ 7 → u.getReg (heapReg h) = BitVec.ofNat 64 (index + 2 ^ 32 * h)
  leafAt : ∀ i, i < 8 → DigAt u (B + leafO + 16 * i) (leaf i)
  padAt : ∀ l, l < 6 → DigAt u (B + padO l) (pads l)
  sibAt : ∀ l, l < 6 → DigAt u (B + sibO l j) (sibs l)
structure MidE (j B k index : Nat) (u : MachineState) (l : Nat) (v : Digest) (s : MachineState) : Prop where
  pc : s.pc = pcOf (cbE j + ecIdx l + 1)
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r
  x3 : 4 ≤ l → s.getReg .x3 = BitVec.ofNat 64 (heapOf 3 j)
  a1 : l ≠ 0 → s.getReg .x11 = BitVec.ofNat 64 64
  a2 : s.getReg .x12 = BitVec.ofNat 64 (B + curO l j)
  node : DigAt s (B + curO l j) v
  frame : Frame u s (fun A => ∃ off ∈ stagesW j (l + 1), A = B + off)
theorem lvl_stepE {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPreE j B k index leaf pads sibs u) (l : Nat) (hl : l < 6) (v : Digest) (s : MachineState)
    (hs : MidE j B k index u l v s) :
    ∃ t, Steps im s (lvlSt l) (lvlSt l) t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads sibs v l)) ∧
      ∀ a : BitVec 256, MidE j B k index u (l + 1) (a.extractLsb' 0 128) (writeHash t a) := by
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
  generalize ht : (lvlE j l).toState s = t at hst hec hreg hmem
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
    rw [hreg, lvlRegs_x12, eX8_eval hx8]
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
    have hP := hu.padAt l hl
    unfold padO at hP
    have hf := fun off (h : off ∈ stagesW j (l + 1)) => stagesW_free (off := off) hl h
    rw [Nat.add_assoc]
    refine DigAt.of_eq hP ?_ ?_
    · rw [tS _ (by omega) (by omega) (by omega), sU _ (by omega) (fun h => (hf _ h).1 (by unfold padO; rfl))]
    · rw [show B + (blkO l + 32) + 8 = B + (blkO l + 40) by omega, tS _ (by omega) (by omega) (by omega),
        sU _ (by omega) (fun h => (hf _ h).2.1 (by unfold padO; omega))]
  have hsib : DigAt t (B + sibO l j) (sibs l) := by
    have hS := hu.sibAt l hl
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
  have hhdr : DigAt t (B + blkO l + 16) (header 11 k index 0 (heapOf l j)) := by
    constructor
    · rw [hmem _ (by omega), if_neg (by omega), if_pos rfl, hdr11_lo,
        hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
    · rw [show B + blkO l + 16 + 8 = B + blkO l + 24 by omega, hmem _ (by omega), if_pos rfl, hdr11_hi]
      apply hdr1E_eval hj (by omega) hidx
      · rw [hkeep .x22 (by decide) (by decide) (by decide) (by decide)]; exact hu.s6
      · intro h h1 h7
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
  have hpcT : t.pc = pcOf (cbE j + ecIdx (l + 1)) := by
    rw [← ht, PRes.toState_pc (lvlE j l) s rfl]; rfl
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
theorem p7_stepE {im : Image} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPreE j B k index leaf pads sibs u) (v : Digest) (s : MachineState)
    (hs : MidE j B k index u 6 v s) :
    ∃ t, Steps im s 4 4 t ∧ ChildPost j B k index u v t := by
  have h8 := hu.base8
  have hhi := hu.baseHi
  unfold MEMORY_BYTES at hhi
  have hkeep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → s.getReg r = u.getReg r := hs.keep
  have hx8 : s.getReg .x8 = BitVec.ofNat 64 B := (hkeep .x8 (by decide) (by decide) (by decide) (by decide)).trans hu.s0
  have hpc : s.pc = pcOf (cbE j + (ecIdx 6 + 1)) := by rw [hs.pc, Nat.add_assoc]
  obtain ⟨hst, -⟩ := expRun_sound hcode (childRunE_p7 j hj) s hpc
    (lvlObl_holds 6 (by omega) hx8 h8 (by unfold MEMORY_BYTES; omega)) (fun b hb => by cases hb)
  have hreg : ∀ x, ((p7E j).toState s).getReg x = ((RegFile.init.set .x10 (eX8 (blkO 6))).get x).eval s :=
    fun x => PRes.toState_getReg _ _ _
  have hmem : ∀ A, A < 2 ^ 64 → ((p7E j).toState s).getMem (BitVec.ofNat 64 A) =
      if A = B + blkO 6 + 24 then (hdr1E j 6).eval s
      else if A = B + blkO 6 + 16 then s.getReg .x27 else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (PRes.toState_getMem _ _ _).trans (lvlMem_get hx8 (by omega) j 6 A (by omega) hA)
  have hpcT : ((p7E j).toState s).pc = s.getReg .x1 &&& ~~~1#64 := rfl
  generalize ht : (p7E j).toState s = t at hst hreg hmem hpcT
  have hother : ∀ r : Reg, r ≠ .x10 → t.getReg r = s.getReg r := by
    intro r h10; rw [hreg, RegFile.get_set_ne _ _ h10, RegFile.init_get_eval]
  have hb6 := bitAt_lt j 6
  have hblk6 : blkO 6 = 0 := rfl
  have hheap6 : heapOf 6 j = 1 := by
    unfold heapOf
    rw [show 2 ^ (6 + 1) = 128 by rfl, Nat.div_eq_of_lt hj]; rfl
  refine ⟨t, hst, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpcT, hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
  · intro r h3 h10 h11 h12; rw [hother r h10]; exact hkeep r h3 h10 h11 h12
  · rw [hother .x3 (by decide)]; exact hs.x3 (by omega)
  · rw [hreg, RegFile.get_set_self _ _ (by decide), eX8_eval hx8, hblk6, Nat.add_zero]
  · rw [hother .x11 (by decide)]; exact hs.a1 (by omega)
  · rw [hother .x12 (by decide)]; exact hs.a2
  · have hc : curO 6 j = 0 ∨ curO 6 j = 48 := by unfold curO blkO; omega
    refine DigAt.of_eq hs.node ?_ ?_
    · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_neg (by rw [hblk6]; omega)]
    · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_neg (by rw [hblk6]; omega)]
  · rw [hmem _ (by omega), if_neg (by rw [hblk6]; omega), if_pos (by rw [hblk6]),
      hkeep .x27 (by decide) (by decide) (by decide) (by decide), hu.w0]
  · rw [hmem _ (by omega), if_pos (by rw [hblk6])]
    rw [← hheap6]
    apply hdr1E_eval hj (by omega) hidx
    · rw [hkeep .x22 (by decide) (by decide) (by decide) (by decide)]; exact hu.s6
    · intro h h1 h7
      obtain ⟨n3, n10, n11, n12⟩ := heapReg_ne h
      rw [hkeep _ n3 n10 n11 n12]; exact hu.heaps h h1 h7
  · have hP : Frame s t (fun A => A = B + blkO 6 + 24 ∨ A = B + blkO 6 + 16) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    refine (hs.frame.trans hP).mono ?_
    intro A _ hA
    rw [childWrites_eq]
    rcases hA with ⟨off, hoff, rfl⟩ | (rfl | rfl)
    · exact ⟨off, hoff, rfl⟩
    · exact ⟨blkO 6 + 24, mem_stagesW (m := 6) (by omega) (by simp [stageW]), by omega⟩
    · exact ⟨blkO 6 + 16, mem_stagesW (m := 6) (by omega) (by simp [stageW]), by omega⟩
theorem child_restE {im : Image} {sk : BitVec 256} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPreE j B k index leaf pads sibs u) :
    ∀ n l v s, l + n = 6 → MidE j B k index u l v s →
      TBSim im sk s (cycR l n) ((List.range' l n).foldlM (childLevelP k index j pads sibs) v)
        (ChildPost j B k index u) := by
  intro n
  induction n with
  | zero =>
    intro l v s hln hs
    have hl6 : l = 6 := by omega
    subst hl6
    obtain ⟨t, hst, hpost⟩ := p7_stepE hj hcode hidx hu v s hs
    simp only [List.range'_zero, List.foldlM_nil, cycR]
    exact (TBSim.steps hst (TBSim.pure hpost)).mono (by omega) (fun _ _ h => h)
  | succ m ih =>
    intro l v s hln hs
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := lvl_stepE hj hcode hidx hu l (by omega) v s hs
    rw [List.range'_succ, List.foldlM_cons, childLevelP_eq]
    have hg := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk)
      (f := fun v' => (List.range' (l + 1) m).foldlM (childLevelP k index j pads sibs) v') hf h5 hv hin
      (fun a => ih (l + 1) _ _ (by omega) (hpost a))
    rw [nodeIn_blocks] at hg
    simp only [cycR]
    exact (TBSim.steps hst hg).mono (by omega) (fun _ _ h => h)
theorem child_tbE {im : Image} {sk : BitVec 256} {j : Nat} (hj : j < 128) (hcode : NewCodeAt im)
    {B k index : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState} (hidx : index < 2 ^ 32)
    (hu : ChildPreE j B k index leaf pads sibs u) :
    TBSim im sk u 102 (childProg k index j leaf pads sibs) (ChildPost j B k index u) := by
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
  have H : ∀ a : BitVec 256, TBSim im sk (writeHash t a) (cycR 0 6)
      ((fun v => (List.range 6).foldlM (childLevelP k index j pads sibs) v) (a.extractLsb' 0 128))
      (ChildPost j B k index u) := by
    intro a
    have hmid : MidE j B k index u 0 (a.extractLsb' 0 128) (writeHash t a) := by
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
    show TBSim im sk (writeHash t a) (cycR 0 6)
      ((List.range 6).foldlM (childLevelP k index j pads sibs) (a.extractLsb' 0 128)) (ChildPost j B k index u)
    rw [List.range_eq_range']
    exact child_restE hj hcode hidx hu 6 0 _ _ rfl hmid
  have hg := SigGolfCandidate.T3M.Expand.tb_shortHash_bind' (image := im) (sk := sk)
    (f := fun v => (List.range 6).foldlM (childLevelP k index j pads sibs) v) (hec rfl) h5 hv hin H
  rw [leaf_blocks, cycR_06] at hg
  unfold childProg
  exact (TBSim.steps hst hg).mono (by simp only [p0E]; omega) (fun _ _ h => h)
end ClaudeWCT.W9.Machine.Expand
end
