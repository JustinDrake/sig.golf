import SigGolfCandidate.W9Drv.ChildPrefix
import SigGolfCandidate.W9Machine.WctSourceWords
import SigGolfCandidate.W9Machine.WctPackedHeader
import SigGolfCandidate.W9Machine.WctTraceProgram
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.VerifyP
import SigGolfCandidate.ClaudeWCT.WCT9.Basic

section

namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
def prefixWrites (B A : Nat) : Prop := B + 64 ≤ A ∧ A < B + 464
theorem stagesW_prefix_bound {j off : Nat} (h : off ∈ stagesW j 6) :
    64 ≤ off ∧ off + 8 ≤ 464 := by
  obtain ⟨m, hm, ho⟩ := List.mem_flatMap.mp h
  have hm' := List.mem_range.mp hm
  have hb := bitAt_lt j m
  simp only [stageW, List.mem_cons, List.not_mem_nil, or_false] at ho
  unfold curO at ho
  unfold blkO at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
theorem last_setup {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index P : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs u)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 P) (hP8 : P % 8 = 0) (hPhi : P + 48 ≤ 2 ^ 24)
    (v : Digest) (s : MachineState) (hs : Mid j B k index u 5 v s) :
    ∃ t, Steps im s 4 4 t ∧ fetch im t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧ hashInput t = toQ (pad64 (nodeIn k index j pads sibs v 5)) ∧
      t.pc = pcOf (childBase j + 36) ∧ t.getReg .x11 = 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (P + 16 * bitAt j 6) ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r) ∧
      Frame u t (prefixWrites B) := by
  let l : Nat := 5
  have hl : l < 6 := by decide
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
  have hb6 := bitAt_lt j 6
  have hb1 := bitAt_lt j (l + 1)
  have h10 : t.getReg .x10 = BitVec.ofNat 64 (B + blkO l) := by rw [hreg, lvlRegs_x10, eX8_eval hx8]
  have h11 : t.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [hreg, show (lvlRegs j l).get .x11 = .reg .x11 from rfl]
    exact hs.a1 (by decide)
  have h12 : t.getReg .x12 = BitVec.ofNat 64 (P + 16 * bitAt j 6) := by
    rw [hreg, show (lvlRegs j l).get .x12 = addC (.reg .x9) (BitVec.ofNat 64 (16 * bitAt j 6)) from rfl, addC_eval]
    simp only [E.eval, hkeep .x9 (by decide) (by decide) (by decide) (by decide), h9, ofNat_add_ofNat]
  have hother : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = u.getReg r := by
    intro r h3 h10' h11' h12'
    rw [hreg, lvlRegs_other j l r h3 h10' h11' h12', RegFile.init_get_eval]
    exact hkeep r h3 h10' h11' h12'
  have h5 : t.getReg .x5 = 0 := (hother .x5 (by decide) (by decide) (by decide) (by decide)).trans hu.t0
  have hcur : curO (l + 1) j % 8 = 0 ∧ curO (l + 1) j + 32 ≤ 464 := by
    unfold curO blkO; omega
  have hv : hashArgumentsValid t = true :=
    hashArgs_of t (B + blkO l) 64 (P + 16 * bitAt j 6) h10 h11 h12 (by unfold blkO; omega) (by decide)
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
  refine ⟨t, hst, hec rfl, h5, hv, hin, ?_, h11, h12, hother, ?_⟩
  · rw [← ht, PRes.toState_pc (lvlRes j l) s rfl]
    rfl
  · have hF : Frame s t (fun A => A = B + blkO l + 24 ∨ A = B + blkO l + 16) := by
      intro A hA hn
      simp only [not_or] at hn
      rw [hmem A hA, if_neg hn.1, if_neg hn.2]
    apply (hs.frame.trans hF).mono
    intro A hA h
    rcases h with ⟨off, hoff, rfl⟩ | rfl | rfl
    · have hb := stagesW_prefix_bound hoff
      unfold prefixWrites
      omega
    all_goals change B + 64 ≤ _ ∧ _ < B + 464; norm_num [l, blkO]
theorem aX9_eval {s : MachineState} {P : Nat} (hP : s.getReg .x9 = BitVec.ofNat 64 P) (off : Nat) :
    (aX9 off).eval s = BitVec.ofNat 64 (P + off) := by
  simp only [aX9, Addr.eval, E.eval, hP, ofNat_add_ofNat]
theorem valid_aX9 {s : MachineState} {P off w : Nat} (hP : s.getReg .x9 = BitVec.ofNat 64 P)
    (hal : (P + off) % w = 0) (hhi : P + off + w ≤ MEMORY_BYTES) : (Oblig.valid (aX9 off) w).holds s := by
  simp only [Oblig.holds, aX9_eval hP, accessValid, rangeValid, Bool.and_eq_true, decide_eq_true_eq]
  rw [toNat_ofNat_lt (by unfold MEMORY_BYTES at hhi; omega)]
  exact ⟨hhi, hal⟩
theorem copy_pair {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    (B P : Nat) (s : MachineState) (v other : Digest)
    (hB : s.getReg .x8 = BitVec.ofNat 64 B) (hP : s.getReg .x9 = BitVec.ofNat 64 P)
    (hB8 : B % 8 = 0) (hBhi : B + 1024 ≤ MEMORY_BYTES)
    (hP8 : P % 8 = 0) (hPhi : P + 48 ≤ MEMORY_BYTES)
    (hpc : s.pc = pcOf (childBase j + 37))
    (hv : DigAt s (P + 16 * bitAt j 6) v) (ho : DigAt s (B + sibO 6 j) other) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
      DigAt t P (V3.orderPair j v other).left ∧ DigAt t (P + 16) (V3.orderPair j v other).right ∧
      (∀ r : Reg, r ≠ .x3 → r ≠ .x14 → t.getReg r = s.getReg r) ∧
      Frame s t (fun A => A = P + otherDest j ∨ A = P + otherDest j + 8) := by
  have hb := bitAt_lt j 6
  have hsib : sibO 6 j % 8 = 0 ∧ sibO 6 j ≤ 48 := by unfold sibO blkO; omega
  have hod : otherDest j % 8 = 0 ∧ otherDest j ≤ 16 := by unfold otherDest; omega
  obtain ⟨hst, -⟩ := childRun_sound hcode (childRun_p7 j hj) s hpc (by
    intro o ho
    simp only [p7Res, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact valid_aX9 hP (by omega) (by omega)
    · exact valid_aX9 hP (by omega) (by omega)
    · exact valid_aX8 hB (by omega) (by omega)
    · exact valid_aX8 hB (by omega) (by omega)) rfl
  let t := (p7Res j).toState s
  have hmem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = P + otherDest j + 8 then s.getMem (BitVec.ofNat 64 (B + sibO 6 j + 8))
      else if A = P + otherDest j then s.getMem (BitVec.ofNat 64 (B + sibO 6 j))
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [PRes.toState_getMem]
    simp only [p7Res, memEval_cons, memEval_nil, aX9_eval hP]
    rw [show P + (otherDest j + 8) = P + otherDest j + 8 by omega]
    simp only [E.eval, eX8_eval hB]
    simp only [ofNat_inj hA (show P + otherDest j + 8 < 2 ^ 64 by unfold MEMORY_BYTES at hPhi; omega),
      ofNat_inj hA (show P + otherDest j < 2 ^ 64 by unfold MEMORY_BYTES at hPhi; omega)]
    simp only [Nat.add_assoc]
  have hc : DigAt t (P + 16 * bitAt j 6) v := by
    refine DigAt.of_eq hv ?_ ?_
    all_goals
      rw [hmem _ (by unfold MEMORY_BYTES at hPhi; omega), if_neg (by unfold otherDest; omega),
        if_neg (by unfold otherDest; omega)]
  have hd : DigAt t (P + otherDest j) other := by
    constructor
    · rw [hmem _ (by unfold MEMORY_BYTES at hPhi; omega), if_neg (by omega), if_pos rfl]
      exact ho.1
    · rw [hmem _ (by unfold MEMORY_BYTES at hPhi; omega), if_pos rfl]
      exact ho.2
  refine ⟨t, hst, rfl, ?_, ?_, ?_, ?_⟩
  · rcases (show bitAt j 6 = 0 ∨ bitAt j 6 = 1 by omega) with he | he
    · simpa [V3.orderPair, ← show bitAt j 6 = j / 64 % 2 from rfl, he] using hc
    · simpa [V3.orderPair, ← show bitAt j 6 = j / 64 % 2 from rfl, otherDest, he] using hd
  · rcases (show bitAt j 6 = 0 ∨ bitAt j 6 = 1 by omega) with he | he
    · simpa [V3.orderPair, ← show bitAt j 6 = j / 64 % 2 from rfl, otherDest, he] using hd
    · simpa [V3.orderPair, ← show bitAt j 6 = j / 64 % 2 from rfl, he] using hc
  · intro r h3 h14
    rw [PRes.toState_getReg]
    simp only [p7Res, RegFile.get_set_ne _ _ h14, RegFile.get_set_ne _ _ h3, RegFile.init_get_eval]
  · intro A hA hn
    rw [hmem A hA, if_neg (by tauto), if_neg (by tauto)]
structure PairPost (B P : Nat) (u : MachineState) (pair : V3.RootPair) (t : MachineState) : Prop where
  pc : t.pc = u.getReg .x1 &&& ~~~1#64
  a1 : t.getReg .x11 = 64
  left : DigAt t P pair.left
  right : DigAt t (P + 16) pair.right
  keep : ∀ r : Reg, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x14 → t.getReg r = u.getReg r
  frame : Frame u t (fun A => prefixWrites B A ∨ P ≤ A ∧ A < P + 48)
theorem tail_good {im : Image} {j : Nat} (hj : j < 128) (hcode : ChildCodeAt im j)
    {B k index P : Nat} {leaf pads sibs : Nat → Digest} {u : MachineState}
    (hu : ChildPre j B k index leaf pads sibs u)
    (h9 : u.getReg .x9 = BitVec.ofNat 64 P) (hP8 : P % 8 = 0) (hPB : P + 48 ≤ B)
    (other : Digest) (hsib : DigAt u (B + sibO 6 j) other)
    (v : Digest) (s : MachineState) (hs : Mid j B k index u 5 v s)
    (N C A : Nat) (Q : Prop) (K : V3.RootPair → OracleComp HashSpec Obs)
    (hK : ∀ computed t, PairPost B P u (V3.orderPair j computed other) t →
      GoodQFor im t N C Q A (K (V3.orderPair j computed other))) :
    GoodQFor im s (N + 10) (C + 17) Q (A + 17)
      (ccM (childLevelP k index j pads sibs v 5 >>= fun computed => pure (V3.orderPair j computed other)) K) := by
  have hBhi := hu.baseHi
  have hPhi : P + 48 ≤ 2 ^ 24 := by unfold MEMORY_BYTES at hBhi; omega
  have hb := bitAt_lt j 6
  have hsb : sibO 6 j ≤ 48 := by unfold sibO blkO; omega
  obtain ⟨t, hst, hf, h5, hv, hin, hpc, h11, h12, hkeep, hframe⟩ :=
    last_setup hj hcode hu h9 hP8 hPhi v s hs
  have hsibT : DigAt t (B + sibO 6 j) other := by
    refine DigAt.of_eq hsib ?_ ?_
    all_goals exact hframe _ (by unfold MEMORY_BYTES at hBhi; omega) (by unfold prefixWrites; omega)
  have H : ∀ ans : BitVec 256, GoodQFor im (writeHash t ans) (N + 5) (C + 5) Q (A + 5)
      (ccM (pure (V3.orderPair j (ans.extractLsb' 0 128) other)) K) := by
    intro ans
    have hdest : P + 16 * bitAt j 6 + 32 < 2 ^ 64 := by omega
    have hsibH : DigAt (writeHash t ans) (B + sibO 6 j) other := by
      refine DigAt.of_eq hsibT ?_ ?_
      all_goals
        rw [getMem_writeHash t ans _ _ h12 hdest (by unfold MEMORY_BYTES at hBhi; omega),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    obtain ⟨z, hz, hpcZ, hleft, hright, hk, hfr⟩ := copy_pair hj hcode B P (writeHash t ans) _ other
      (by rw [writeHash_getReg, hkeep .x8 (by decide) (by decide) (by decide) (by decide)]; exact hu.s0)
      (by rw [writeHash_getReg, hkeep .x9 (by decide) (by decide) (by decide) (by decide)]; exact h9)
      hu.base8 hu.baseHi hP8 hPhi
      (by rw [writeHash_pc, hpc, SigGolfCandidate.T3M.pcOf_add4])
      (DigAt.writeHash_lo t ans _ h12 hdest) hsibH
    have hp : PairPost B P u (V3.orderPair j (ans.extractLsb' 0 128) other) z := by
      refine ⟨?_, ?_, hleft, hright, ?_, ?_⟩
      · rw [hpcZ, writeHash_getReg, hkeep .x1 (by decide) (by decide) (by decide) (by decide)]
      · rw [hk .x11 (by decide) (by decide), writeHash_getReg, h11]
      · intro r h3 h10 h11 h12 h14
        rw [hk r h3 h14, writeHash_getReg]
        exact hkeep r h3 h10 h11 h12
      · have hw := frame_writeHash4 t ans _ h12 hdest
        apply ((hframe.trans hw).trans hfr).mono
        intro addr ha hh
        rcases hh with (hc | hw) | hc
        · exact Or.inl hc
        · right
          rcases hw with rfl | rfl | rfl | rfl <;> omega
        · right
          have hod : otherDest j ≤ 16 := by unfold otherDest; omega
          rcases hc with rfl | rfl <;> omega
    simpa only [ccM_pure] using GoodQFor.steps hz (hK _ z hp)
  have hh := GoodQFor.shortHash_bind (f := fun computed => pure (V3.orderPair j computed other)) (K := K) hf h5 hv hin H
  rw [nodeIn_blocks] at hh
  rw [childLevelP_eq]
  exact GoodQFor.steps' hst hh (by omega) (by omega) (fun q => ⟨q, by omega⟩)
end W9Drv.ChildProof
end

section

namespace W9Drv.ChildProof
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest HashOutput M shortHash pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem nodeInput_eq (k index heap : Nat) (left pad right : Digest) :
    V3.nodeInput k index heap left pad right = blk4 left (nodeHeader k index heap) pad right := by
  have hb (lo hi : BitVec 64) : bytesLE 8 lo ++ bytesLE 8 hi = bytesLE 16 (hi ++ lo) := by
    apply readLE_inj (by simp [bytesLE_length])
    simp only [readLE_append, bytesLE_length, readLE_bytesLE, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]
    omega
  simp only [V3.nodeInput, blk4, nodeHeader, w0n, ← hb, List.append_assoc]
  rfl
theorem heapOf_eq (j l : Nat) (hl : l < 6) : heapOf l j = (128 + j) / 2 ^ (l + 1) := by
  interval_cases l <;> norm_num [heapOf, Nat.add_div] <;> omega
theorem source_level (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (v : Digest) (l : Nat) (hl : l < 6) :
    (let other := V3.sibling w k.val j.val l
     let left := if j.val / 2 ^ l % 2 = 0 then v else other
     let right := if j.val / 2 ^ l % 2 = 0 then other else v
     shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (l + 1)) left (V3.nodePad w k.val l) right)) =
    childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val) v l := by
  dsimp only
  rw [nodeInput_eq, ← heapOf_eq _ _ hl]
  unfold childLevelP bitAt
  split_ifs <;> rfl
theorem childProgram_split (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest) :
    V3.childProgram w index k j ends =
      (shortHash (leafBytes (V3.leafFields k.val index j.val ends)) >>= fun v =>
        (List.range 5).foldlM (childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val)) v >>=
        fun v5 => childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val) v5 5 >>=
        fun computed => pure (V3.orderPair j.val computed (V3.sibling w k.val j.val 6))) := by
  unfold V3.childProgram
  congr 1
  funext v
  have hfold (ls : List Nat) (hls : ∀ l ∈ ls, l < 6) (v : Digest) :
      ls.foldlM (fun value level =>
        let other := V3.sibling w k.val j.val level
        let left := if j.val / 2 ^ level % 2 = 0 then value else other
        let right := if j.val / 2 ^ level % 2 = 0 then other else value
        shortHash (V3.nodeInput k.val index ((128 + j.val) / 2 ^ (level + 1))
          left (V3.nodePad w k.val level) right)) v =
      ls.foldlM (childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val)) v := by
    induction ls generalizing v with
    | nil => rfl
    | cons l ls ih =>
      rw [List.foldlM_cons, List.foldlM_cons, source_level w index k j v l (hls l (by simp))]
      congr 1
      funext v'
      exact ih (fun i hi => hls i (List.mem_cons_of_mem _ hi)) v'
  rw [hfold (List.range 6) (fun l hl => List.mem_range.mp hl)]
  rw [show List.range 6 = List.range 5 ++ [5] from rfl, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, bind_assoc]
theorem child_code (j : Nat) (hj : j < 128) : ChildCodeAt Frozen.image j := by
  have hc := (slice_at _ _ (child_linked j hj)).2.2.2
  have hp : (pcOf (childBase j)).toNat = 4096 + 4 * childBase j := by
    simp only [pcOf, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold childBase; omega)
  rw [hp, show (4096 + 4 * childBase j - 4096) / 4 = childBase j by omega] at hc
  intro i word hi
  obtain ⟨hbound, hval⟩ := List.getElem?_eq_some_iff.mp hi
  have h := List.prefix_iff_getElem?.mp hc i hbound
  simpa only [List.getElem?_drop, hval] using h
theorem child_pre (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (ends : List Digest)
    (u : MachineState) (hu : Child.Pre Frozen.layout w index k j ends u) :
    ChildPre j.val (coordinateBase k) k.val index (V3.leafFields k.val index j.val ends)
      (V3.nodePad w k.val) (V3.sibling w k.val j.val) u := by
  refine ⟨hu.pc, ?_, ?_, hu.hashMode, hu.baseReg, hu.hashInput, hu.hashLen, hu.nodeHeader,
    hu.indexReg, ?_, hu.leafAt, hu.padAt, ?_⟩
  · unfold coordinateBase
    omega
  · have hk := k.isLt
    unfold coordinateBase MEMORY_BYTES
    omega
  · intro h h2 h7
    have he : heapReg h = Child.heapReg h := by interval_cases h <;> rfl
    rw [he]
    exact hu.heaps h h2 h7
  · intro l hl
    have he : sibO l j.val = V3.siblingOffset j.val l := by
      have hb := bitAt_lt j.val l
      unfold sibO V3.siblingOffset V3.blockOffset blkO bitAt at *
      split_ifs <;> omega
    rw [he]
    exact hu.sibAt l (by omega)
theorem child_good : ChildGood := by
  intro j w index k ends u N C A Q K hu hK
  have hp := child_pre w index k j ends u hu
  have hcode := child_code j.val j.isLt
  have hP8 : pairAddress k % 8 = 0 := by unfold pairAddress; omega
  have hPB : pairAddress k + 48 ≤ coordinateBase k := by unfold pairAddress coordinateBase; omega
  have hsib : DigAt u (coordinateBase k + sibO 6 j.val) (V3.sibling w k.val j.val 6) := by
    have he : sibO 6 j.val = V3.siblingOffset j.val 6 := by
      have hb := bitAt_lt j.val 6
      unfold sibO V3.siblingOffset V3.blockOffset blkO bitAt at *
      split_ifs <;> omega
    rw [he]
    exact hu.sibAt 6 (by decide)
  have hg := child_prefix_good Frozen.image j.val j.isLt hcode (coordinateBase k) k.val index
    (V3.leafFields k.val index j.val ends) (V3.nodePad w k.val) (V3.sibling w k.val j.val) u
    (N + 10) (C + 17) (A + 17) Q
    (fun v => ccM (childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val) v 5 >>=
      fun computed => pure (V3.orderPair j.val computed (V3.sibling w k.val j.val 6))) K)
    (by have := hu.indexBound; omega) hp (fun v s hs => by
      apply tail_good j.isLt hcode hp hu.forestPointer hP8 hPB _ hsib v s hs N C A Q K
      intro computed t ht
      apply hK _ t
      refine ⟨?_, ht.a1, ht.left, ht.right, ?_, ht.frame⟩
      · rw [ht.pc, hu.returnPC]
        fin_cases k <;> decide
      · intro r hr
        simp only [Child.clobbers, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact ht.keep r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2)
  rw [childProgram_split]
  simp only [ccM_bind, Nat.add_assoc] at hg ⊢
  exact hg
#print axioms child_good
end W9Drv.ChildProof
end

section




set_option autoImplicit false
namespace W9Machine
open OracleComp SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest M)
open ClaudeWCT
theorem chainLow_canonical (index coord child chain step : Nat)
    (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128) (ht : chain < 7) (hs : step < 3) :
    V3.chainLow index coord child chain step = WCT9.ftsChainLow index coord child chain step := by
  rw [chainLow_add _ _ _ _ _ ht hs, chainPrefix_value _ _ _ hk hj]
  unfold WCT9.ftsChainLow
  rw [Nat.mod_eq_of_lt (by omega : chain < 8), Nat.mod_eq_of_lt (by omega : step < 4),
    Nat.mod_eq_of_lt (by omega : coord < 16), Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hi]
  omega
theorem chainInput_canonical (index coord child chain step : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 7) (hs : step < 3) :
    V3.chainInput index coord child chain step a b c value =
      ClaudeWCT.W9.T3M.wctChainInputP index coord child chain step a b c value := by
  change _ = blk4 a (WCT9.ftsChainHeaderP index coord child chain step b) c value
  rw [← wordBytes_wordsOf (V3.chainInput _ _ _ _ _ _ _ _ _) 8
      (chainInput_length _ _ _ _ _ _ _ _ _),
    ← wordBytes_wordsOf (blk4 _ _ _ _) 8 (blk4_length _ _ _ _),
    wordsOf_chainInput, wordsOf_blk4]
  simp only [dlo, dhi, WCT9.ftsChainHeaderP_low, WCT9.ftsChainHeaderP_high,
    chainLow_canonical _ _ _ _ _ hi hk hj ht hs]
theorem chainP_canonical (index coord child chain start count : Nat) (a c value : Digest)
    (b : V3.HeaderPad) (hi : index < 2 ^ 31) (hk : coord < 9) (hj : child < 128)
    (ht : chain < 7) (hbound : start + count ≤ 3) :
    V3.chainP index coord child chain start count a b c value =
      ClaudeWCT.W9.T3M.wctChainP index coord child chain start count a b c value := by
  induction count generalizing start value with
  | zero => rfl
  | succ count ih =>
    simp only [V3.chainP, ClaudeWCT.W9.T3M.wctChainP, List.range'_succ, List.foldlM_cons]
    rw [chainInput_canonical _ _ _ _ _ _ _ _ _ hi hk hj ht (by omega)]
    congr 1
    funext v
    exact ih (start + 1) v (by omega)
def canonicalChains (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128) (rank : Fin 728) :
    M (List Digest) :=
  (List.finRange 7).mapM fun t =>
    let d := WCT9.digit rank t
    ClaudeWCT.W9.T3M.wctChainP index k.val j.val t.val (3 - d) d
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).1
      (ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val)
      (ClaudeWCT.W9.T3M.wcpads w k.val t.val).2
      (ClaudeWCT.W9.T3M.wreveal w k.val t.val d)
theorem chainProgram_canonical (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) (hi : index < 2 ^ 31) :
    V3.chainProgram w index k j rank = canonicalChains w index k j rank := by
  unfold V3.chainProgram canonicalChains
  congr 1
  funext t
  have hd := WCT9.digit_le_three rank t
  rw [chainP_canonical _ _ _ _ _ _ _ _ _ _ hi k.isLt j.isLt t.isLt (by omega)]
  have hb : V3.chainPadB w k.val t.val = ClaudeWCT.W9.T3M.wcHeaderPad w k.val t.val := by
    simp only [V3.chainPadB, ClaudeWCT.W9.T3M.wcHeaderPad, SigGolfCandidate.T3M.wdig_hi,
      V3.chainOffset, V3.regionOffset, ClaudeWCT.W9.T3M.wctChainBlock,
      ClaudeWCT.W9.T3M.regionBase, Nat.add_assoc, Nat.reduceAdd]
  rw [hb]
  rfl
end W9Machine
end

section



namespace W9Drv
open W9Machine W9Drv.ChildProof SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open OracleComp
theorem nodeLow_add (k : Fin 9) (index : Nat) : V3.nodeLow k.val index = 1 + 3 * 256 + (4+k.val)*65536 + index*2^32 := by
  unfold V3.nodeLow
  fin_cases k <;> norm_num only [Nat.reduceAdd, Nat.reduceShiftLeft, Nat.reduceOr]
  all_goals rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by decide)]
  all_goals simp [Nat.shiftLeft_eq, Nat.add_comm]
theorem nodeHeader_canonical (k : Fin 9) (index heap : Nat) (hi : index < 2^31) (hh : heap < 2^32) :
  nodeHeader k.val index heap = ClaudeWCT.WCT9.wctNodeHeader k.val index heap := by
  rw [ClaudeWCT.WCT9.wctNodeHeader_eq _ _ _ (by omega) (by omega) hh]
  apply BitVec.eq_of_toNat_eq
  simp only [nodeHeader, w0n, BitVec.toNat_append, BitVec.toNat_ofNat]
  rw [nodeLow_add]
  have hk := k.isLt
  have hb : 1 + 3 * 256 + (4 + k.val) * 65536 + index * 2^32 < 2^64 := by omega
  rw [Nat.mod_eq_of_lt (by omega : heap < 2^64), Nat.mod_eq_of_lt hb,
    ← Nat.shiftLeft_add_eq_or_of_lt hb, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega
open SigGolfCandidate.T3 (Digest M shortHash)
def coordTail (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) : M (Digest × Digest) := do
  let leaf ← ClaudeWCT.WCT9.leafHash index k.val j.val ends
  let top ← (List.finRange 6).foldlM (fun value level => do
    let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
    let pair := if j.val / 2 ^ level.val % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.W9.T3M.wctNodeHashP k.val index
      (2 ^ (6 - level.val) + j.val / 2 ^ (level.val + 1))
      pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val level.val) pair.2) leaf
  let other := ClaudeWCT.W9.T3M.wsib w k.val j.val 6
  pure (if j.val / 2 ^ 6 % 2 = 0 then (top, other) else (other, top))
theorem wctCoordP_split (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (rank : Fin 728) (hi : index < 2 ^ 31) :
    ClaudeWCT.W9.T3M.wctCoordP w index k j rank =
      (V3.chainProgram w index k j rank >>= coordTail w index k j) := by
  rw [chainProgram_canonical w index k j rank hi]
  rfl
theorem leafInput_canonical (k index j : Nat) (ends : List Digest) (h : ends.length = 7) :
    shortHash (V3.leafInput k index j ends) = ClaudeWCT.WCT9.leafHash index k j ends := by
  match ends, h with
  | [e0, e1, e2, e3, e4, e5, e6], _ =>
    simp only [V3.leafInput, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.flatMap_cons, List.flatMap_nil, V3.leafFields, ClaudeWCT.WCT9.leafHash,
      List.drop_succ_cons, List.drop_zero, List.append_nil, List.append_assoc,
      ClaudeWCT.WCT9.leaf_header_eq]
    rfl
theorem source_level_canonical (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (v : Digest) (l : Nat) (hl : l < 6) (hi : index < 2^31) :
    childLevelP k.val index j.val (V3.nodePad w k.val) (V3.sibling w k.val j.val) v l =
      (let other := ClaudeWCT.W9.T3M.wsib w k.val j.val l
       let pair := if j.val / 2 ^ l % 2 = 0 then (v, other) else (other, v)
       ClaudeWCT.W9.T3M.wctNodeHashP k.val index (heapOf l j.val)
         pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val l) pair.2) := by
  have hh : heapOf l j.val < 2^32 := by
    have hj := j.isLt
    interval_cases l <;> norm_num [heapOf] <;> omega
  unfold childLevelP
  rw [nodeHeader_canonical k index (heapOf l j.val) hi hh]
  simp only [bitAt, V3.sibling, V3.siblingOffset, V3.nodePad, V3.blockOffset,
    V3.regionOffset, ClaudeWCT.W9.T3M.wsib, ClaudeWCT.W9.T3M.wmpad,
    ClaudeWCT.W9.T3M.wctMerkleBlock, ClaudeWCT.W9.T3M.regionBase,
    sibOff, Nat.add_assoc]
  have hb : j.val / 2^l % 2 = 0 ∨ j.val / 2^l % 2 = 1 := by omega
  rcases hb with hb | hb <;> simp only [hb] <;> rfl
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
theorem childProgram_canonical (w : WBytes) (index : Nat) (k : Fin 9) (j : Fin 128)
    (ends : List Digest) (hends : ends.length = 7) (hi : index < 2^31) :
    (V3.childProgram w index k j ends >>= fun p => pure (p.left, p.right)) =
      coordTail w index k j ends := by
  unfold V3.childProgram coordTail
  rw [leafInput_canonical _ _ _ _ hends]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext leaf
  have hf : (List.range 6).foldlM (fun value level =>
        shortHash (V3.nodeInput k.val index ((128+j.val)/2^(level+1))
          (if j.val/2^level%2=0 then value else V3.sibling w k.val j.val level)
          (V3.nodePad w k.val level)
          (if j.val/2^level%2=0 then V3.sibling w k.val j.val level else value))) leaf =
      (List.finRange 6).foldlM (fun value level =>
        let other := ClaudeWCT.W9.T3M.wsib w k.val j.val level.val
        let pair := if j.val/2^level.val%2=0 then (value,other) else (other,value)
        ClaudeWCT.W9.T3M.wctNodeHashP k.val index (heapOf level.val j.val)
          pair.1 (ClaudeWCT.W9.T3M.wmpad w k.val level.val) pair.2) leaf := by
    rw [← finRange_map_val (n := 6), List.foldlM_map]
    congr 1
    funext value level
    rw [source_level w index k j value level.val level.isLt,
      source_level_canonical w index k j value level.val level.isLt hi]
  rw [hf]
  congr 1
  funext value
  simp only [V3.orderPair, V3.sibling, V3.siblingOffset, V3.blockOffset,
    V3.regionOffset, ClaudeWCT.W9.T3M.wsib, ClaudeWCT.W9.T3M.wctMerkleBlock,
    ClaudeWCT.W9.T3M.regionBase, sibOff, Nat.add_assoc]
  have hb : j.val/64%2=0 ∨ j.val/64%2=1 := by omega
  rcases hb with hb | hb <;> simp only [show 2^6=64 from rfl, hb] <;> rfl
end W9Drv
end
