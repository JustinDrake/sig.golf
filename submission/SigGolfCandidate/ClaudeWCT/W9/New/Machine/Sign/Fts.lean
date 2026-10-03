import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsChild

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash nodeHash)
def loopW (c : Nat) (A : Nat) : Prop := bodyW c A ∨ (HEAPW + 16 * 128 ≤ A ∧ A < SCREND)
structure LoopInv (sk : BitVec 256) (c index sel w : Nat) (s0 : MachineState) (j : Nat)
    (acc : List Digest × List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if j < 128 then leafI c else nodeI c)
  body : BodySt sk (if j < 128 then j else 127) index sel w t
  len : acc.1.length = j
  leaves : ∀ j' < j, DigAt t (HEAPW + 16 * (128 + j')) (acc.1.getD j' 0)
  vals : sel < j → acc.2.length = 7 ∧ ∀ i < 7, DigAt t (slotV c i) (acc.2.getD i 0)
  nosig : j ≤ sel → ∀ A, A < 2 ^ 64 → slotV c 0 ≤ A → A < slotV c 7 →
    t.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A)
  regs : RegsExcept s0 t (.x18 :: bodyRegs)
  frame : Frame s0 t (loopW c)
def loopStepC : Nat := childC + 4
theorem BodySt.with18 {sk : BitVec 256} {j j' index sel w : Nat} {u v : MachineState} (h : BodySt sk j index sel w u)
    (hr : RegsExcept u v [.x6, .x18]) (hf : Frame u v (fun _ => False)) (h18 : v.getReg .x18 = BitVec.ofNat 64 j') :
    BodySt sk j' index sel w v := by
  have g : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) := fun A hA => hf.get hA id
  exact ⟨by rw [hr.get (by simp)]; exact h.x5, h18, by rw [hr.get (by simp)]; exact h.x22,
    by rw [hr.get (by simp)]; exact h.x24, by rw [hr.get (by simp)]; exact h.x25,
    by rw [g _ (by ao)]; exact h.p0, by rw [g _ (by ao)]; exact h.p8, by rw [g _ (by ao)]; exact h.p32,
    by rw [g _ (by ao)]; exact h.p40, by rw [g _ (by ao)]; exact h.p48, by rw [g _ (by ao)]; exact h.p56,
    by rw [g _ (by ao)]; exact h.z0, by rw [g _ (by ao)]; exact h.z8, by rw [g _ (by ao)]; exact h.z32,
    by rw [g _ (by ao)]; exact h.z40⟩
section loop
variable {im : Image} {sk : BitVec 256}
theorem child_step (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hsel : sel < 128)
    (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {s0 : MachineState} (j : Nat) (hj : j < 128) (acc : List Digest × List Digest) (t : MachineState)
    (h : LoopInv sk c index sel w s0 j acc t) :
    TBSim im sk t loopStepC (do
        let (root, values) ← WCT9.buildChild index c j word
        pure (acc.1 ++ [root], if j = sel then values else acc.2)) (LoopInv sk c index sel w s0 (j + 1)) := by
  have hpc : t.pc = pcOf (leafI c) := by rw [h.pc, if_pos hj]
  have hb : BodySt sk j index sel w t := by have := h.body; rwa [if_pos hj] at this
  refine (TBSim.bind (W₂ := 4) (child_unit hcode hc hj hsel hidx hw hword hpc hb) (fun rv u hu => ?_)).mono
    (by unfold loopStepC; omega) (fun _ _ h => h)
  obtain ⟨root, values⟩ := rv
  obtain ⟨upc, ub, uroot, usel, uregs, uframe, unos⟩ := hu
  obtain ⟨v, k, sv, hk, vp1, vp2, vregs, vframe⟩ := step_T hcode hc hj u upc ub.x18
  refine TBSim.pure_steps' sv ?_ |>.mono hk (fun _ _ h => h)
  have hheap : ∀ A, A < 2 ^ 64 → v.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) :=
    fun A hA => vframe.get hA (fun h => h)
  have fuv : Frame t v (childW c j) := (uframe.trans vframe).mono (fun A _ hA => by
    rcases hA with hA | hA
    · exact hA
    · exact hA.elim)
  refine ⟨?_, ?_, ?_, fun j' hj' => ?_, fun hs => ?_, fun hs A hA h1 h2 => ?_, ?_, ?_⟩
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact (vp1 h1).1
    · rw [if_neg h1]; exact (vp2 (by omega)).1
  · by_cases h1 : j + 1 < 128
    · rw [if_pos h1]; exact ub.with18 vregs vframe (vp1 h1).2
    · rw [if_neg h1]; exact ub.with18 vregs vframe (vp2 (by omega)).2
  · simp [h.len]
  · by_cases hlt : j' < j
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [h.len]; exact hlt),
        ← List.getD_eq_getElem?_getD]
      refine (h.leaves j' hlt).frame fuv (by ao) ?_ ?_ <;> (unfold childW bodyW slotV; aoh)
    · have : j' = j := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h.len]), h.len, Nat.sub_self]
      exact uroot.frame vframe (by ao) (fun h => h) (fun h => h)
  · by_cases hjs : j = sel
    · subst hjs
      rw [if_pos rfl]
      obtain ⟨hl, hd⟩ := usel rfl
      exact ⟨hl, fun i hi => (hd i hi).frame vframe (by unfold slotV; ao) (fun h => h) (fun h => h)⟩
    · rw [if_neg hjs]
      obtain ⟨hl, hd⟩ := h.vals (by omega)
      refine ⟨hl, fun i hi => ⟨?_, ?_⟩⟩
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).1
      · rw [hheap _ (by unfold slotV; ao), unos hjs _ (by unfold slotV; ao) (by unfold slotV; omega)
          (by unfold slotV; omega)]
        exact (hd i hi).2
  · rw [hheap A hA, unos (by omega) A hA h1 h2]; exact h.nosig (by omega) A hA h1 h2
  · exact (h.regs.trans (uregs.trans vregs)).mono (by simp [bodyRegs])
  · refine (h.frame.trans fuv).mono (fun A _ hA => ?_)
    unfold loopW
    rcases hA with hA | hA
    · exact hA
    · unfold childW at hA
      rcases hA with hA | hA
      · left; exact hA
      · right; constructor <;> aoh
theorem LoopInv.init {c index sel w : Nat} {s0 : MachineState} (hpc : s0.pc = pcOf (leafI c))
    (hb : BodySt sk 0 index sel w s0) : LoopInv sk c index sel w s0 0 ([], []) s0 :=
  ⟨by rw [if_pos (by norm_num)]; exact hpc, by rw [if_pos (by norm_num)]; exact hb, rfl,
    fun j' hj' => absurd hj' (by omega), fun h => absurd h (by omega), fun _ _ _ _ _ => rfl,
    RegsExcept.refl _ _, Frame.refl _ _⟩
theorem child_loop (hcode : NewCodeAt im) {c index sel w : Nat} {word : WCT9.Rank} (hc : c < 9) (hsel : sel < 128)
    (hidx : index < 2 ^ 31) (hw : w < 2 ^ 64) (hword : ∀ i : Fin 7, w / 4 ^ i.val % 4 = WCT9.digit word i)
    {s0 : MachineState} (h0 : LoopInv sk c index sel w s0 0 ([], []) s0) :
    TBSim im sk s0 (128 * loopStepC) (WCT9.coordRows index ⟨c, hc⟩ ⟨sel, hsel⟩ word)
      (LoopInv sk c index sel w s0 128) := by
  unfold WCT9.coordRows
  rw [List.range_eq_range']
  exact TBSim.foldlM_range' 0 128 _ _ (LoopInv sk c index sel w s0) loopStepC
    (fun j hj acc t ht => by
      simp only [Nat.zero_add]
      exact child_step hcode hc hsel hidx hw hword j hj acc t ht) h0
end loop
def treeStep (index c : Nat) (nodes : Array Digest) (heap : Nat) : M (Array Digest) := do
  let value ← nodeHash 11 c index heap (nodes.getD (2 * heap) 0) (nodes.getD (2 * heap + 1) 0)
  pure (nodes.set! heap value)
theorem heap_order_list : (List.range' 1 127).reverse = (List.range' 0 127).map (fun k => 127 - k) := by
  decide +kernel
theorem heapBuild_eq (index c : Nat) (leaves : List Digest) :
    WCT9.heapBuild index c leaves =
      (List.range' 0 127).foldlM (fun nodes k => treeStep index c nodes (127 - k))
        ((List.replicate 128 (0 : Digest) ++ leaves).toArray) := by
  unfold WCT9.heapBuild
  rw [heap_order_list, List.foldlM_map]
  rfl
def treeRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x28, .x29]
def treeW (A : Nat) : Prop :=
  (A = NODEW ∨ A = NODEW + 8 ∨ A = NODEW + 16 ∨ A = NODEW + 24 ∨ A = NODEW + 48 ∨ A = NODEW + 56) ∨
    (NOUTW ≤ A ∧ A < NOUTW + 32) ∨ (HEAPW + 16 ≤ A ∧ A < HEAPW + 2048)
structure TreeInv (c index : Nat) (s0 : MachineState) (k : Nat) (nodes : Array Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 127 then nodeI c else rI c)
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 (127 - k)
  x22 : t.getReg .x22 = BitVec.ofNat 64 index
  size : nodes.size = 256
  heap : ∀ m, 127 - k < m → m < 256 → DigAt t (HEAPW + 16 * m) (nodes.getD m 0)
  z32 : t.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0
  z40 : t.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0
  regs : RegsExcept s0 t (.x18 :: treeRegs)
  frame : Frame s0 t treeW
def treeC : Nat := 25 + (8 + 12)
theorem hashInput_node (t : MachineState) {c index h : Nat} {L R : Digest} (hc : c < 9) (hidx : index < 2 ^ 32)
    (hh : h < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODEW) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hL : DigAt t NODEW L) (m16 : t.getMem (BitVec.ofNat 64 (NODEW + 16)) = BitVec.ofNat 64 (hdr11 c))
    (m24 : t.getMem (BitVec.ofNat 64 (NODEW + 24)) = BitVec.ofNat 64 (index + 2 ^ 32 * h))
    (z32 : t.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0) (z40 : t.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0)
    (hR : DigAt t (NODEW + 48) R) : hashInput t = toQ (pad64 (nodeIn c index h L R)) := by
  refine hashInput_of_words t _ 0 NODEW (by rw [pad64_of_aligned _ (by rw [nodeIn_len]), nodeIn_len]) h10 (by ao)
    (by ao) h11 ?_
  rw [wordsOf_node c index h L R (by omega) hidx hh]
  intro k hk
  interval_cases k
  · exact hL.1
  · exact hL.2
  · exact m16
  · exact m24
  · exact z32
  · exact z40
  · exact hR.1
  · exact hR.2
section tree
variable {im : Image} {sk : BitVec 256}
theorem tree_step (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    (k : Nat) (hk : k < 127) (nodes : Array Digest) (t : MachineState) (h : TreeInv c index s0 k nodes t) :
    TBSim im sk t treeC (treeStep index c nodes (127 - k)) (TreeInv c index s0 (k + 1)) := by
  have hpc : t.pc = pcOf (nodeI c) := by rw [h.pc, if_pos hk]
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, n0, n8, n48, n56, n16, n24, r1, f1⟩ :=
    step_N hcode hc (by omega : 1 ≤ 127 - k) (by omega) t hpc h.x18 h.x22 (by omega)
  have hL : DigAt t1 NODEW (nodes.getD (2 * (127 - k)) 0) := by
    have := h.heap (2 * (127 - k)) (by omega) (by omega)
    exact ⟨by rw [n0, show HEAPW + 32 * (127 - k) = HEAPW + 16 * (2 * (127 - k)) by ring]; exact this.1,
      by rw [n8, show HEAPW + 32 * (127 - k) + 8 = HEAPW + 16 * (2 * (127 - k)) + 8 by ring]; exact this.2⟩
  have hR : DigAt t1 (NODEW + 48) (nodes.getD (2 * (127 - k) + 1) 0) := by
    have := h.heap (2 * (127 - k) + 1) (by omega) (by omega)
    exact ⟨by rw [n48, show HEAPW + 32 * (127 - k) + 16 = HEAPW + 16 * (2 * (127 - k) + 1) by ring]; exact this.1,
      by rw [show NODEW + 48 + 8 = NODEW + 56 by ao, n56,
        show HEAPW + 32 * (127 - k) + 24 = HEAPW + 16 * (2 * (127 - k) + 1) + 8 by ring]; exact this.2⟩
  have hz32 : t1.getMem (BitVec.ofNat 64 (NODEW + 32)) = 0 := by rw [f1.get (by ao) (by intro h'; aoh)]; exact h.z32
  have hz40 : t1.getMem (BitVec.ofNat 64 (NODEW + 40)) = 0 := by rw [f1.get (by ao) (by intro h'; aoh)]; exact h.z40
  have hq := hashInput_node t1 hc (by omega : index < 2 ^ 32) (by omega : 127 - k < 2 ^ 32) x10 x11 hL n16 n24 hz32 hz40 hR
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h.x5
  unfold treeStep
  rw [nodeHash_eq]
  refine (TBSim.steps s1 (TBSim.shortHash_bind' (W := 12) (f := fun value => pure (nodes.set! (127 - k) value)) e1 hx5
    (hashArgs_const t1 NODEW 64 NOUTW x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by rw [blocks64 _ (nodeIn_len _ _ _ _ _)]; unfold treeC; omega) (fun _ _ h => h)
  set u := writeHash t1 a with hu
  have fu := Frame.writeHash t1 a NOUTW x12 (by ao)
  have hntpc : u.pc = pcOf (ntI c) := by
    rw [hu, pc_writeHash, p1]
    have : 1 ≤ ntI c := by have : ∀ c, c < 9 → 1 ≤ ntI c := by decide +kernel
                           exact this c hc
    exact pcOf_pred4 _ this
  have u18 : u.getReg .x18 = BitVec.ofNat 64 (127 - k) := by rw [hu, getReg_writeHash, r1.get (by simp)]; exact h.x18
  obtain ⟨t2, s2, q1, q2, x18', w0, w8, r2, f2⟩ := step_NT hcode hc (by omega : 1 ≤ 127 - k) (by omega) u hntpc u18
  have hout := DigAt.writeHash_lo t1 a NOUTW x12 (by ao)
  refine TBSim.pure_steps' s2 ⟨?_, ?_, ?_, ?_, ?_, fun m hm1 hm2 => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hk1 : k + 1 < 127
    · rw [if_pos hk1]; exact q1 (by omega)
    · rw [if_neg hk1]; exact q2 (by omega)
  · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x5
  · rw [x18', show 127 - k - 1 = 127 - (k + 1) by omega]
  · rw [r2.get (by simp), hu, getReg_writeHash, r1.get (by simp)]; exact h.x22
  · simp [h.size]
  · by_cases hmk : m = 127 - k
    · subst hmk
      rw [WCT9.getD_set_self _ _ _ (by rw [h.size]; omega)]
      exact ⟨by rw [w0]; exact hout.1, by rw [w8]; exact hout.2⟩
    · rw [WCT9.getD_set_other _ _ _ _ (fun he => hmk he.symm)]
      have hd := h.heap m (by omega) hm2
      have g : ∀ A, (A = HEAPW + 16 * m ∨ A = HEAPW + 16 * m + 8) →
          t2.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
        intro A hA
        rw [f2.get (by aoh) (by intro h'; aoh), fu.get (by aoh) (by intro h'; aoh), f1.get (by aoh) (by intro h'; aoh)]
      exact ⟨by rw [g _ (Or.inl rfl)]; exact hd.1, by rw [g _ (Or.inr rfl)]; exact hd.2⟩
  · rw [f2.get (by ao) (by intro h'; aoh), fu.get (by ao) (by intro h'; aoh)]; exact hz32
  · rw [f2.get (by ao) (by intro h'; aoh), fu.get (by ao) (by intro h'; aoh)]; exact hz40
  · exact (h.regs.trans ((r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 u [])).trans r2)).mono
      (by simp [treeRegs])
  · refine (((h.frame.trans f1).trans fu).trans f2).mono (fun A _ hA => ?_)
    unfold treeW
    rcases hA with ((hA | hA) | hA) | hA
    · exact hA
    · left; rcases hA with h' | h' | h' | h' | h' | h' <;> simp [h']
    · right; left; exact hA
    · right; right; rcases hA with rfl | rfl <;> constructor <;> omega
theorem tree_loop (hcode : NewCodeAt im) {c index : Nat} (hc : c < 9) (hidx : index < 2 ^ 31) {s0 : MachineState}
    {leaves : List Digest} (h0 : TreeInv c index s0 0 ((List.replicate 128 (0 : Digest) ++ leaves).toArray) s0) :
    TBSim im sk s0 (127 * treeC) (WCT9.heapBuild index c leaves) (TreeInv c index s0 127) := by
  rw [heapBuild_eq]
  exact TBSim.foldlM_range' 0 127 _ _ (TreeInv c index s0) treeC
    (fun k hk nodes t ht => by
      simp only [Nat.zero_add]
      exact tree_step hcode hc hidx k hk nodes t ht) h0
end tree
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash nodeHash)
structure GlobSt (sk : BitVec 256) (N : BitVec 256) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x22 : t.getReg .x22 = BitVec.ofNat 64 (N.toNat % 2 ^ 31)
  nbuf : OutAt t NBUF N
  table : TableAt t
  p0 : t.getMem (BitVec.ofNat 64 PRIVW) = sk.extractLsb' 0 64
  p8 : t.getMem (BitVec.ofNat 64 (PRIVW + 8)) = sk.extractLsb' 64 64
  p32 : t.getMem (BitVec.ofNat 64 (PRIVW + 32)) = sk.extractLsb' 128 64
  p40 : t.getMem (BitVec.ofNat 64 (PRIVW + 40)) = sk.extractLsb' 192 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
def coordW (c : Nat) (A : Nat) : Prop :=
  loopW c A ∨ treeW A ∨ A = FORW + forOff c ∨ A = FORW + forOff c + 8 ∨ (slotP c 0 ≤ A ∧ A < slotP c 7)
theorem GlobSt.frame {sk N : BitVec 256} {s t : MachineState} {c : Nat} {l : List Reg} (hc : c < 9)
    (h : GlobSt sk N s) (hr : RegsExcept s t l) (hl : .x5 ∉ l ∧ .x22 ∉ l) (hf : Frame s t (coordW c)) :
    GlobSt sk N t := by
  have hfo : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
  have nw : ∀ A, (NBUF ≤ A ∧ A < NBUF + 32 ∨ TBL ≤ A ∧ A < TBL + 65536 ∨ A = PRIVW ∨ A = PRIVW + 8 ∨
      A = PRIVW + 32 ∨ A = PRIVW + 40 ∨ ScrZero A) → ¬ coordW c A := by
    intro A hA hw
    unfold coordW loopW bodyW treeW slotV slotP ScrZero at *
    aoh
  refine ⟨by rw [hr.get hl.1]; exact h.x5, by rw [hr.get hl.2]; exact h.x22, fun k hk => ?_, fun k hk => ?_,
    ?_, ?_, ?_, ?_, fun A hA => ?_⟩
  · rw [hf.get (by ao) (nw _ (Or.inl (by constructor <;> ao)))]; exact h.nbuf k hk
  · rw [hf.get (by ao) (nw _ (Or.inr (Or.inl (by constructor <;> ao))))]; exact h.table k hk
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p0
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p8
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p32
  · rw [hf.get (by ao) (nw _ (by simp))]; exact h.p40
  · have hA' : A < 2 ^ 64 := by unfold ScrZero at hA; aoh
    rw [hf.get hA' (nw _ (by simp [hA]))]; exact h.zero A hA
theorem coordW_other {c c' A : Nat} (hc : c < 9) (hc' : c' < 9) (hne : c ≠ c')
    (hA : (SIG + 16 + 224 * c' ≤ A ∧ A < SIG + 16 + 224 * (c' + 1)) ∨ A = FORW + forOff c' ∨
      A = FORW + forOff c' + 8) : ¬ coordW c A := by
  have h1 : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
  have h2 : forOff c' ≤ 144 := by unfold forOff; split_ifs <;> omega
  have h3 : forOff c ≠ forOff c' ∧ forOff c + 8 ≠ forOff c' ∧ forOff c ≠ forOff c' + 8 := by
    unfold forOff; split_ifs <;> omega
  intro hw
  unfold coordW loopW bodyW treeW slotV slotP at *
  aoh
def coordC (c : Nat) : Nat := fk c + (1 + (1 + (128 * loopStepC + (127 * treeC + (8 + 7 * 13)))))
theorem coordC_le (c : Nat) : coordC c ≤ 13 + (1 + (1 + (128 * loopStepC + (127 * treeC + (8 + 7 * 13))))) := by
  unfold coordC fk; split_ifs <;> omega
theorem field_lt16016 {N : BitVec 256} (hadm : WCT9.admissible N = true) {c : Nat} (hc : c < 9) :
    N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14 < 16016 :=
  ((WCT9.admissible_iff N).1 hadm).2 ⟨c, hc⟩
theorem pcI_seven (c : Nat) (hc : c < 9) : pcI c 7 = if c < 8 then cbase (c + 1) else 10918 := by
  interval_cases c <;> decide
section coord
variable {im : Image} {sk : BitVec 256}
theorem path_copies (hcode : NewCodeAt im) {c sel : Nat} (hc : c < 9) (hsel : sel < 128) {heap : Array Digest} :
    ∀ n, n ≤ 7 → ∀ t : MachineState, t.pc = pcOf (pcI c (7 - n)) → t.getReg .x24 = BitVec.ofNat 64 sel →
      (∀ m, 1 ≤ m → m < 256 → DigAt t (HEAPW + 16 * m) (heap.getD m 0)) →
      ∃ u, Steps im t (13 * n) (13 * n) u ∧ u.pc = pcOf (pcI c 7) ∧
        (∀ l, 7 - n ≤ l → l < 7 → DigAt u (slotP c l) (heap.getD (2 ^ (7 - l) + (sel / 2 ^ l ^^^ 1)) 0)) ∧
        RegsExcept t u [.x6, .x7, .x28, .x29] ∧ Frame t u (fun A => slotP c (7 - n) ≤ A ∧ A < slotP c 7) := by
  intro n
  induction n with
  | zero =>
    intro _ t hpc _ _
    exact ⟨t, Steps.refl t, hpc, fun l h1 h2 => absurd h2 (by omega), RegsExcept.refl _ _, fun A _ _ => rfl⟩
  | succ n ih =>
    intro hn t hpc h24 hheap
    have hl : 7 - (n + 1) < 7 := by omega
    obtain ⟨t1, s1, p1, m0, m8, r1, f1⟩ := step_PC hcode hc hl hsel t hpc h24
    have hph := pathHeap_lt sel (7 - (n + 1)) hsel hl
    have hm := hheap (2 ^ (7 - (7 - (n + 1))) + (sel / 2 ^ (7 - (n + 1)) ^^^ 1)) (by
      have : 1 ≤ 2 ^ (7 - (7 - (n + 1))) := Nat.one_le_two_pow; omega) hph
    have h24' : t1.getReg .x24 = BitVec.ofNat 64 sel := by rw [r1.get (by simp)]; exact h24
    have hheap' : ∀ m, 1 ≤ m → m < 256 → DigAt t1 (HEAPW + 16 * m) (heap.getD m 0) := fun m h1 h2 =>
      (hheap m h1 h2).frame f1 (by ao) (by unfold slotP; intro h; rcases h with h | h <;> aoh)
        (by unfold slotP; intro h; rcases h with h | h <;> aoh)
    obtain ⟨u, su, pu, hu, ru, fu⟩ := ih (by omega) t1 (by rw [p1, show 7 - (n + 1) + 1 = 7 - n by omega]) h24' hheap'
    refine ⟨u, (s1.trans su).of_eq (by ring) (by ring), pu, fun l h1 h2 => ?_, (r1.trans ru).mono (by simp), ?_⟩
    · by_cases hle : 7 - n ≤ l
      · exact hu l hle h2
      · have : l = 7 - (n + 1) := by omega
        subst this
        have hd : DigAt t1 (slotP c (7 - (n + 1))) (heap.getD (2 ^ (7 - (7 - (n + 1))) + (sel / 2 ^ (7 - (n + 1)) ^^^ 1)) 0) :=
          ⟨by rw [m0]; exact hm.1, by rw [m8]; exact hm.2⟩
        exact DigAt.frame hd fu (by unfold slotP; ao) (by unfold slotP; intro h; aoh) (by unfold slotP; intro h; aoh)
    · refine (f1.trans fu).mono (fun A _ hA => ?_)
      unfold slotP at *
      rcases hA with (h | h) | h <;> aoh
theorem getD_map_range7 (f : Nat → Digest) {l : Nat} (hl : l < 7) : ((List.range 7).map f).getD l 0 = f l := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
theorem toArray_getD_high (leaves : List Digest) (m : Nat) (hm : 128 ≤ m) :
    ((List.replicate 128 (0 : Digest) ++ leaves).toArray).getD m 0 = leaves.getD (m - 128) 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append_right (by simp; omega)]
  simp [List.getD_eq_getElem?_getD]
theorem coord_unit (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) {N : BitVec 256}
    (hadm : WCT9.admissible N = true) {s : MachineState} (hpc : s.pc = pcOf (cbase c)) (hg : GlobSt sk N s)
    (state : List WCT9.Opening × List Digest) :
    TBSim im sk s (coordC c) (WCT9.openingStep (N.toNat % 2 ^ 31) N state ⟨c, hc⟩) (fun st t =>
      t.pc = pcOf (pcI c 7) ∧ GlobSt sk N t ∧
        (∃ op root, st = (state.1 ++ [op], state.2 ++ [root]) ∧ OpeningAt t c op ∧ DigAt t (FORW + forOff c) root) ∧
        RegsExcept s t ftsRegs ∧ Frame s t (coordW c)) := by
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hf16 := field_lt16016 hadm hc
  have hsel128 : N.toNat / 2 ^ WCT9.coordBase c % 128 < 128 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t1, s1, p1, x24, x28, r1, f1⟩ := step_F hcode hc s hpc hg.nbuf
  have ht1 : TableAt t1 := fun k hk => by rw [f1.get (by ao) id]; exact hg.table k hk
  obtain ⟨t2, s2, p2, x25, r2, f2⟩ := step_lwu hcode hc t1 p1 (by omega) x28 ht1
  obtain ⟨t3, s3, p3, x18, r3, f3⟩ := step_Z hcode hc t2 p2
  have g3 : ∀ A, A < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [f3.get hA id, f2.get hA id, f1.get hA id]
  have hz : ∀ A, ScrZero A → t3.getMem (BitVec.ofNat 64 A) = 0 := fun A hA => by
    rw [g3 A (by unfold ScrZero at hA; aoh)]; exact hg.zero A hA
  have r13 : RegsExcept s t3 [.x6, .x18, .x24, .x25, .x28] := ((r1.trans r2).trans r3).mono (by simp)
  have hb3 : BodySt sk 0 (N.toNat % 2 ^ 31) (N.toNat / 2 ^ WCT9.coordBase c % 128)
      (pkAt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14)) t3 :=
    ⟨by rw [r13.get (by simp)]; exact hg.x5, x18, by rw [r13.get (by simp)]; exact hg.x22,
      by rw [r3.get (by simp), r2.get (by simp)]; exact x24, by rw [r3.get (by simp)]; exact x25,
      by rw [g3 _ (by ao)]; exact hg.p0, by rw [g3 _ (by ao)]; exact hg.p8, by rw [g3 _ (by ao)]; exact hg.p32,
      by rw [g3 _ (by ao)]; exact hg.p40, hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]),
      hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero]), hz _ (by simp [ScrZero])⟩
  have hword : ∀ i : Fin 7, pkAt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14) / 4 ^ i.val % 4 =
      WCT9.digit (WCT9.rank N ⟨c, hc⟩) i := fun i => pkAt_digit _ hf16 i
  unfold WCT9.openingStep
  dsimp only
  simp only [WCT9.buildCoordinate_factor, bind_assoc, pure_bind]
  refine (TBSim.steps ((s1.trans s2).trans s3) (TBSim.bind (W₂ := 127 * treeC + (8 + 7 * 13))
    (child_loop (word := WCT9.rank N ⟨c, hc⟩) hcode hc hsel128 hidx (by have := pkAt_lt (N.toNat / 2 ^ (WCT9.coordBase c + 7) % 2 ^ 14); omega)
      hword (LoopInv.init p3 hb3)) (fun rows t4 h4 => ?_))).mono (by unfold coordC; omega) (fun _ _ h => h)
  have h4pc : t4.pc = pcOf (nodeI c) := by have := h4.pc; rwa [if_neg (by norm_num)] at this
  have h4b := h4.body
  rw [if_neg (by norm_num)] at h4b
  have g4 : ∀ A, A < 2 ^ 64 → ¬ loopW c A → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA hn => h4.frame.get hA hn
  have h0 : TreeInv c (N.toNat % 2 ^ 31) t4 0 ((List.replicate 128 (0 : Digest) ++ rows.1).toArray) t4 :=
    ⟨by rw [if_pos (by norm_num)]; exact h4pc, h4b.x5, h4b.x18, h4b.x22, by simp [h4.len],
      fun m hm1 hm2 => by
        rw [toArray_getD_high _ _ (by omega)]
        have := h4.leaves (m - 128) (by omega)
        rwa [show 128 + (m - 128) = m by omega] at this,
      by rw [g4 _ (by ao) (by unfold loopW bodyW slotV; intro h; aoh)]; exact hz _ (by simp [ScrZero]),
      by rw [g4 _ (by ao) (by unfold loopW bodyW slotV; intro h; aoh)]; exact hz _ (by simp [ScrZero]),
      RegsExcept.refl _ _, Frame.refl _ _⟩
  refine TBSim.bind (W₂ := 8 + 7 * 13) (tree_loop hcode hc hidx h0) (fun heap t5 h5 => ?_)
  have h5pc : t5.pc = pcOf (rI c) := by have := h5.pc; rwa [if_neg (by norm_num)] at this
  obtain ⟨t6, s6, p6, q0, q8, r6, f6⟩ := step_R0 hcode hc t5 h5pc
  have h24 : t6.getReg .x24 = BitVec.ofNat 64 (N.toNat / 2 ^ WCT9.coordBase c % 128) := by
    rw [r6.get (by simp), h5.regs.get (by simp [treeRegs])]; exact h4b.x24
  have hfo : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
  have hheap6 : ∀ m, 1 ≤ m → m < 256 → DigAt t6 (HEAPW + 16 * m) (heap.getD m 0) := fun m h1 h2 =>
    (h5.heap m (by omega) h2).frame f6 (by ao) (by intro h; rcases h with h | h <;> aoh)
      (by intro h; rcases h with h | h <;> aoh)
  obtain ⟨t7, s7, p7, hpath, r7, f7⟩ := path_copies hcode hc hsel128 7 le_rfl t6 (by rw [p6]) h24 hheap6
  have hregs : RegsExcept s t7 ftsRegs :=
    ((((r13.trans h4.regs).trans h5.regs).trans r6).trans r7).mono (by simp [ftsRegs, bodyRegs, treeRegs])
  have hframe : Frame s t7 (coordW c) := by
    refine (((((f1.trans f2).trans f3).trans h4.frame).trans h5.frame).trans f6 |>.trans f7).mono (fun A _ hA => ?_)
    unfold coordW
    rcases hA with (((((hA | hA) | hA) | hA) | hA) | hA) | hA
    · exact hA.elim
    · exact hA.elim
    · exact hA.elim
    · left; exact hA
    · right; left; exact hA
    · rcases hA with h | h
      · right; right; right; left; exact h
      · right; right; left; exact h
    · right; right; right; right; exact hA
  have hval : ∀ i : Fin 7, DigAt t7 (SIG + 16 + 224 * c + 16 * i.val) (rows.2.getD i.val 0) := fun i => by
    obtain ⟨-, hd⟩ := h4.vals hsel128
    have h1 := hd i.val i.isLt
    unfold slotV at h1
    refine ((h1.frame h5.frame (by ao) ?_ ?_).frame f6 (by ao) ?_ ?_).frame f7 (by ao) ?_ ?_ <;>
      (intro h; (try simp only [treeW, slotP] at h); have := i.isLt; aoh)
  refine TBSim.pure_steps' (s6.trans s7) ⟨p7, GlobSt.frame hc hg hregs (by simp [ftsRegs]) hframe,
    ⟨_, _, rfl, ⟨fun i => hval i, fun l => ?_⟩, ?_⟩, hregs, hframe⟩
  · have hx : N.toNat / 2 ^ WCT9.coordBase c % 128 / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val) := by
      have := pathHeap_lt _ l.val hsel128 l.isLt
      have h2 := pathIdx_eq _ hsel128 l.val l.isLt
      have : (N.toNat / 2 ^ WCT9.coordBase c % 128 + 128) / 2 ^ l.val ^^^ 1 < 2 ^ (7 - l.val + 1) := by
        apply Nat.xor_lt_two_pow
        · rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show 7 - l.val + 1 + l.val = 8 by omega]; omega
        · exact Nat.one_lt_two_pow (by omega)
      rw [pow_succ] at this; omega
    have := hpath l.val (by omega) l.isLt
    unfold slotP at this
    show DigAt t7 (SIG + 128 + 224 * c + 16 * l.val) (((List.range 7).map fun level =>
      ((WCT9.heapLevels heap).getD level []).getD ((WCT9.child N ⟨c, hc⟩).val / 2 ^ level ^^^ 1) 0).getD l.val 0)
    have hcv : (WCT9.child N ⟨c, hc⟩).val = N.toNat / 2 ^ WCT9.coordBase c % 128 := rfl
    rw [getD_map_range7 _ l.isLt, hcv, show ((WCT9.heapLevels heap).getD l.val []).getD _ 0 =
      SigGolfCandidate.T3.Correctness.treeValue (WCT9.heapLevels heap) l.val _ from rfl,
      WCT9.heapLevels_value heap l.val _ (by omega) hx]
    exact this
  · have h1 : DigAt t6 (FORW + forOff c) (heap.getD 1 0) := by
      have := h5.heap 1 (by norm_num) (by norm_num)
      exact ⟨by rw [q0]; exact this.1, by rw [q8]; exact this.2⟩
    rw [show ((WCT9.heapLevels heap).getD 7 []).getD 0 0 = heap.getD 1 0 from
      WCT9.heapLevels_value heap 7 0 (by norm_num) (by norm_num)]
    exact h1.frame f7 (by ao) (by unfold slotP; intro h; aoh) (by unfold slotP; intro h; aoh)
end coord
end ClaudeWCT.W9.Machine.Sign
end

section

set_option linter.unusedSimpArgs false
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Digest header pad64 shortHash)
def coordCmax : Nat := 13 + (1 + (1 + (128 * loopStepC + (127 * treeC + (8 + 7 * 13)))))
def ftsW' (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 2032)
structure FtsInv (sk N : BitVec 256) (s0 : MachineState) (k : Nat) (st : List WCT9.Opening × List Digest)
    (t : MachineState) : Prop where
  pc : t.pc = pcOf (if k < 9 then cbase k else 10918)
  glob : GlobSt sk N t
  len1 : st.1.length = k
  len2 : st.2.length = k
  outs : ∀ c < k, OpeningAt t c (st.1.getD c ⟨fun _ => 0, fun _ => 0⟩) ∧ DigAt t (FORW + forOff c) (st.2.getD c 0)
  regs : RegsExcept s0 t ftsRegs
  frame : Frame s0 t ftsW'
theorem foldlM_finRange9 {α : Type} (f : α → Fin 9 → M α) (init : α) :
    (List.finRange 9).foldlM f init =
      (List.range' 0 9).foldlM (fun st k => if h : k < 9 then f st ⟨k, h⟩ else pure st) init := by
  rw [show List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
    show List.range' 0 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp only [List.foldlM_cons, List.foldlM_nil]
  rfl
theorem OpeningAt.frame {s t : MachineState} {W : Nat → Prop} {c : Nat} {op : WCT9.Opening} (hc : c < 9)
    (h : OpeningAt s c op) (hf : Frame s t W)
    (hW : ∀ A, SIG + 16 + 224 * c ≤ A → A < SIG + 16 + 224 * (c + 1) → ¬ W A) : OpeningAt t c op := by
  refine ⟨fun i => (h.1 i).frame hf (by ao) (hW _ (by omega) (by have := i.isLt; omega))
    (hW _ (by omega) (by have := i.isLt; omega)), fun l => (h.2 l).frame hf (by ao)
      (hW _ (by omega) (by have := l.isLt; omega)) (hW _ (by omega) (by have := l.isLt; omega))⟩
theorem getD_snoc {α : Type} (l : List α) (x d : α) (n : Nat) :
    (l ++ [x]).getD n d = if n < l.length then l.getD n d else if n = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp
section fts
variable {im : Image} {sk : BitVec 256}
theorem fts_step (hcode : NewCodeAt im) {N : BitVec 256} (hadm : WCT9.admissible N = true) {s0 : MachineState}
    (k : Nat) (hk : k < 9) (st : List WCT9.Opening × List Digest) (t : MachineState) (h : FtsInv sk N s0 k st t) :
    TBSim im sk t coordCmax
      ((fun st k => if h : k < 9 then WCT9.openingStep (N.toNat % 2 ^ 31) N st ⟨k, h⟩ else pure st) st (0 + k))
      (FtsInv sk N s0 (k + 1)) := by
  simp only [Nat.zero_add, dif_pos hk]
  have hpc : t.pc = pcOf (cbase k) := by rw [h.pc, if_pos hk]
  refine (coord_unit hcode hk hadm hpc h.glob st).mono (coordC_le k) (fun st' u hu => ?_)
  obtain ⟨upc, ug, ⟨op, root, rfl, hop, hroot⟩, uregs, uframe⟩ := hu
  have hfo : forOff k ≤ 144 := by unfold forOff; split_ifs <;> omega
  refine ⟨?_, ug, by simp [h.len1], by simp [h.len2], fun c hc => ?_, (h.regs.trans uregs).mono (by simp),
    (h.frame.trans uframe).mono (fun A _ hA => ?_)⟩
  · rw [upc, pcI_seven k hk]
    by_cases h8 : k < 8
    · rw [if_pos h8, if_pos (by omega)]
    · rw [if_neg h8, if_neg (by omega)]
  · rw [getD_snoc, getD_snoc, h.len1, h.len2]
    by_cases hck : c < k
    · rw [if_pos hck, if_pos hck]
      obtain ⟨o1, o2⟩ := h.outs c hck
      have hfo' : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
      exact ⟨o1.frame (by omega) uframe (fun A h1 h2 => coordW_other hk (by omega) (by omega) (Or.inl ⟨h1, h2⟩)),
        o2.frame uframe (by ao) (coordW_other hk (by omega) (by omega) (Or.inr (Or.inl rfl)))
          (coordW_other hk (by omega) (by omega) (Or.inr (Or.inr rfl)))⟩
    · have : c = k := by omega
      subst this
      rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos rfl, if_pos rfl]
      exact ⟨hop, hroot⟩
  · rcases hA with hA | hA
    · exact hA
    · unfold ftsW'
      unfold coordW loopW bodyW treeW slotV slotP at hA
      aoh
end fts
theorem hashInput_forest (t : MachineState) {index : Nat} (roots : List Digest) (hlen : roots.length = 9)
    (hidx : index < 2 ^ 32) (h10 : t.getReg .x10 = BitVec.ofNat 64 FORW) (h11 : t.getReg .x11 = BitVec.ofNat 64 192)
    (hr : ∀ c < 9, DigAt t (FORW + forOff c) (roots.getD c 0))
    (m16 : t.getMem (BitVec.ofNat 64 (FORW + 16)) = BitVec.ofNat 64 3841)
    (m24 : t.getMem (BitVec.ofNat 64 (FORW + 24)) = BitVec.ofNat 64 index)
    (z : ∀ k < 4, t.getMem (BitVec.ofNat 64 (FORW + 160 + 8 * k)) = 0) :
    hashInput t = toQ (pad64 (forestIn index roots)) := by
  refine hashInput_of_words t _ 2 FORW (by rw [pad64_forest _ _ hlen]; simp [forestIn_len _ _ hlen]) h10 (by ao)
    (by ao) h11 ?_
  rw [wordsOf_forest index roots hlen hidx]
  match roots, hlen with
  | [r0, r1, r2, r3, r4, r5, r6, r7, r8], _ =>
    have d0 := hr 0 (by norm_num); have d1 := hr 1 (by norm_num); have d2 := hr 2 (by norm_num)
    have d3 := hr 3 (by norm_num); have d4 := hr 4 (by norm_num); have d5 := hr 5 (by norm_num)
    have d6 := hr 6 (by norm_num); have d7 := hr 7 (by norm_num); have d8 := hr 8 (by norm_num)
    have z0 := z 0 (by norm_num); have z1 := z 1 (by norm_num); have z2 := z 2 (by norm_num)
    have z3 := z 3 (by norm_num)
    simp only [forOff, List.getD_cons_zero, List.getD_cons_succ, if_true, Nat.add_zero,
      show (1 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 0 by decide,
      show (4 : Nat) ≠ 0 by decide, show (5 : Nat) ≠ 0 by decide, show (6 : Nat) ≠ 0 by decide,
      show (7 : Nat) ≠ 0 by decide, show (8 : Nat) ≠ 0 by decide, if_false] at d0 d1 d2 d3 d4 d5 d6 d7 d8
    intro k hk
    interval_cases k <;> simp only [List.getD_cons_zero, List.drop_succ_cons, List.drop_zero, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, wordsOf_bytesLE16, List.cons_append, List.nil_append,
      List.getD_cons_succ, List.getD_cons_zero]
    · exact d0.1
    · exact d0.2
    · exact m16
    · exact m24
    · exact d1.1
    · exact d1.2
    · exact d2.1
    · exact d2.2
    · exact d3.1
    · exact d3.2
    · exact d4.1
    · exact d4.2
    · exact d5.1
    · exact d5.2
    · exact d6.1
    · exact d6.2
    · exact d7.1
    · exact d7.2
    · exact d8.1
    · exact d8.2
    · exact z0
    · exact z1
    · exact z2
    · exact z3
theorem ftsC_bound : 11 + (9 * coordCmax + (11 + (8 * 3 + (1 + 0)))) ≤ ftsC := by
  unfold coordCmax loopStepC childC pairC chainC treeC ftsC; norm_num
section fts2
variable {im : Image}
theorem ftsGood (im : Image) : FtsGood im := by
  intro hcode sk N s hpre
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  obtain ⟨t0, s0', p0, k1, k2, r0, f0⟩ := step_SK hcode s hpre.pc
  have g0 : ∀ A, A < 2 ^ 64 → A ≠ PRIVW + 40 → A ≠ PRIVW + 32 → A ≠ PRIVW + 8 → A ≠ PRIVW →
      t0.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 h3 h4 =>
    f0.get hA (by simp [h1, h2, h3, h4])
  have hg0 : GlobSt sk N t0 :=
    { x5 := by rw [r0.get (by simp)]; exact hpre.x5
      x22 := by rw [r0.get (by simp)]; exact hpre.x22
      nbuf := fun k hk => by rw [g0 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hpre.nbuf k hk
      table := fun k hk => by rw [g0 _ (by ao) (by ao) (by ao) (by ao) (by ao)]; exact hpre.table k hk
      p0 := by have := k1 0 (by norm_num); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
               exact hpre.sk 0 (by norm_num)
      p8 := by have := k1 1 (by norm_num); simp only [Nat.mul_one] at this; rw [this]; exact hpre.sk 1 (by norm_num)
      p32 := by have := k2 0 (by norm_num); simp only [Nat.mul_zero, Nat.add_zero] at this; rw [this]
                exact hpre.sk 2 (by norm_num)
      p40 := by have := k2 1 (by norm_num); simp only [Nat.mul_one] at this; rw [this]
                rw [show SK + 16 + 8 = SK + 8 * 3 from rfl]; exact hpre.sk 3 (by norm_num)
      zero := fun A hA => by
        rw [g0 _ (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh)
          (by unfold ScrZero at hA; aoh) (by unfold ScrZero at hA; aoh)]
        exact hpre.zero A hA }
  have hinv0 : FtsInv sk N s 0 ([], []) t0 :=
    ⟨by rw [if_pos (by norm_num)]; exact p0, hg0, rfl, rfl, fun c hc => absurd hc (by omega),
      r0.mono (by simp [ftsRegs]), f0.mono (fun A _ hA => by unfold ftsW'; left; rcases hA with h | h | h | h <;> aoh)⟩
  unfold WCT9.signForest WCT9.forestRows
  rw [foldlM_finRange9]
  refine (TBSim.steps s0' (TBSim.bind (W₂ := 11 + (8 * 3 + (1 + 0)))
    (TBSim.foldlM_range' 0 9 _ _ (FtsInv sk N s) coordCmax (fun k hk st t ht => fts_step hcode hpre.adm k hk st t ht)
      hinv0) (fun st t9 h9 => ?_))).mono ftsC_bound (fun _ _ h => h)
  have h9pc : t9.pc = pcOf 10918 := by have := h9.pc; rwa [if_neg (by norm_num)] at this
  obtain ⟨t1, s1, e1, p1, x10, x11, x12, m16, m24, r1, f1⟩ := step_For hcode t9 h9pc h9.glob.x22
  have g1 : ∀ A, A < 2 ^ 64 → A ≠ FORW + 24 → A ≠ FORW + 16 →
      t1.getMem (BitVec.ofNat 64 A) = t9.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 =>
    f1.get hA (by simp [h1, h2])
  have hq : hashInput t1 = toQ (pad64 (forestIn (N.toNat % 2 ^ 31) st.2)) := by
    refine hashInput_forest t1 st.2 h9.len2 (by omega) x10 x11 (fun c hc => ?_) m16 m24 (fun k hk => ?_)
    · have hfo : forOff c ≤ 144 := by unfold forOff; split_ifs <;> omega
      have hfo' : forOff c ≠ 16 ∧ forOff c ≠ 24 ∧ forOff c + 8 ≠ 16 ∧ forOff c + 8 ≠ 24 := by
        unfold forOff; split_ifs <;> omega
      exact (h9.outs c hc).2.frame f1 (by ao) (by intro h; rcases h with h | h <;> omega)
        (by intro h; rcases h with h | h <;> omega)
    · rw [g1 _ (by ao) (by ao) (by ao)]
      exact h9.glob.zero _ (by unfold ScrZero; interval_cases k <;> simp)
  have hx5 : t1.getReg .x5 = 0 := by rw [r1.get (by simp)]; exact h9.glob.x5
  have hbl : (toQ (pad64 (forestIn (N.toNat % 2 ^ 31) st.2))).blocks = 3 := by
    rw [pad64_forest _ _ h9.len2, blocks_toQ ⟨by simp [forestIn_len _ _ h9.len2], by simp [forestIn_len _ _ h9.len2]⟩]
    simp [forestIn_len _ _ h9.len2]
  rw [forestPk_eq]
  refine (TBSim.steps s1 (TBSim.shortHash_bind' (W := 1 + 0) (f := fun root => pure (st.1, root)) e1 hx5
    (hashArgs_const t1 FORW 192 FOUT x10 x11 x12 (by ao) (by norm_num) (by ao) (by ao) (by ao)) hq
    (fun a => ?_))).mono (by rw [hbl]) (fun _ _ h => h)
  have fh := Frame.writeHash t1 a FOUT x12 (by ao)
  obtain ⟨t2, s2, p2, r2, f2⟩ := step_J hcode (writeHash t1 a) (by rw [pc_writeHash, p1, pcOf_add4])
  have hroot := DigAt.writeHash_lo t1 a FOUT x12 (by ao)
  refine TBSim.pure_steps' s2 ⟨p2, ?_, ?_, h9.len1, fun k hk => ?_, ?_, ?_⟩
  · rw [r2.get (by simp), getReg_writeHash]; exact hx5
  · exact hroot.frame f2 (by ao) id id
  · refine (((h9.outs k hk).1.frame hk f1 (fun A h1 h2 => ?_)).frame hk fh (fun A h1 h2 => ?_)).frame hk f2
      (fun A _ _ h => h)
    · intro h; rcases h with h | h <;> aoh
    · intro h; aoh
  · exact (h9.regs.trans ((r1.trans (fun x _ => getReg_writeHash t1 a x : RegsExcept t1 (writeHash t1 a) [])).trans
      r2)).mono (by simp [ftsRegs])
  · refine (((h9.frame.trans f1).trans fh).trans f2).mono (fun A _ hA => ?_)
    unfold FtsW
    unfold ftsW' at hA
    rcases hA with ((hA | hA) | hA) | hA
    · rcases hA with hA | hA
      · left; exact hA
      · right; left; exact hA
    · left; rcases hA with h | h <;> constructor <;> aoh
    · right; right; exact hA
    · exact hA.elim
end fts2
end ClaudeWCT.W9.Machine.Sign
end
