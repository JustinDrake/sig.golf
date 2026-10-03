import SigGolfCandidate.T3M.Verify.CanonicalBankInvariants

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def bankK (F : FCtx) (c : Nat) : List (Reg × Word) :=
  [(.x1,pcOf (banks[c]!+13)),(.x2,0x1000000),(.x5,0),(.x8,3),(.x9,4),(.x13,5),
    (.x11,64),(.x19,BitVec.ofNat 64 (WIT+64+144*c)),(.x20,0xfef000),(.x21,0xfef400),
    (.x22,BitVec.ofNat 64 F.idx),(.x24,BitVec.ofNat 64 (ETAB+24*c)),
    (.x25,BitVec.ofNat 64 (forestSlot c)),(.x27,BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)),
    (.x28,BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx)),(.x29,BitVec.ofNat 64 A4_LIMIT),(.x31,0x10000),
    (.x16,BitVec.ofNat 64 (TAB+8*F.g (3*c))),
    (.x17,BitVec.ofNat 64 (TAB+8*F.g (3*c+1))),
    (.x18,BitVec.ofNat 64 (TAB+8*F.g (3*c+2)))]

theorem bankK_keep (F : FCtx) (c : Nat) : ∀ p∈bankK F c, p.1∈pendingKeep := by
  intro p hp
  simp only [bankK,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pendingKeep]

theorem FrameMark.bankKnown {F c g j ptr initial s}
    (h : FrameMark (plan g j) c ptr initial s) (hk : KnownOK (bankK F c) initial) :
    KnownOK (bankK F c) s := by
  intro p hp
  rw [h.regs p.1 (bankK_keep F c p hp)]; exact hk p hp

theorem bankKnown_slot (F : FCtx) (c k : Nat) (s : MachineState)
    (h : KnownOK (bankK F c) s) (hk : k<3) :
    s.getReg (slotReg k)=BitVec.ofNat 64 (TAB+8*F.g (3*c+k)) := by
  rcases (show k=0 ∨ k=1 ∨ k=2 by omega) with rfl | rfl | rfl
  · simpa [slotReg] using h (.x16,BitVec.ofNat 64 (TAB+8*F.g (3*c))) (by simp [bankK])
  · simpa [slotReg] using h (.x17,BitVec.ofNat 64 (TAB+8*F.g (3*c+1))) (by simp [bankK])
  · simpa [slotReg] using h (.x18,BitVec.ofNat 64 (TAB+8*F.g (3*c+2))) (by simp [bankK])

def bankPend (F : FCtx) (c : Nat) (p : BlockPlan) (nodes : List Digest) (heap : Nat) : Pending :=
  match p.leaf with
  | some k => .leaf (3*c+k) (F.g (3*c+k))
  | none => .merge (heap/2) (nodes.getD p.depth 0)

def nextNodes (p : BlockPlan) (nodes : List Digest) (node : Digest) : List Digest :=
  if p.variant=1 then nodes.take p.depth++[node] else nodes.take p.depth

structure BankAt (F : FCtx) (c g j ptr : Nat) (nodes : List Digest) (node : Digest)
    (heap : Nat) (s : MachineState) : Prop where
  pc : s.pc=pcOf (plan g j).start
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  known : KnownOK (bankK F c) s
  common : Common F s
  stack : FrameNodes nodes s
  depth : nodes.length=inDepth (plan g j)
  current : (plan g j).leaf=none → DigAt s (frameA ((plan g j).depth+1)+48) node
  rev : (plan g j).leaf=none → s.getReg .x23=FtsRev.rv heap
  heapBound : heap<4096
  orig : WitF F.w ptr s

theorem BankAt.pending {F c g j ptr nodes node heap s}
    (h : BankAt F c g j ptr nodes node heap s) (hc : c<7) (hg : g<42) (hj : j<5) :
    PendingMatch F c (plan g j) (bankPend F c (plan g j) nodes heap) ∧
      PendingReady F c (plan g j) ptr (bankPend F c (plan g j) nodes heap) node s ∧
      pendHeap (bankPend F c (plan g j) nodes heap)<4096 ∧
      (∀ k, (plan g j).leaf=some k → accessValid (s.getReg (slotReg k)) 8=true) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  have hl := plan_links ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb hl
  have h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c) := h.known
    (.x19,BitVec.ofNat 64 (WIT+64+144*c)) (by simp [bankK])
  have h27 : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) := h.known
    (.x27,BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)) (by simp [bankK])
  have h28 : s.getReg .x28=BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx) := h.known
    (.x28,BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx)) (by simp [bankK])
  have h11 : s.getReg .x11=64#64 := h.known (.x11,64#64) (by simp [bankK])
  have h5 : s.getReg .x5=0 := h.known (.x5,0#64) (by simp [bankK])
  have h25 : s.getReg .x25=BitVec.ofNat 64 (forestSlot c) := h.known
    (.x25,BitVec.ofNat 64 (forestSlot c)) (by simp [bankK])
  cases hp : (plan g j).leaf with
  | some k =>
    have hk3 := hb.2.2.2.1 k hp
    have hslot : 3*c+k<21 := by omega
    have hglobal := F.g_lt _ hslot
    have hr : (pendingHeap (plan g j)).eval s=FtsRev.rv (2048+F.g (3*c+k)) := by
      simp only [pendingHeap,hp,E.eval,bankKnown_slot F c k s h.known hk3]
      exact h.common.glob.2.2.2.2.2.tab _ hglobal
    have hslots : ∀ i, (plan g j).leaf=some i → accessValid (s.getReg (slotReg i)) 8=true := by
      intro i hi
      have hi3 := hb.2.2.2.1 i hi
      rw [bankKnown_slot F c i s h.known hi3]
      apply accessValid_ofNat
      · have hiG := F.g_lt (3*c+i) (by omega)
        unfold TAB; omega
      · unfold TAB; omega
    refine ⟨?_,?_,?_,by simpa only [hp] using hslots⟩
    · simp only [bankPend,hp,PendingMatch]
      refine ⟨k,?_,hk3,?_,?_⟩ <;> first | rfl | trivial
    · simp only [bankPend,hp]
      exact ⟨h.pc,h.pointer,h19,hr,h27,h28,h11,h5,h25,by trivial,h.orig⟩
    · simp only [bankPend,hp,pendHeap]; omega
  | none =>
    have hd := hl.1 hp
    have hlen : nodes.length=(plan g j).depth+1 := by
      simpa [inDepth,hp] using h.depth
    have hr : (pendingHeap (plan g j)).eval s=FtsRev.rv (heap/2) := by
      simp only [pendingHeap,hp,shifted,E.eval,cE,h.rev hp]
      exact FtsRev.rv_sll1 heap (by have := h.heapBound; omega)
    refine ⟨?_,?_,?_,?_⟩
    · simp only [bankPend,hp,PendingMatch]
      exact ⟨by trivial,by omega,by have := h.heapBound; omega⟩
    · simp only [bankPend,hp]
      refine ⟨h.pc,h.pointer,h19,hr,h27,h28,h11,h5,h25,?_,h.orig⟩
      exact ⟨h.stack _ (by omega),by simpa [frame,frameA] using h.current hp⟩
    · simp only [bankPend,hp,pendHeap]; have := h.heapBound; omega
    · intro k hk; contradiction

#print axioms BankAt.pending
end SigGolfCandidate.T3M.CanonicalNative
