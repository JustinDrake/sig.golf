import SigGolfCandidate.T3M.Verify.CanonicalQuery

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

def pendHeap : Pending → Nat
  | .leaf _ g => 2048+g
  | .merge heap _ => heap

def PendingMatch (F : FCtx) (c : Nat) (p : BlockPlan) : Pending → Prop
  | .leaf s g => ∃ j, p.leaf=some j ∧ j<3 ∧ s=3*c+j ∧ g=F.g s
  | .merge heap _ => p.leaf=none ∧ p.depth+1 ≤ 2 ∧ heap<2048

def PendingPayload (p : BlockPlan) (node : Digest) (s : MachineState) : Pending → Prop
  | .leaf _ _ => True
  | .merge _ left => DigAt s (frame (p.depth+1)) left ∧
      DigAt s (frame (p.depth+1)+48) node

theorem pending_match_addr (F : FCtx) (c : Nat) (p : BlockPlan) (pend : Pending)
    (hm : PendingMatch F c p pend) :
    pendingAddr p (WIT+64+144*c)=pendAddr p.depth pend := by
  cases pend with
  | leaf slot g =>
    obtain ⟨j,hj,hj3,hs,hg⟩ := hm
    simp only [pendingAddr,hj,pendAddr,hs]
    omega
  | merge heap left => simp [pendingAddr,hm.1,pendAddr,frame,frameA]

theorem WitF.pending_frame (F : FCtx) (c : Nat) (p : BlockPlan) (pend : Pending)
    (ptr side : Nat) (s t : MachineState)
    (hm : PendingMatch F c p pend) (hc : c<7) (hp : 1088 ≤ ptr)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c))
    (hr : RawRes (pendingSpec p side) pendingKeep s t) (hw : WitF F.w ptr s) :
    WitF F.w ptr t := by
  intro k hk ho
  rw [hr.pending_frame _ _ h19]
  · exact hw k hk ho
  all_goals
    apply ofNat_ne (by unfold WIT WX at *; omega)
      (by cases pend with
          | leaf slot g =>
            obtain ⟨j,hj,hj3,hs,hg⟩ := hm
            simp only [pendingAddr,hj]; unfold WIT; omega
          | merge heap left => have hdepth := hm.2.1
                               simp only [pendingAddr,hm.1]; unfold frame; omega)
    cases pend with
    | leaf slot g =>
      obtain ⟨j,hj,hj3,hs,hg⟩ := hm
      simp only [pendingAddr,hj]
      unfold leafNT at ho
      omega
    | merge heap left =>
      simp only [pendingAddr,hm.1]
      unfold frame WIT
      have hd := hm.2.1
      omega

theorem pending_typed (F : FCtx) (c : Nat) (p : BlockPlan) (pend : Pending)
    (node : Digest) (side : Nat) (s t : MachineState)
    (hm : PendingMatch F c p pend) (hc : c<7)
    (hr : RawRes (pendingSpec p side) pendingKeep s t)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c))
    (hh : (pendingHeap p).eval s=FtsRev.rv (pendHeap pend))
    (h27 : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx))
    (hd : PendingPayload p node s pend) : PendOK F c p.depth node t pend := by
  have haddr := pending_match_addr F c p pend hm
  have h10 := hr.pending_src _ h19
  rw [haddr] at h10
  have hpa64 : pendingAddr p (WIT+64+144*c)+64<2^64 := by
    cases pend with
    | leaf slot g =>
      obtain ⟨j,hj,hj3,hs,hg⟩ := hm
      simp only [pendingAddr,hj]; unfold WIT; omega
    | merge heap left => have hdepth := hm.2.1
                         simp only [pendingAddr,hm.1]; unfold frame; omega
  have hhdr := hr.pending_header _ h19 (by omega)
  have hframe : ∀ off, off=0 ∨ off=8 ∨ off=48 ∨ off=56 →
      t.getMem (BitVec.ofNat 64 (pendingAddr p (WIT+64+144*c)+off))=
        s.getMem (BitVec.ofNat 64 (pendingAddr p (WIT+64+144*c)+off)) := by
    intro off hoff
    apply hr.pending_frame _ _ h19
    all_goals
      apply ofNat_ne (by rcases hoff with rfl | rfl | rfl | rfl <;> omega) (by omega)
      rcases hoff with rfl | rfl | rfl | rfl <;> omega
  cases pend with
  | leaf slot g =>
    obtain ⟨j,hj,hj3,hs,hg⟩ := hm
    simp only [hj,Option.isSome_some,if_true,h28,hh,pendHeap] at hhdr
    have h0 : pendingAddr p (WIT+64+144*c)+16=leafT slot := by
      simp only [pendingAddr,hj,hs,leafT]; omega
    have h1 : pendingAddr p (WIT+64+144*c)+24=leafT slot+8 := by
      simp only [pendingAddr,hj,hs,leafT]; omega
    rw [h0,h1] at hhdr
    exact ⟨by omega,by omega,hg,h10,hhdr.1,hhdr.2⟩
  | merge heap left =>
    simp only [hm.1,Option.isSome_none,Bool.false_eq_true,if_false,h27,hh,pendHeap] at hhdr
    have hbase : pendingAddr p (WIT+64+144*c)=frameA (p.depth+1) := by
      simp [pendingAddr,hm.1,frame,frameA]
    rw [hbase] at hhdr hframe
    refine ⟨hm.2.1,hm.2.2,h10,?_,hhdr.1,hhdr.2,?_⟩
    · obtain ⟨h0,h8⟩ := hd.1
      exact ⟨(by simpa using (hframe 0 (by simp)).trans h0),
        (hframe 8 (by simp)).trans h8⟩
    · obtain ⟨h48,h56⟩ := hd.2
      exact ⟨(hframe 48 (by simp)).trans h48,
        (by simpa [Nat.add_assoc] using (hframe 56 (by simp)).trans h56)⟩

theorem scheduled_pending_query (F : FCtx) (c g j ptr : Nat) (pend : Pending)
    (node : Digest) (s : MachineState)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr) (hpx : ptr<WX) (hp8 : ptr%8=0)
    (hm : PendingMatch F c (plan g j) pend)
    (hpc : s.pc=pcOf (plan g j).start)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c))
    (hh : (pendingHeap (plan g j)).eval s=FtsRev.rv (pendHeap pend))
    (h27 : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx))
    (h28 : s.getReg .x28=BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx))
    (h11 : s.getReg .x11=64#64)
    (hs : ∀ k, (plan g j).leaf=some k → accessValid (s.getReg (slotReg k)) 8=true)
    (hd : PendingPayload (plan g j) node s pend) (hw : WitF F.w ptr s)
    (hpad : ∀ d, 1 ≤ d → d ≤ 2 → s.getMem (BitVec.ofNat 64 (frameA d+32))=0 ∧
      s.getMem (BitVec.ofNat 64 (frameA d+40))=0) :
    ∃ t, RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t ∧
      hashInput t=toQ (T3.pad64 (pendBlk F c node pend)) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  obtain ⟨t,ht⟩ := pending_run g j (pendHeap pend%2) hg hj (Nat.mod_lt _ (by decide)) s hpc
    (pending_br_holds _ s _ hh)
    (pending_access _ s c hc (by intro k hk; exact hb.2.2.2.1 k hk) h19 hs)
  have htyped := pending_typed F c _ pend node _ s t hm hc ht h19 hh h27 h28 hd
  have h11t : t.getReg .x11=64#64 := (ht.keep .x11 (by simp [pendingKeep])).trans h11
  have hpadt : ∀ d, 1 ≤ d → d ≤ 2 → t.getMem (BitVec.ofNat 64 (frameA d+32))=0 ∧
      t.getMem (BitVec.ofNat 64 (frameA d+40))=0 := by
    intro d hd1 hd2
    obtain ⟨z0,z1⟩ := hpad d hd1 hd2
    have hf : ∀ off, off=32 ∨ off=40 → t.getMem (BitVec.ofNat 64 (frameA d+off))=
        s.getMem (BitVec.ofNat 64 (frameA d+off)) := by
      intro off hoff
      apply ht.pending_frame _ _ h19
      all_goals
        apply ofNat_ne (by unfold frameA; rcases hoff with rfl | rfl <;> omega)
          (by cases hp : (plan g j).leaf with
              | none => simp only [pendingAddr,hp]; unfold frame; omega
              | some k => have hk := hb.2.2.2.1 k hp
                          simp only [pendingAddr,hp]; unfold WIT; omega)
        cases hp : (plan g j).leaf with
        | none => simp only [pendingAddr,hp]; unfold frame frameA
                  rcases hoff with rfl | rfl <;> omega
        | some k => simp only [pendingAddr,hp]; unfold frameA WIT
                    rcases hoff with rfl | rfl <;> omega
    exact ⟨(hf 32 (by simp)).trans z0,(hf 40 (by simp)).trans z1⟩
  have h10 : t.getReg .x10=BitVec.ofNat 64 (pendAddr (plan g j).depth pend) := by
    rw [ht.pending_src _ h19,pending_match_addr F c _ pend hm]
  exact ⟨t,ht,pending_hashInput_general F c _ node pend t t htyped
    (WitF.pending_frame F c _ pend ptr _ s t hm hc hp h19 ht hw) hc hpadt
    (fun _ => rfl) h10 h11t⟩

#print axioms scheduled_pending_query
end SigGolfCandidate.T3M.CanonicalNative
