import SigGolfCandidate.T3M.Verify.CanonicalPending
import SigGolfCandidate.T3M.Verify.CanonicalRungTransition

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

theorem pending_hash_next : ∀ (g : Fin 42) (j : Fin 5) (side : Fin 2),
    0<(plan g.val j.val).folds →
      atHash (plan g.val j.val) side.val 0+1=atRung (plan g.val j.val) side.val 0 :=
  by decide +kernel

structure PendingReady (F : FCtx) (c : Nat) (p : BlockPlan) (ptr : Nat)
    (pend : Pending) (node : Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf p.start
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  leafbase : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c)
  rev : (pendingHeap p).eval s=FtsRev.rv (pendHeap pend)
  hdr : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)
  leafhdr : s.getReg .x28=BitVec.ofNat 64 (hdr1 (leafW0 c) F.idx)
  bytes : s.getReg .x11=64#64
  hash : s.getReg .x5=0
  forest : s.getReg .x25=BitVec.ofNat 64 (forestSlot c)
  payload : PendingPayload p node s pend
  orig : WitF F.w ptr s

theorem pending_query_dest (F : FCtx) (c g j ptr : Nat) (pend : Pending) (node : Digest)
    (s t : MachineState) (h : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hg : g<42) (hj : j<5) :
    t.getReg .x12=BitVec.ofNat 64 (if (plan g j).folds=0 then
      destA c (plan g j).variant (plan g j).depth
      else WIT+fblk ptr 0+48*(pendHeap pend%2)) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  rw [hr.regs (.x12,if (plan g j).folds=0 then dest (plan g j)
      else rAdd .x14 (BitVec.ofNat 64 (8+48*(pendHeap pend%2)))) (by simp [pendingSpec])]
  split_ifs with ha
  · exact dest_eval _ s c h.forest hb.2.2.1
  · simp only [rAdd,addC_eval,E.eval,h.pointer,BitVec.ofNat_add_ofNat]
    congr 1; unfold fblk; omega

theorem pending_hash_valid (F : FCtx) (c g j ptr : Nat) (pend : Pending) (node : Digest)
    (s t : MachineState) (h : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : ptr+888 ≤ 32168) (hp8 : ptr%8=0)
    (hm : PendingMatch F c (plan g j) pend) : hashArgumentsValid t=true := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h10 := hr.pending_src _ h.leafbase
  rw [pending_match_addr F c _ pend hm] at h10
  have h11 : t.getReg .x11=64#64 := (hr.keep .x11 (by simp [pendingKeep])).trans h.bytes
  have h12 := pending_query_dest F c g j ptr pend node s t h hr hg hj
  have hsrc : pendAddr (plan g j).depth pend+64 ≤ 2^24 ∧
      pendAddr (plan g j).depth pend%8=0 := by
    cases pend with
    | leaf slot g =>
      obtain ⟨k,hk,hk3,hslot,hg⟩ := hm
      simp only [pendAddr,hslot]; unfold WIT; omega
    | merge heap left =>
      have hd := hm.2.1
      simp only [pendAddr]; unfold frameA; omega
  by_cases hzero : (plan g j).folds=0
  · rw [if_pos hzero] at h12
    have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
      (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
    apply hashArgs_of t _ 64 _ h10 h11 h12 hsrc.2 (by decide) hsrc.1
    · unfold destA frameA forestSlot; split_ifs <;> omega
    · have := hd.2.2.2.2.2; unfold WIT at this; omega
  · rw [if_neg hzero] at h12
    apply hashArgs_of t _ 64 _ h10 h11 h12 hsrc.2 (by decide) hsrc.1
    · unfold WIT fblk; omega
    · have hs := Nat.mod_lt (pendHeap pend) (by decide : 0<2)
      unfold WIT fblk; omega

theorem pending_advance (F : FCtx) (c g j ptr : Nat) (pend : Pending) (node : Digest)
    (s t : MachineState) (answer : HashOutput)
    (h : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hn : 0<(plan g j).folds)
    (hp : 1088 ≤ ptr) (hpmax : ptr+888 ≤ 32168)
    (hm : PendingMatch F c (plan g j) pend) :
    RungReady F c (plan g j) ptr 0 (pendHeap pend) (answer.extractLsb' 0 128)
      (writeHash t answer) := by
  have h12 := pending_query_dest F c g j ptr pend node s t h hr hg hj
  rw [if_neg (by omega)] at h12
  have hout : pendHeap pend%2<2 := Nat.mod_lt _ (by decide)
  have hw := WitF.pending_frame F c _ pend ptr _ s t hm hc hp h.leafbase hr h.orig
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [writeHash_pc,hr.pc rfl,pcOf_add4]
    exact congrArg pcOf (pending_hash_next ⟨g,hg⟩ ⟨j,hj⟩ ⟨pendHeap pend%2,hout⟩ hn)
  · rw [writeHash_getReg,hr.pending_pointer _ h.pointer]
    try (congr 1 <;> omega)
  · rw [writeHash_getReg]; exact hr.pending_heap _ h.rev
  · rw [writeHash_getReg,hr.keep .x27 (by simp [pendingKeep])]; exact h.hdr
  · rw [writeHash_getReg,hr.keep .x11 (by simp [pendingKeep])]; exact h.bytes
  · rw [writeHash_getReg,hr.keep .x5 (by simp [pendingKeep])]; exact h.hash
  · rw [writeHash_getReg,hr.keep .x25 (by simp [pendingKeep])]; exact h.forest
  · exact DigAt.writeHash_lo t answer _ h12 (by unfold WIT fblk; omega)
  · intro k hk ho
    have ha : WIT+8*k+8 ≤ WIT+fblk ptr 0+48*(pendHeap pend%2) ∨
        WIT+fblk ptr 0+48*(pendHeap pend%2)+32 ≤ WIT+8*k := by
      unfold fblk leafNT at ho; unfold fblk
      rcases Nat.mod_two_eq_zero_or_one (pendHeap pend) with he | he <;>
        rw [he] at ho ⊢ <;> omega
    rw [writeHash_frame t answer _ _ h12 (by unfold WIT WX at *; omega)
      (by unfold WIT fblk; omega) ha]
    apply hw k hk
    rcases ho with ho | ho | ho | ho | ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr (Or.inl ho)
    all_goals exact Or.inr (Or.inr (by unfold fblk at *; omega))

theorem pending_finish (F : FCtx) (c g j ptr : Nat) (pend : Pending) (node : Digest)
    (s t : MachineState) (answer : HashOutput)
    (h : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hn : (plan g j).folds=0)
    (hp : 1088 ≤ ptr) (hpmax : ptr+888 ≤ 32168)
    (hm : PendingMatch F c (plan g j) pend) :
    SegmentEnd F c (plan g j) (ptr+8) (pendHeap pend) (answer.extractLsb' 0 128)
      (writeHash t answer) ∧
      (writeHash t answer).pc=pcOf (atHash (plan g j) (pendHeap pend%2) (plan g j).folds+1) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h12 := pending_query_dest F c g j ptr pend node s t h hr hg hj
  rw [if_pos hn] at h12
  have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
    (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
  have dlow := hd.2.2.2.2.2
  have hw := WitF.pending_frame F c _ pend ptr _ s t hm hc hp h.leafbase hr h.orig
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [writeHash_getReg,hr.pending_pointer _ h.pointer,hn]
    try (congr 1 <;> omega)
  · rw [writeHash_getReg]; exact hr.pending_heap _ h.rev
  · rw [writeHash_getReg,hr.keep .x27 (by simp [pendingKeep])]; exact h.hdr
  · rw [writeHash_getReg,hr.keep .x11 (by simp [pendingKeep])]; exact h.bytes
  · rw [writeHash_getReg,hr.keep .x5 (by simp [pendingKeep])]; exact h.hash
  · rw [writeHash_getReg,hr.keep .x25 (by simp [pendingKeep])]; exact h.forest
  · exact DigAt.writeHash_lo t answer _ h12 hd.2.2.1
  · intro k hk ho
    rw [writeHash_frame t answer _ _ h12 (by unfold WIT WX at *; omega)
      (by have := hd.2.2.1; omega) (Or.inr (by unfold WIT at *; omega))]
    apply hw k hk
    rcases ho with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr (by omega))
  · rw [writeHash_pc,hr.pc rfl,pcOf_add4,hn]
    rfl

#print axioms pending_advance
#print axioms pending_finish
#print axioms pending_hash_valid
end SigGolfCandidate.T3M.CanonicalNative
