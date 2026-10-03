import SigGolfCandidate.T3M.Verify.CanonicalQuery
import SigGolfCandidate.T3M.Verify.CanonicalControl

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

theorem intermediate_hash_next : ∀ (g : Fin 42) (j : Fin 5) (i : Fin 10) (side : Fin 2),
    i.val+1<(plan g.val j.val).folds →
      atHash (plan g.val j.val) side.val (i.val+1)+1=
        atRung (plan g.val j.val) side.val (i.val+1) := by decide +kernel

theorem plan_variants : ∀ (g : Fin 42) (j : Fin 5),
    (plan g.val j.val).variant=1 → (plan g.val j.val).depth<2 := by decide +kernel

theorem dest_eval (p : BlockPlan) (s : MachineState) (c : Nat)
    (h25 : s.getReg .x25=BitVec.ofNat 64 (forestSlot c)) (hV : p.variant ≤ 2) :
    (dest p).eval s=BitVec.ofNat 64 (destA c p.variant p.depth) := by
  rcases (show p.variant=0 ∨ p.variant=1 ∨ p.variant=2 by omega) with ha | ha | ha <;>
    simp [dest,destA,ha,E.eval,cE,h25,frame,frameA,Nat.mul_add,Nat.add_assoc]

theorem rung_dest_eval (p : BlockPlan) (s : MachineState) (c ptr i out : Nat)
    (h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+BitVec.ofNat 64 (80*p.folds))
    (h25 : s.getReg .x25=BitVec.ofNat 64 (forestSlot c)) (hV : p.variant ≤ 2) :
    (rungDest p i out).eval s=
      BitVec.ofNat 64 (if i+1=p.folds then destA c p.variant p.depth
        else WIT+fblk ptr (i+1)+48*out) := by
  unfold rungDest
  split_ifs with h
  · exact dest_eval p s c h25 hV
  · simp only [rAdd,addC_eval,E.eval,h14]
    rw [offset_cancel,BitVec.ofNat_add_ofNat]
    congr 1; unfold fblk; omega

structure RungReady (F : FCtx) (c : Nat) (p : BlockPlan) (ptr i heap : Nat)
    (node : Digest) (s : MachineState) : Prop where
  pc : s.pc=pcOf (atRung p (heap%2) i)
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8+80*p.folds)
  rev : s.getReg .x23=FtsRev.rv heap
  hdr : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)
  bytes : s.getReg .x11=64#64
  hash : s.getReg .x5=0
  forest : s.getReg .x25=BitVec.ofNat 64 (forestSlot c)
  node : DigAt s (WIT+fblk ptr i+48*(heap%2)) node
  orig : FoldOrig F.w ptr i heap s

theorem rung_query_dest (F : FCtx) (c g j ptr i heap : Nat) (node : Digest)
    (s t : MachineState) (h : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hg : g<42) (hj : j<5) :
    t.getReg .x12=BitVec.ofNat 64 (if i+1=(plan g j).folds
      then destA c (plan g j).variant (plan g j).depth
      else WIT+fblk ptr (i+1)+48*(heap/2%2)) := by
  rw [hr.regs (.x12,rungDest (plan g j) i (heap/2%2)) (by simp [rungSpec])]
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  apply rung_dest_eval _ s c ptr i _ _ h.forest hb.2.2.1
  rw [BitVec.ofNat_add_ofNat]; exact h.pointer

theorem rung_hash_valid (F : FCtx) (c g j ptr i heap : Nat) (node : Digest)
    (s t : MachineState) (h : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : ptr+888 ≤ 32168) (hp8 : ptr%8=0) : hashArgumentsValid t=true := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by rw [BitVec.ofNat_add_ofNat]; exact h.pointer
  have h10 : t.getReg .x10=BitVec.ofNat 64 (WIT+fblk ptr i) := by
    rw [hr.rung_src _ h14,BitVec.ofNat_add_ofNat]
    congr 1; unfold fblk; omega
  have h11 : t.getReg .x11=64#64 := (hr.keep .x11 (by simp [rungKeep])).trans h.bytes
  have h12 := rung_query_dest F c g j ptr i heap node s t h hr hg hj
  by_cases hlast : i+1=(plan g j).folds
  · rw [if_pos hlast] at h12
    have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
      (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
    apply hashArgs_of t _ 64 _ h10 h11 h12
    · unfold fblk WIT; omega
    · decide
    · unfold fblk WIT; omega
    · unfold destA frameA forestSlot; split_ifs <;> omega
    · have := hd.2.2.2.2.2
      unfold WIT at this; omega
  · rw [if_neg hlast] at h12
    apply hashArgs_of t _ 64 _ h10 h11 h12
    · unfold fblk WIT; omega
    · decide
    · unfold fblk WIT; omega
    · unfold fblk WIT; omega
    · have ht := Nat.mod_lt (heap/2) (by decide : 0<2)
      unfold fblk WIT; omega

theorem rung_advance (F : FCtx) (c g j ptr i heap : Nat) (node : Digest)
    (s t : MachineState) (answer : HashOutput)
    (h : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hg : g<42) (hj : j<5) (hi : i+1<(plan g j).folds)
    (hp : 1088 ≤ ptr) (hpmax : ptr+888 ≤ 32168) (he : heap<4096) :
    RungReady F c (plan g j) ptr (i+1) (heap/2) (answer.extractLsb' 0 128)
      (writeHash t answer) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by rw [BitVec.ofNat_add_ofNat]; exact h.pointer
  have hout : heap/2%2<2 := Nat.mod_lt _ (by decide)
  have h12 := rung_query_dest F c g j ptr i heap node s t h hr hg hj
  rw [if_neg (by omega)] at h12
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [writeHash_pc,hr.pc rfl]
    simp only [rungSpec,if_neg (by omega : i+1≠(plan g j).folds)]
    rw [pcOf_add4,intermediate_hash_next ⟨g,hg⟩ ⟨j,hj⟩ ⟨i,by omega⟩ ⟨heap/2%2,hout⟩ hi]
  · rw [writeHash_getReg,hr.keep .x14 (by simp [rungKeep])]; exact h.pointer
  · rw [writeHash_getReg]; exact hr.rung_heap heap h.rev (by omega)
  · rw [writeHash_getReg,hr.keep .x27 (by simp [rungKeep])]; exact h.hdr
  · rw [writeHash_getReg,hr.keep .x11 (by simp [rungKeep])]; exact h.bytes
  · rw [writeHash_getReg,hr.keep .x5 (by simp [rungKeep])]; exact h.hash
  · rw [writeHash_getReg,hr.keep .x25 (by simp [rungKeep])]; exact h.forest
  · exact DigAt.writeHash_lo t answer _ h12 (by unfold WIT fblk; omega)
  · intro k hk ho
    have hn := rung_next ptr i (heap/2%2) (8*k) hout ho hp
    rw [writeHash_frame t answer _ _ h12 (by unfold WIT WX at *; omega)
      (by unfold WIT fblk; omega) (rung_dest_avoid ptr (i+1) (heap/2%2) (8*k) hout hp ho)]
    rw [hr.rung_frame _ _ h14]
    · apply h.orig k hk
      rcases hn.2.2 with h0 | h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl h0))
    all_goals
      rw [BitVec.ofNat_add_ofNat]
      apply ofNat_ne (by unfold WIT WX at *; omega) (by unfold WIT; omega)
      unfold fblk at hn
      omega

structure SegmentEnd (F : FCtx) (c : Nat) (p : BlockPlan) (ptr heap : Nat)
    (node : Digest) (s : MachineState) : Prop where
  pointer : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr)
  rev : s.getReg .x23=FtsRev.rv heap
  hdr : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx)
  bytes : s.getReg .x11=64#64
  hash : s.getReg .x5=0
  forest : s.getReg .x25=BitVec.ofNat 64 (forestSlot c)
  node : DigAt s (destA c p.variant p.depth) node
  orig : WitF F.w ptr s

theorem rung_finish (F : FCtx) (c g j ptr i heap : Nat) (node : Digest)
    (s t : MachineState) (answer : HashOutput)
    (h : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hi : i+1=(plan g j).folds)
    (hp : 1088 ≤ ptr) (hpmax : ptr+888 ≤ 32168) (he : heap<4096) :
    SegmentEnd F c (plan g j) (ptr+8+80*(plan g j).folds) (heap/2)
      (answer.extractLsb' 0 128) (writeHash t answer) ∧
      (writeHash t answer).pc=pcOf (atHash (plan g j) (heap%2) (plan g j).folds+1) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by rw [BitVec.ofNat_add_ofNat]; exact h.pointer
  have h12 := rung_query_dest F c g j ptr i heap node s t h hr hg hj
  rw [if_pos hi] at h12
  have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
    (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
  have dlow := hd.2.2.2.2.2
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [writeHash_getReg,hr.keep .x14 (by simp [rungKeep]),h.pointer]
    congr 1; omega
  · rw [writeHash_getReg]; exact hr.rung_heap heap h.rev (by omega)
  · rw [writeHash_getReg,hr.keep .x27 (by simp [rungKeep])]; exact h.hdr
  · rw [writeHash_getReg,hr.keep .x11 (by simp [rungKeep])]; exact h.bytes
  · rw [writeHash_getReg,hr.keep .x5 (by simp [rungKeep])]; exact h.hash
  · rw [writeHash_getReg,hr.keep .x25 (by simp [rungKeep])]; exact h.forest
  · exact DigAt.writeHash_lo t answer _ h12 hd.2.2.1
  · intro k hk ho
    have hn := tail_next ptr i (plan g j).folds (8*k) hi hp ho
    rw [writeHash_frame t answer _ _ h12 (by unfold WIT WX at *; omega)
      (by have := hd.2.2.1; omega) (Or.inr (by unfold WIT at *; omega))]
    rw [hr.rung_frame _ _ h14]
    · apply h.orig k hk
      rcases hn.2.2 with h0 | h0 | h0
      · exact Or.inl h0
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl h0))
    all_goals
      rw [BitVec.ofNat_add_ofNat]
      apply ofNat_ne (by unfold WIT WX at *; omega) (by unfold WIT; omega)
      unfold fblk at hn
      omega
  · rw [writeHash_pc,hr.pc rfl]
    simp only [rungSpec,pcOf_add4,hi,if_true]

theorem SegmentEnd.control {F c p ptr heap node s t sp keep}
    (h : SegmentEnd F c p ptr heap node s) (hr : RawRes sp keep s t)
    (hm : sp.mem=[])
    (hk : ∀ r, r=.x14 ∨ r=.x23 ∨ r=.x27 ∨ r=.x11 ∨ r=.x5 ∨ r=.x25 → r∈keep) :
    SegmentEnd F c p ptr heap node t := by
  have hf : ∀ A, t.getMem A=s.getMem A := by intro A; rw [hr.mem,hm]; rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hr.keep .x14 (hk _ (by simp))]; exact h.pointer
  · rw [hr.keep .x23 (hk _ (by simp))]; exact h.rev
  · rw [hr.keep .x27 (hk _ (by simp))]; exact h.hdr
  · rw [hr.keep .x11 (hk _ (by simp))]; exact h.bytes
  · rw [hr.keep .x5 (hk _ (by simp))]; exact h.hash
  · rw [hr.keep .x25 (hk _ (by simp))]; exact h.forest
  · exact ⟨(hf _).trans h.node.1,(hf _).trans h.node.2⟩
  · intro k hk ho; rw [hf]; exact h.orig k hk ho

#print axioms rung_finish
#print axioms rung_advance
#print axioms rung_hash_valid
end SigGolfCandidate.T3M.CanonicalNative
