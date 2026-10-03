import SigGolfCandidate.T3M.Verify.CanonicalCommon
import SigGolfCandidate.T3M.Verify.CanonicalFrame
import SigGolfCandidate.T3M.CanonicalPort.Combined

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

abbrev GQ := CanonicalPort.Verify.GoodQ

theorem fold_blocks_c (F : FCtx) (c ptr i heap : Nat) (node : Digest) :
    (toQ (T3.pad64 (foldBlk F c ptr i heap node))).blocks=1 := by
  unfold foldBlk; split <;> exact blocks_blk4 _ _ _ _

theorem foldStep_bind_c {β : Type} (F : FCtx) (c ptr i heap : Nat) (node : Digest)
    (k : Digest × Nat → T3.M β) :
    (foldStep F.w F.idx c ptr (node,heap) i >>= k)=
      (T3.shortHash (foldBlk F c ptr i heap node) >>= fun v => k (v,heap/2)) := by
  rw [foldStep_eq,bind_assoc]; simp only [pure_bind]

def Finished (F : FCtx) (c g j ptr heap : Nat) (node : Digest) (s : MachineState) : Prop :=
  SegmentEnd F c (plan g j) ptr heap node s ∧
    ∃ side, side<2 ∧ s.pc=pcOf (atHash (plan g j) side (plan g j).folds+1)

/-- Exact cost of the nonempty scheduled fold suffix: 14 cycles per fold, less
one cycle on the final fold. Hash queries and their arbitrary answers are part
of the oracle simulation, rather than a fixed test transcript. -/
theorem folds_good (F : FCtx) (c g j ptr : Nat) (initial : MachineState)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop)
    (hK : ∀ node heap u, Finished F c g j (ptr+8+80*(plan g j).folds) heap node u →
      Common F u → FrameMark (plan g j) c ptr initial u → heap<4096 →
      GQ u B B Q A (R (node,heap))) :
    ∀ n i heap node s, i+n=(plan g j).folds → 0<n → heap<4096 →
      RungReady F c (plan g j) ptr i heap node s → Common F s →
      FrameMark (plan g j) c ptr initial s →
      GQ s (B+(14*n-1)) (B+(14*n-1)) Q (A+(14*n-1))
        (CanonicalPort.Verify.ccM ((List.range' i n).foldlM (foldStep F.w F.idx c ptr) (node,heap)) R) := by
  intro n
  induction n with
  | zero => intro i heap node s heq hn; omega
  | succ n ih =>
    intro i heap node s heq hn he hs hcommon hmark
    have hi : i<(plan g j).folds := by omega
    obtain ⟨t,hr,hin⟩ := scheduled_rung_query F c g j i heap ptr node s hc hg hj hi
      hpx hp8 he hs.pc hs.pointer hs.rev hs.hdr hs.bytes hs.node hs.orig
    have hf := hr.ecall rfl
    have h5 : t.getReg .x5=0 := (hr.keep .x5 (by simp [rungKeep])).trans hs.hash
    have hv := rung_hash_valid F c g j ptr i heap node s t hs hr hc hg hj hi hpx hp8
    have hb := fold_blocks_c F c ptr i heap node
    simp only [List.range'_succ,List.foldlM_cons,foldStep_bind_c]
    by_cases hz : n=0
    · subst n
      have hlast : i+1=(plan g j).folds := by omega
      have hq := CanonicalPort.Verify.GoodQ.shortHash_bind (N:=B) (C:=B) (A:=A) (Q:=Q)
        (f:=fun v => List.foldlM (foldStep F.w F.idx c ptr) (v,heap/2) (List.range' (i+1) 0))
        (K:=R) hf h5 hv hin (fun answer => by
          simp only [List.range'_zero,List.foldlM_nil,CanonicalPort.Verify.ccM_pure]
          obtain ⟨hend,hpc⟩ := rung_finish F c g j ptr i heap node s t answer hs hr
            hc hg hj hlast hp hpx he
          exact hK _ _ _ ⟨hend,heap%2,Nat.mod_lt _ (by decide),hpc⟩
            (hcommon.rung_answer hs hr hc hg hj hi hp hpx hp8 answer)
            (hmark.rung_answer hs hr hc hg hj hi hpx answer) (by omega))
      rw [hb] at hq
      apply CanonicalPort.Verify.GoodQ.steps' hr.steps hq
      · simp only [rungSpec,if_pos hlast]; omega
      · simp only [rungSpec,if_pos hlast]; omega
      · intro hQ; refine ⟨hQ,?_⟩
        simp only [rungSpec,if_pos hlast]; omega
    · have hinner : i+1<(plan g j).folds := by omega
      have hq := CanonicalPort.Verify.GoodQ.shortHash_bind
        (N:=B+(14*n-1)) (C:=B+(14*n-1)) (A:=A+(14*n-1)) (Q:=Q)
        (f:=fun v => List.foldlM (foldStep F.w F.idx c ptr) (v,heap/2) (List.range' (i+1) n))
        (K:=R) hf h5 hv hin (fun answer =>
          ih (i+1) (heap/2) _ _ (by omega) (by omega) (by omega)
            (rung_advance F c g j ptr i heap node s t answer hs hr hg hj hinner hp hpx he)
            (hcommon.rung_answer hs hr hc hg hj hi hp hpx hp8 answer)
            (hmark.rung_answer hs hr hc hg hj hi hpx answer))
      rw [hb] at hq
      apply CanonicalPort.Verify.GoodQ.steps' hr.steps hq
      · simp only [rungSpec,if_neg (by omega : i+1≠(plan g j).folds)]; omega
      · simp only [rungSpec,if_neg (by omega : i+1≠(plan g j).folds)]; omega
      · intro hQ; refine ⟨hQ,?_⟩
        simp only [rungSpec,if_neg (by omega : i+1≠(plan g j).folds)]; omega

theorem pending_good (F : FCtx) (c g j ptr : Nat) (initial : MachineState)
    (pend : Pending) (node : Digest) (s : MachineState)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (he : pendHeap pend<4096)
    (hm : PendingMatch F c (plan g j) pend)
    (hs : PendingReady F c (plan g j) ptr pend node s)
    (hcommon : Common F s) (hmark : FrameMark (plan g j) c ptr initial s)
    (haccess : ∀ k, (plan g j).leaf=some k → accessValid (s.getReg (slotReg k)) 8=true)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop)
    (hK : ∀ node heap u, Finished F c g j (ptr+8+80*(plan g j).folds) heap node u →
      Common F u → FrameMark (plan g j) c ptr initial u → heap<4096 →
      GQ u B B Q A (R (node,heap))) :
    GQ s (B+14+14*(plan g j).folds) (B+14+14*(plan g j).folds) Q
      (A+14+14*(plan g j).folds)
      (CanonicalPort.Verify.ccM (pendingHash F.w F.idx c node pend >>= fun v =>
        foldsP F.w F.idx c ptr (plan g j).folds v (pendHeap pend)) R) := by
  obtain ⟨t,hr,hin⟩ := scheduled_pending_query F c g j ptr pend node s hc hg hj hp
    (by unfold WX; omega) hp8 hm hs.pc hs.leafbase hs.rev hs.hdr hs.leafhdr hs.bytes
    haccess hs.payload hs.orig hcommon.fpad
  have hf := hr.ecall rfl
  have h5 : t.getReg .x5=0 := (hr.keep .x5 (by simp [pendingKeep])).trans hs.hash
  have hv := pending_hash_valid F c g j ptr pend node s t hs hr hc hg hj hpx hp8 hm
  have hb : (toQ (T3.pad64 (pendBlk F c node pend))).blocks=1 := by
    cases pend <;> unfold pendBlk <;> exact blocks_blk4 _ _ _ _
  rw [pendingHash_eq]
  by_cases hz : (plan g j).folds=0
  · have hq := CanonicalPort.Verify.GoodQ.shortHash_bind (N:=B) (C:=B) (A:=A) (Q:=Q)
      (f:=fun v => foldsP F.w F.idx c ptr (plan g j).folds v (pendHeap pend)) (K:=R)
      hf h5 hv hin (fun answer => by
        simp only [foldsP,hz,List.range_zero,List.foldlM_nil,CanonicalPort.Verify.ccM_pure]
        obtain ⟨hend,hpc⟩ := pending_finish F c g j ptr pend node s t answer hs hr
          hc hg hj hz hp hpx hm
        apply hK _ _ _
        · refine ⟨?_,pendHeap pend%2,Nat.mod_lt _ (by decide),hpc⟩
          simpa only [hz,Nat.mul_zero,Nat.add_zero] using hend
        · exact hcommon.pending_answer hs hr hc hg hj hp hpx hp8 answer
        · exact hmark.pending_answer hs hr hc hg hj hpx answer
        · exact he)
    rw [hb] at hq
    apply CanonicalPort.Verify.GoodQ.steps' hr.steps hq
    · simp only [pendingSpec,if_pos hz]; omega
    · simp only [pendingSpec,if_pos hz]; omega
    · intro hQ; refine ⟨hQ,?_⟩
      simp only [pendingSpec,if_pos hz]; omega
  · have hq := CanonicalPort.Verify.GoodQ.shortHash_bind
      (N:=B+(14*(plan g j).folds-1)) (C:=B+(14*(plan g j).folds-1))
      (A:=A+(14*(plan g j).folds-1)) (Q:=Q)
      (f:=fun v => foldsP F.w F.idx c ptr (plan g j).folds v (pendHeap pend)) (K:=R)
      hf h5 hv hin (fun answer => by
        simp only [foldsP,List.range_eq_range']
        exact folds_good F c g j ptr initial hc hg hj hp hpx hp8 R B A Q hK
          (plan g j).folds 0 (pendHeap pend) _ _ (by omega) (by omega) he
          (pending_advance F c g j ptr pend node s t answer hs hr hc hg hj (by omega) hp hpx hm)
          (hcommon.pending_answer hs hr hc hg hj hp hpx hp8 answer)
          (hmark.pending_answer hs hr hc hg hj hpx answer))
    rw [hb] at hq
    apply CanonicalPort.Verify.GoodQ.steps' hr.steps hq
    · simp only [pendingSpec,if_neg hz]; omega
    · simp only [pendingSpec,if_neg hz]; omega
    · intro hQ; refine ⟨hQ,?_⟩
      simp only [pendingSpec,if_neg hz]; omega

#print axioms folds_good
#print axioms pending_good
end SigGolfCandidate.T3M.CanonicalNative
