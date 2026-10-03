import SigGolfCandidate.T3M.Verify.CanonicalSegment

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def tailBudget (p : BlockPlan) : Nat := if p.folds=0 then 0 else 1

theorem segment_good (F : FCtx) (c g j ptr : Nat) (initial : MachineState)
    (pend : Pending) (node : Digest) (s : MachineState)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (he : pendHeap pend<4096)
    (hm : PendingMatch F c (plan g j) pend)
    (hs : PendingReady F c (plan g j) ptr pend node s)
    (hcommon : Common F s) (hmark : FrameMark (plan g j) c ptr initial s)
    (haccess : ∀ k, (plan g j).leaf=some k → accessValid (s.getReg (slotReg k)) 8=true)
    (R : Digest × Nat → OracleComp HashSpec CanonicalPort.Verify.Obs)
    (B A : Nat) (Q : Prop)
    (hK : ∀ node heap u,
      SegmentEnd F c (plan g j) (ptr+8+80*(plan g j).folds) heap node u →
      u.pc=pcOf (nextSegment g j) → Common F u → FrameMark (plan g j) c ptr initial u → heap<4096 →
      GQ u B B Q A (R (node,heap))) :
    GQ s (B+14+14*(plan g j).folds+tailBudget (plan g j))
      (B+14+14*(plan g j).folds+tailBudget (plan g j)) Q
      (A+14+14*(plan g j).folds+tailBudget (plan g j))
      (CanonicalPort.Verify.ccM (pendingHash F.w F.idx c node pend >>= fun v =>
        foldsP F.w F.idx c ptr (plan g j).folds v (pendHeap pend)) R) := by
  have h := pending_good F c g j ptr initial pend node s hc hg hj hp hpx hp8 he hm hs
    hcommon hmark haccess R (B+tailBudget (plan g j)) (A+tailBudget (plan g j)) Q
    (fun node heap u hend hcom hfm hhe => by
      obtain ⟨hseg,side,hside,hpc⟩ := hend
      obtain ⟨v,hv⟩ := tail_run g j side hg hj hside u hpc
      have hsegv := hseg.control hv (by rfl) (by
        intro r hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [allKeep])
      have hpcv : v.pc=pcOf (nextSegment g j) := hv.pc rfl
      have hcomv := hcom.control hv (by rfl)
      have hfmv := hfm.control hv (by rfl)
        (by decide +kernel : ∀ r∈pendingKeep, r∈allKeep)
      apply CanonicalPort.Verify.GoodQ.steps' hv.steps (hK node heap v hsegv hpcv hcomv hfmv hhe)
      · unfold tailSpec tailBudget; split_ifs <;> dsimp only <;> omega
      · unfold tailSpec tailBudget; split_ifs <;> dsimp only <;> omega
      · intro hQ; refine ⟨hQ,?_⟩
        unfold tailSpec tailBudget; split_ifs <;> dsimp only <;> omega)
  convert h using 1 <;> omega

theorem FrameMark.digest {p c ptr initial s node A}
    (h : FrameMark p c ptr initial s) (hd : DigAt initial A node)
    (hA : A+8<2^24) (hs0 : SegSafe p c ptr A) (hs8 : SegSafe p c ptr (A+8)) :
    DigAt s A node :=
  ⟨(h.mem A (by omega) hs0).trans hd.1,(h.mem (A+8) hA hs8).trans hd.2⟩

#print axioms segment_good
end SigGolfCandidate.T3M.CanonicalNative
