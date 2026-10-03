import SigGolfCandidate.T3M.Verify.CanonicalBankState

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

theorem FrameNodes.take {nodes s} (h : FrameNodes nodes s) (n : Nat) :
    FrameNodes (nodes.take n) s := by
  intro k hk
  have hk' : k<n ∧ k<nodes.length := by simpa [List.length_take,Nat.lt_min] using hk
  have hh := h k hk'.2
  simpa only [List.getD_eq_getElem?_getD,List.getElem?_take,if_pos hk'.1] using hh

theorem BankAt.next {F c g j ptr nodes node heap s t nextNode nextHeap}
    (h : BankAt F c g j ptr nodes node heap s)
    (hend : SegmentEnd F c (plan g j) (ptr+8+80*(plan g j).folds) nextHeap nextNode t)
    (hpc : t.pc=pcOf (nextSegment g j)) (hcom : Common F t)
    (hfm : FrameMark (plan g j) c ptr s t) (he : nextHeap<4096)
    (hc : c<7) (hg : g<42) (hj : j<4) (hp : 1088 ≤ ptr) :
    BankAt F c g (j+1) (ptr+8+80*(plan g j).folds)
      (nextNodes (plan g j) nodes nextNode) nextNode nextHeap t := by
  have hmeta := plan_links ⟨g,hg⟩ ⟨j,by omega⟩
  dsimp only at hmeta
  have hlink := hmeta.2.2.2.1 hj
  have hge : (plan g j).depth ≤ nodes.length := by
    rw [h.depth]; unfold inDepth; split_ifs <;> omega
  have hlen : (nodes.take (plan g j).depth).length=(plan g j).depth := by
    rw [List.length_take,Nat.min_eq_left hge]
  have hs := hfm.nodes (h.stack.take (plan g j).depth) hc hg (by omega) hp hlen
  have hout : (nextNodes (plan g j) nodes nextNode).length=outDepth (plan g j) := by
    unfold nextNodes outDepth
    split_ifs <;> simp only [List.length_append,List.length_singleton,hlen,Nat.add_zero]
  have hstack : FrameNodes (nextNodes (plan g j) nodes nextNode) t := by
    unfold nextNodes
    split_ifs with hpush
    · apply hs.append
      simpa [destA,hpush,hlen] using hend.node
    · exact hs
  refine ⟨?_,hend.pointer,hfm.bankKnown h.known,hcom,hstack,?_,?_,?_,he,hend.orig⟩
  · simpa [nextSegment,show j≠4 by omega] using hpc
  · exact hout.trans hlink.1
  · intro hnone
    obtain ⟨hvar,hdepth⟩ := hlink.2 hnone
    simpa [destA,hvar,hdepth] using hend.node
  · intro hnone; exact hend.rev

#print axioms BankAt.next
end SigGolfCandidate.T3M.CanonicalNative
