import SigGolfCandidate.T3M.Verify.CanonicalSegmentJoin

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

def FrameNodes (nodes : List Digest) (s : MachineState) : Prop :=
  ∀ k, k<nodes.length → DigAt s (frameA (k+1)) (nodes.getD k 0)

def outDepth (p : BlockPlan) : Nat := p.depth+(if p.variant=1 then 1 else 0)
def inDepth (p : BlockPlan) : Nat := p.depth+(if p.leaf.isSome then 0 else 1)

theorem plan_links : ∀ (g : Fin 42) (j : Fin 5),
    let p := plan g.val j.val
    (p.leaf=none → p.depth ≤ 1) ∧
    (p.variant=2 ↔ j.val=4) ∧
    (j.val=0 → p.leaf=some 0 ∧ p.depth=0) ∧
    (j.val<4 → outDepth p=inDepth (plan g.val (j.val+1)) ∧
      ((plan g.val (j.val+1)).leaf=none → p.variant=0 ∧
        p.depth=(plan g.val (j.val+1)).depth+1)) ∧
    (j.val=4 → p.variant=2 ∧ p.depth=0) := by decide +kernel

theorem frame_below_safe (p : BlockPlan) (c ptr k off : Nat)
    (hc : c<7) (hd : p.depth ≤ 2) (hp : 1088 ≤ ptr)
    (hV : p.variant ≤ 2) (hleaf : ∀ j, p.leaf=some j → j<3)
    (hk : k<p.depth) (hoff : off=0 ∨ off=8) :
    SegSafe p c ptr (frameA (k+1)+off) := by
  refine ⟨?_,?_,Or.inl ?_,?_⟩
  · cases hleafp : p.leaf with
    | some j => have hj := hleaf j hleafp
                simp only [pendingAddr,hleafp]; unfold frameA WIT
                rcases hoff with rfl | rfl <;> omega
    | none => simp only [pendingAddr,hleafp]; unfold frame frameA
              rcases hoff with rfl | rfl <;> omega
  · cases hleafp : p.leaf with
    | some j => have hj := hleaf j hleafp
                simp only [pendingAddr,hleafp]; unfold frameA WIT
                rcases hoff with rfl | rfl <;> omega
    | none => simp only [pendingAddr,hleafp]; unfold frame frameA
              rcases hoff with rfl | rfl <;> omega
  · unfold frameA WIT; rcases hoff with rfl | rfl <;> omega
  · unfold destA frameA forestSlot
    split_ifs <;> rcases hoff with rfl | rfl <;> omega

theorem roots_below_safe (p : BlockPlan) (c ptr k off : Nat)
    (hc : c<7) (hd : p.depth ≤ 2) (hp : 1088 ≤ ptr)
    (hV : p.variant ≤ 2) (hleaf : ∀ j, p.leaf=some j → j<3)
    (hmerge : p.leaf=none → p.depth ≤ 1) (hpush : p.variant=1 → p.depth<2)
    (hk : k<c) (hoff : off=0 ∨ off=8) :
    SegSafe p c ptr (forestSlot k+off) := by
  refine ⟨?_,?_,Or.inl ?_,?_⟩
  · cases hleafp : p.leaf with
    | some j => have hj := hleaf j hleafp
                simp only [pendingAddr,hleafp]; unfold forestSlot WIT
                split_ifs <;> rcases hoff with rfl | rfl <;> omega
    | none => have hd' := hmerge hleafp
              simp only [pendingAddr,hleafp]; unfold forestSlot frame
              split_ifs <;> rcases hoff with rfl | rfl <;> omega
  · cases hleafp : p.leaf with
    | some j => have hj := hleaf j hleafp
                simp only [pendingAddr,hleafp]; unfold forestSlot WIT
                split_ifs <;> rcases hoff with rfl | rfl <;> omega
    | none => have hd' := hmerge hleafp
              simp only [pendingAddr,hleafp]; unfold forestSlot frame
              split_ifs <;> rcases hoff with rfl | rfl <;> omega
  · unfold forestSlot WIT; split_ifs <;> rcases hoff with rfl | rfl <;> omega
  · unfold destA frameA forestSlot
    split_ifs <;> rcases hoff with rfl | rfl <;> omega

theorem FrameMark.nodes {g j c ptr initial s nodes}
    (h : FrameMark (plan g j) c ptr initial s) (hn : FrameNodes nodes initial)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hlen : nodes.length=(plan g j).depth) : FrameNodes nodes s := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  intro k hk
  apply h.digest (hn k hk) (by unfold frameA; omega)
  · exact frame_below_safe _ c ptr k 0 hc hb.2.1 hp hb.2.2.1 hb.2.2.2.1
      (by omega) (by simp)
  · simpa only [Nat.add_zero] using
      frame_below_safe _ c ptr k 8 hc hb.2.1 hp hb.2.2.1 hb.2.2.2.1 (by omega) (by simp)

theorem FrameMark.roots {g j c ptr initial s roots}
    (h : FrameMark (plan g j) c ptr initial s) (hn : RootsOK roots initial)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hlen : roots.length=c) : RootsOK roots s := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have hl := plan_links ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hl
  intro k hk
  apply h.digest (hn k hk) (by unfold forestSlot; split_ifs <;> omega)
  · exact roots_below_safe _ c ptr k 0 hc hb.2.1 hp hb.2.2.1 hb.2.2.2.1
      hl.1 (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
      (by omega) (by simp)
  · simpa only [Nat.add_zero] using
      roots_below_safe _ c ptr k 8 hc hb.2.1 hp hb.2.2.1 hb.2.2.2.1
        hl.1 (plan_variants ⟨g,hg⟩ ⟨j,hj⟩) (by omega) (by simp)

theorem FrameNodes.append {nodes s node} (h : FrameNodes nodes s)
    (hn : DigAt s (frameA (nodes.length+1)) node) : FrameNodes (nodes++[node]) s := by
  intro k hk
  by_cases hkn : k<nodes.length
  · rw [List.getD_append nodes [node] 0 k hkn]; exact h k hkn
  · have hke : k=nodes.length := by simp only [List.length_append,List.length_singleton] at hk; omega
    subst k
    rw [List.getD_append_right nodes [node] 0 nodes.length (by omega)]
    simpa using hn

#print axioms FrameMark.nodes
#print axioms FrameMark.roots
end SigGolfCandidate.T3M.CanonicalNative
