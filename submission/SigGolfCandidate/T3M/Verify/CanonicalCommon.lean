import SigGolfCandidate.T3M.Verify.CanonicalPendingTransition
import SigGolfCandidate.T3M.Verify.CanonicalTables

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

/-- Words needed across all scheduled FTS segments. -/
def Protected (A : Nat) : Prop := A<512 ∨
  (WIT ≤ A ∧ A<WIT+64) ∨
  (∃ d, 1 ≤ d ∧ d ≤ 2 ∧ (A=frameA d+32 ∨ A=frameA d+40)) ∨
  (0xfef000 ≤ A ∧ A+8 ≤ 2^24)

structure Common (F : FCtx) (s : MachineState) : Prop where
  glob : Glob [] F.w F.pk s
  etab : ∀ k, k<21 → s.getMem (BitVec.ofNat 64 (ETAB+8*k))=
    BitVec.ofNat 64 (TAB+8*F.g k)
  fpad : ∀ d, 1 ≤ d → d ≤ 2 → s.getMem (BitVec.ofNat 64 (frameA d+32))=0 ∧
    s.getMem (BitVec.ofNat 64 (frameA d+40))=0
  tables : TablesOK s

theorem Common.transport {F s t} (h : Common F s)
    (hm : ∀ A, Protected A → t.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) :
    Common F t := by
  obtain ⟨hk,hw,hpk,hz,hh,hd⟩ := h.glob
  refine ⟨⟨by simp [KnownOK],?_,?_,?_,?_,?_⟩,?_,?_,?_⟩
  · intro j hj
    rw [hm _ (Or.inr (Or.inl (by unfold WIT; omega)))]
    exact hw j hj
  · exact ⟨(hm 0xA0 (Or.inl (by omega))).trans hpk.1,
      (hm 0xA8 (Or.inl (by omega))).trans hpk.2⟩
  · intro a ha
    have hb : a<512 := by
      simp only [pSlots,List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl | rfl | rfl <;> omega
    rw [hm _ (Or.inl hb)]; exact hz a ha
  · unfold PHalf
    rw [hm CTRW (Or.inl (by unfold CTRW; omega))]; exact hh
  · apply hd.congr
    intro A hA hEnd
    exact hm A (Or.inr (Or.inr (Or.inr ⟨by unfold TAB at hA; omega,hEnd⟩)))
  · intro k hk
    rw [hm _ (Or.inl (by unfold ETAB; omega))]; exact h.etab k hk
  · intro d h1 h2
    exact ⟨(hm _ (Or.inr (Or.inr (Or.inl ⟨d,h1,h2,Or.inl rfl⟩)))).trans (h.fpad d h1 h2).1,
      (hm _ (Or.inr (Or.inr (Or.inl ⟨d,h1,h2,Or.inr rfl⟩)))).trans (h.fpad d h1 h2).2⟩
  · intro k hk
    rw [hm _ (Or.inr (Or.inr (Or.inr (by omega))))]; exact h.tables k hk

theorem pending_protected_ne (p : BlockPlan) (c A off : Nat)
    (hc : c<7) (hdepth : p.depth ≤ 2)
    (hleaf : ∀ j, p.leaf=some j → j<3)
    (hA : Protected A) (hoff : off=16 ∨ off=24) :
    A≠pendingAddr p (WIT+64+144*c)+off := by
  cases hp : p.leaf with
  | some j =>
    have hj := hleaf j hp
    simp only [pendingAddr,hp]
    rcases hA with hA | ⟨hA,hA'⟩ | ⟨d,hd1,hd2,hAd⟩ | ⟨hA,hA'⟩
    · unfold WIT; rcases hoff with rfl | rfl <;> omega
    · rcases hoff with rfl | rfl <;> omega
    · unfold frameA WIT at *; rcases hAd with rfl | rfl <;>
        rcases hoff with rfl | rfl <;> omega
    · unfold WIT; rcases hoff with rfl | rfl <;> omega
  | none =>
    simp only [pendingAddr,hp]
    rcases hA with hA | ⟨hA,hA'⟩ | ⟨d,hd1,hd2,hAd⟩ | ⟨hA,hA'⟩
    · unfold frame; rcases hoff with rfl | rfl <;> omega
    · unfold frame WIT at *; rcases hoff with rfl | rfl <;> omega
    · unfold frameA frame at *; rcases hAd with rfl | rfl <;>
        rcases hoff with rfl | rfl <;> omega
    · unfold frame; rcases hoff with rfl | rfl <;> omega

theorem Common.pending {F s t c g j side}
    (h : Common F s) (hr : RawRes (pendingSpec (plan g j) side) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c)) : Common F t := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  apply h.transport
  intro A hA
  have hAv : A<2^64 := by
    rcases hA with hA | ⟨hA,hA'⟩ | ⟨d,hd1,hd2,hAd⟩ | ⟨hA,hA'⟩
    · omega
    · unfold WIT at *; omega
    · unfold frameA at *; rcases hAd with rfl | rfl <;> omega
    · omega
  apply hr.pending_frame _ _ h19
  all_goals
    apply ofNat_ne hAv
      (by cases hp : (plan g j).leaf with
          | none => simp only [pendingAddr,hp]; unfold frame; omega
          | some k => have hk := hb.2.2.2.1 k hp
                      simp only [pendingAddr,hp]; unfold WIT; omega)
    apply pending_protected_ne _ c A _ hc hb.2.1 hb.2.2.2.1 hA
    simp

theorem Common.rung {F s t g j i side out ptr}
    (h : Common F s) (hr : RawRes (rungSpec (plan g j) i side out) rungKeep s t)
    (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : 1088 ≤ ptr) (hpx : ptr+888 ≤ 32168)
    (h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8+80*(plan g j).folds)) :
    Common F t := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h14' : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by rw [BitVec.ofNat_add_ofNat]; exact h14
  apply h.transport
  intro A hA
  apply hr.rung_frame _ _ h14'
  all_goals
    rw [BitVec.ofNat_add_ofNat]
    have hAv : A<2^64 := by
      rcases hA with hA | ⟨hA,hA'⟩ | ⟨d,hd1,hd2,hAd⟩ | ⟨hA,hA'⟩
      · omega
      · unfold WIT at *; omega
      · unfold frameA at *; rcases hAd with rfl | rfl <;> omega
      · omega
    apply ofNat_ne hAv (by unfold WIT; omega)
    rcases hA with hA | ⟨hA,hA'⟩ | ⟨d,hd1,hd2,hAd⟩ | ⟨hA,hA'⟩
    · unfold WIT; omega
    · omega
    · unfold frameA WIT at *; rcases hAd with rfl | rfl <;> omega
    · unfold WIT; omega

theorem Common.hash {F s} (h : Common F s) (answer : HashOutput) (dst : Nat)
    (h12 : s.getReg .x12=BitVec.ofNat 64 dst)
    (hsafe : safeDest dst=true) (hav : FBAvoid dst) (hd : dst+32<2^64) :
    Common F (writeHash s answer) := by
  have ht : dst+32 ≤ 2^23 := by
    simp only [safeDest,Bool.and_eq_true,decide_eq_true_eq] at hsafe
    exact hsafe.1.2
  have hf : ∀ A, A<2^64 → (A+8 ≤ dst ∨ dst+32 ≤ A) →
      (writeHash s answer).getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hdist
    exact writeHash_frame s answer dst A h12 hA (by omega) hdist
  refine ⟨Glob_writeHash h.glob answer dst h12 hsafe,?_,?_,?_⟩
  · intro k hk
    rw [hf _ (by unfold ETAB; omega) ?_]; exact h.etab k hk
    rcases hav.1 with h0 | h0
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · intro d hd1 hd2
    obtain ⟨h0,h1⟩ := h.fpad d hd1 hd2
    have hdist := hav.2.2 d hd1 hd2
    exact ⟨(hf _ (by unfold frameA; omega) (by unfold frameA at *; omega)).trans h0,
      (hf _ (by unfold frameA; omega) (by unfold frameA at *; omega)).trans h1⟩
  · intro k hk
    rw [hf _ (by omega) (Or.inr (by omega))]; exact h.tables k hk

theorem Common.control {F s t sp keep} (h : Common F s) (hr : RawRes sp keep s t)
    (hm : sp.mem=[]) : Common F t := by
  apply h.transport
  intro A _; rw [hr.mem,hm]; rfl

theorem stream_dest_props (ptr i side : Nat) (hp : 1088 ≤ ptr)
    (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (hi : i ≤ 10) (hs : side<2) :
    safeDest (WIT+fblk ptr i+48*side)=true ∧ FBAvoid (WIT+fblk ptr i+48*side) ∧
      WIT+fblk ptr i+48*side+32<2^64 := by
  refine ⟨safeDest_hi _ (by unfold WLO WIT fblk; omega)
    (by unfold WIT fblk; omega) (by unfold WIT fblk; omega),?_,?_⟩
  · refine ⟨Or.inr (by unfold WIT fblk ETAB; omega),
      Or.inr (by unfold WIT fblk SENTINEL; omega),?_⟩
    intro d hd1 hd2
    exact Or.inr (by unfold WIT fblk frameA; omega)
  · unfold WIT fblk; omega

theorem Common.pending_answer {F c g j ptr pend node s t}
    (h : Common F s) (hs : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : 1088 ≤ ptr)
    (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (answer : HashOutput) :
    Common F (writeHash t answer) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have ht := h.pending hr hc hg hj hs.leafbase
  have h12 := pending_query_dest F c g j ptr pend node s t hs hr hg hj
  by_cases hn : (plan g j).folds=0
  · rw [if_pos hn] at h12
    have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
      (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
    exact ht.hash answer _ h12 hd.1 hd.2.1 hd.2.2.1
  · rw [if_neg hn] at h12
    have hd := stream_dest_props ptr 0 (pendHeap pend%2) hp hpx hp8 (by omega)
      (Nat.mod_lt _ (by decide))
    exact ht.hash answer _ h12 hd.1 hd.2.1 hd.2.2

theorem Common.rung_answer {F c g j ptr i heap node s t}
    (h : Common F s) (hs : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : 1088 ≤ ptr) (hpx : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (answer : HashOutput) :
    Common F (writeHash t answer) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have ht := h.rung hr hg hj hi hp hpx hs.pointer
  have h12 := rung_query_dest F c g j ptr i heap node s t hs hr hg hj
  by_cases hn : i+1=(plan g j).folds
  · rw [if_pos hn] at h12
    have hd := destA_props c (plan g j).variant (plan g j).depth hc (by omega) hb.2.1
      (plan_variants ⟨g,hg⟩ ⟨j,hj⟩)
    exact ht.hash answer _ h12 hd.1 hd.2.1 hd.2.2.1
  · rw [if_neg hn] at h12
    have hd := stream_dest_props ptr (i+1) (heap/2%2) hp hpx hp8 (by omega)
      (Nat.mod_lt _ (by decide))
    exact ht.hash answer _ h12 hd.1 hd.2.1 hd.2.2

#print axioms Common.pending
#print axioms Common.rung
#print axioms Common.hash
end SigGolfCandidate.T3M.CanonicalNative
