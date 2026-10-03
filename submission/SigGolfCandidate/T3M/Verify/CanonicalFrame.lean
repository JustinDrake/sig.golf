import SigGolfCandidate.T3M.Verify.CanonicalPendingTransition

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)

/-- Outside the pending header, the fold stream, and the final 32-byte output. -/
def SegSafe (p : BlockPlan) (c ptr A : Nat) : Prop :=
  A≠pendingAddr p (WIT+64+144*c)+16 ∧
  A≠pendingAddr p (WIT+64+144*c)+24 ∧
  (A+8 ≤ WIT+ptr+8 ∨ WIT+ptr+8+80*p.folds ≤ A) ∧
  (A+8 ≤ destA c p.variant p.depth ∨ destA c p.variant p.depth+32 ≤ A)

structure FrameMark (p : BlockPlan) (c ptr : Nat) (initial s : MachineState) : Prop where
  mem : ∀ A, A<2^24 → SegSafe p c ptr A →
    s.getMem (BitVec.ofNat 64 A)=initial.getMem (BitVec.ofNat 64 A)
  regs : ∀ r∈pendingKeep, s.getReg r=initial.getReg r

theorem FrameMark.refl (p c ptr s) : FrameMark p c ptr s s := ⟨by intros; rfl,by intros; rfl⟩

theorem FrameMark.pending {g j c ptr initial s t side}
    (h : FrameMark (plan g j) c ptr initial s)
    (hr : RawRes (pendingSpec (plan g j) side) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5)
    (h19 : s.getReg .x19=BitVec.ofNat 64 (WIT+64+144*c)) :
    FrameMark (plan g j) c ptr initial t := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  refine ⟨?_,fun r hrk => (hr.keep r hrk).trans (h.regs r hrk)⟩
  intro A hA hs
  rw [hr.pending_frame _ _ h19]
  · exact h.mem A hA hs
  all_goals
    apply ofNat_ne (by omega)
      (by cases hp : (plan g j).leaf with
          | none => simp only [pendingAddr,hp]; unfold frame; omega
          | some k => have hk := hb.2.2.2.1 k hp
                      simp only [pendingAddr,hp]; unfold WIT; omega)
    first | exact hs.1 | exact hs.2.1

theorem FrameMark.rung {g j c ptr initial s t side out i}
    (h : FrameMark (plan g j) c ptr initial s)
    (hr : RawRes (rungSpec (plan g j) i side out) rungKeep s t)
    (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : ptr+888 ≤ 32168)
    (h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8+80*(plan g j).folds)) :
    FrameMark (plan g j) c ptr initial t := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have h14' : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by rw [BitVec.ofNat_add_ofNat]; exact h14
  refine ⟨?_,?_⟩
  · intro A hA hs
    rw [hr.rung_frame _ _ h14']
    · exact h.mem A hA hs
    all_goals
      rw [BitVec.ofNat_add_ofNat]
      apply ofNat_ne (by omega) (by unfold WIT; omega)
      rcases hs.2.2.1 with hlow | hhigh <;> omega
  · intro r hrk
    have hk : r∈rungKeep := by
      have hh : ∀ r∈pendingKeep, r∈rungKeep := by decide +kernel
      exact hh r hrk
    exact (hr.keep r hk).trans (h.regs r hrk)

theorem FrameMark.hash {p c ptr initial s} (h : FrameMark p c ptr initial s)
    (answer : HashOutput) (dst : Nat) (hd : dst+32<2^64)
    (h12 : s.getReg .x12=BitVec.ofNat 64 dst)
    (hdst : (WIT+ptr+8 ≤ dst ∧ dst+32 ≤ WIT+ptr+8+80*p.folds) ∨
      dst=destA c p.variant p.depth) : FrameMark p c ptr initial (writeHash s answer) := by
  refine ⟨?_,?_⟩
  · intro A hA hs
    rw [writeHash_frame s answer dst A h12 (by omega) (by omega) ?_]
    · exact h.mem A hA hs
    rcases hdst with ⟨hlo,hhi⟩ | hdest
    · rcases hs.2.2.1 with ha | ha <;> omega
    · rw [hdest]; exact hs.2.2.2
  · intro r hrk
    rw [writeHash_getReg]; exact h.regs r hrk

theorem FrameMark.control {p c ptr initial s t sp keep}
    (h : FrameMark p c ptr initial s) (hr : RawRes sp keep s t) (hm : sp.mem=[])
    (hk : ∀ r∈pendingKeep, r∈keep) : FrameMark p c ptr initial t := by
  refine ⟨?_,fun r hrk => (hr.keep r (hk r hrk)).trans (h.regs r hrk)⟩
  intro A hA hs
  rw [hr.mem,hm]; exact h.mem A hA hs

theorem FrameMark.pending_answer {F c g j ptr pend node initial s t}
    (h : FrameMark (plan g j) c ptr initial s)
    (hs : PendingReady F c (plan g j) ptr pend node s)
    (hr : RawRes (pendingSpec (plan g j) (pendHeap pend%2)) pendingKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hp : ptr+888 ≤ 32168)
    (answer : HashOutput) : FrameMark (plan g j) c ptr initial (writeHash t answer) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have ht := h.pending hr hc hg hj hs.leafbase
  have h12 := pending_query_dest F c g j ptr pend node s t hs hr hg hj
  let dst := if (plan g j).folds=0 then destA c (plan g j).variant (plan g j).depth
      else WIT+fblk ptr 0+48*(pendHeap pend%2)
  have hd : dst+32<2^64 := by
    dsimp only [dst]; split_ifs
    · unfold destA forestSlot frameA; split_ifs <;> omega
    · have hh := Nat.mod_lt (pendHeap pend) (by decide : 0<2)
      unfold WIT fblk; omega
  apply ht.hash answer dst hd h12
  dsimp only [dst]; split_ifs with hz
  · exact Or.inr rfl
  · apply Or.inl
    have hh := Nat.mod_lt (pendHeap pend) (by decide : 0<2)
    unfold fblk; omega

theorem FrameMark.rung_answer {F c g j ptr i heap node initial s t}
    (h : FrameMark (plan g j) c ptr initial s)
    (hs : RungReady F c (plan g j) ptr i heap node s)
    (hr : RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t)
    (hc : c<7) (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : ptr+888 ≤ 32168) (answer : HashOutput) :
    FrameMark (plan g j) c ptr initial (writeHash t answer) := by
  have hb := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hb
  have ht := h.rung hr hg hj hi hp hs.pointer
  have h12 := rung_query_dest F c g j ptr i heap node s t hs hr hg hj
  let dst := if i+1=(plan g j).folds then destA c (plan g j).variant (plan g j).depth
      else WIT+fblk ptr (i+1)+48*(heap/2%2)
  have hd : dst+32<2^64 := by
    dsimp only [dst]; split_ifs
    · unfold destA forestSlot frameA; split_ifs <;> omega
    · have hh := Nat.mod_lt (heap/2) (by decide : 0<2)
      unfold WIT fblk; omega
  apply ht.hash answer dst hd h12
  dsimp only [dst]; split_ifs with hz
  · exact Or.inr rfl
  · apply Or.inl
    have hh := Nat.mod_lt (heap/2) (by decide : 0<2)
    unfold fblk; omega

#print axioms FrameMark.pending_answer
#print axioms FrameMark.rung_answer
end SigGolfCandidate.T3M.CanonicalNative
