import SigGolfCandidate.T3M.Verify.CanonicalPhase
import SigGolfCandidate.T3M.Verify.CanonicalPlan

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace SigGolfCandidate.T3M.CanonicalNative
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput Selection selections header)

theorem pending_hashInput_general {ptr : Nat} (F : FCtx) (c d : Nat) (node : Digest) (pend : Pending) (m u : MachineState)
    (hp : PendOK F c d node m pend) (hw : WitF F.w ptr m) (hc : c < 7)
    (hpad : ∀ d, 1 ≤ d → d ≤ 2 → m.getMem (BitVec.ofNat 64 (frameA d+32))=0 ∧
      m.getMem (BitVec.ofNat 64 (frameA d+40))=0)
    (hmem : ∀ A, u.getMem A = m.getMem A) (h10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr d pend))
    (h11 : u.getReg .x11 = BitVec.ofNat 64 64) :
    hashInput u = toQ (T3.pad64 (pendBlk F c node pend)) := by
  have hidx := F.idx_lt
  rw [T3.pad64, pendBlk_length, show (64 - 64 % 64) % 64 = 0 by rfl, List.replicate_zero, List.append_nil]
  cases pend with
  | leaf s g =>
    obtain ⟨hs3, hs21, hg, -, hT0, hT1⟩ := hp
    have hA : pendAddr d (.leaf s g) = WIT + 64 + 48 * s := rfl
    rw [hA] at h10
    apply hashInput_words8 u _ _ (pendBlk_length F c node _) h10 (by unfold WIT; omega) (by unfold WIT; omega) h11
    simp only [hmem]
    have dP := hw.dig (64 + 48 * s) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 0 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 8 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    have dS := hw.dig (64 + 48 * s + 32) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 32 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 40 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    have dQ := hw.dig (64 + 48 * s + 48) (by omega) (by unfold WX; omega) (Or.inr (Or.inl (leafNT_of s 48 hs21 (by simp))))
      (Or.inr (Or.inl (by have := leafNT_of s 56 hs21 (by simp); simpa [Nat.add_assoc] using this)))
    simp only [pendBlk, wordsOf_blk4, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_leaf c F.idx (by omega) (by omega)]
    rw [nw9_rv g (by rw [hg]; exact F.g_lt s hs21)]
    rw [show WIT + 64 + 48 * s + 8 = WIT + (64 + 48 * s) + 8 by ring, show WIT + 64 + 48 * s = WIT + (64 + 48 * s) by ring,
      dP.1, dP.2]
    rw [show WIT + (64 + 48 * s) + 16 = leafT s by unfold leafT; ring, hT0,
      show WIT + (64 + 48 * s) + 24 = leafT s + 8 by unfold leafT; ring, hT1,
      show WIT + (64 + 48 * s) + 32 = WIT + (64 + 48 * s + 32) by ring, dS.1,
      show WIT + (64 + 48 * s) + 40 = WIT + (64 + 48 * s + 32) + 8 by ring, dS.2,
      show WIT + (64 + 48 * s) + 48 = WIT + (64 + 48 * s + 48) by ring, dQ.1,
      show WIT + (64 + 48 * s) + 56 = WIT + (64 + 48 * s + 48) + 8 by ring, dQ.2]
    simp only [wleafPad, wsecret, leafBlock]
    rw [show 64 + 48 * (s + 1) = 64 + 48 * s + 48 by ring]
  | merge heap left =>
    obtain ⟨hd, hh, -, hL, hT0, hT1, hN⟩ := hp
    have hA : pendAddr d (.merge heap left) = frameA (d + 1) := rfl
    rw [hA] at h10
    apply hashInput_words8 u _ _ (pendBlk_length F c node _) h10 (by unfold frameA; omega) (by unfold frameA; omega) h11
    simp only [hmem]
    obtain ⟨z0, z1⟩ := hpad (d + 1) (by omega) hd
    simp only [pendBlk, wordsOf_blk4, header_packed_lo_3, header_packed_hi_3, header_packed_lo_9, header_packed_hi_9, header_packed_lo_10, header_packed_hi_10, hdr0_node c F.idx (by omega) (by omega)]
    rw [nw10_rv heap (by omega)]
    rw [hL.1, hL.2, hT0, hT1, z0, z1, show frameA (d + 1) + 56 = frameA (d + 1) + 48 + 8 by ring, hN.1, hN.2]
    rfl


/-- The witness words needed by a single fold before its header is written. -/
def FoldOrig (w : WBytes) (ptr i heap : Nat) (s : MachineState) : Prop :=
  Orig w (fun o => o<64 ∨ leafNT o ∨ fblk ptr i+80 ≤ o ∨
    o=fblk ptr i+32 ∨ o=fblk ptr i+40 ∨
    (heap%2=1 ∧ (o=fblk ptr i ∨ o=fblk ptr i+8)) ∨
    (heap%2=0 ∧ (o=fblk ptr i+48 ∨ o=fblk ptr i+56))) s

theorem scheduled_rung_query (F : FCtx) (c g j i heap ptr : Nat)
    (node : Digest) (s : MachineState)
    (hc : c<7) (hg : g<42) (hj : j<5) (hi : i<(plan g j).folds)
    (hp : ptr+888 ≤ 32168) (hp8 : ptr%8=0) (he : heap<4096)
    (hpc : s.pc=pcOf (atRung (plan g j) (heap%2) i))
    (h14 : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8+80*(plan g j).folds))
    (h23 : s.getReg .x23=FtsRev.rv heap)
    (h27 : s.getReg .x27=BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx))
    (h11 : s.getReg .x11=64#64)
    (hnd : DigAt s (WIT+fblk ptr i+48*(heap%2)) node)
    (hw : FoldOrig F.w ptr i heap s) :
    ∃ t, RawRes (rungSpec (plan g j) i (heap%2) (heap/2%2)) rungKeep s t ∧
      hashInput t=toQ (T3.pad64 (foldBlk F c ptr i heap node)) := by
  have hbound := plan_bounds ⟨g,hg⟩ ⟨j,hj⟩
  dsimp only at hbound
  have hi10 : i<10 := by omega
  have hE64 : heap<2^64 := by omega
  have h14' : s.getReg .x14=BitVec.ofNat 64 (WIT+ptr+8)+
      BitVec.ofNat 64 (80*(plan g j).folds) := by
    rw [BitVec.ofNat_add_ofNat]; exact h14
  obtain ⟨t,ht⟩ := rung_run g j i (heap%2) (heap/2%2) hg hj hi10
    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hi s hpc
    (rung_br_holds _ s heap i h23 hE64)
    (rung_access _ s (WIT+ptr+8) i h14' (by unfold WIT; omega)
      (by unfold WIT; omega))
  have h10 : t.getReg .x10=BitVec.ofNat 64 (WIT+fblk ptr i) := by
    rw [ht.rung_src _ h14',BitVec.ofNat_add_ofNat]
    congr 1; unfold fblk; omega
  have h11t : t.getReg .x11=64#64 := (ht.keep .x11 (by simp [rungKeep])).trans h11
  have hh := ht.rung_header _ h14'
  have hs : shifted.eval s=FtsRev.rv (heap/2) := by
    simp only [shifted,E.eval,cE,h23]
    exact FtsRev.rv_sll1 heap hE64
  have hhdr : t.getMem (BitVec.ofNat 64 (WIT+fblk ptr i+16))=
        BitVec.ofNat 64 (hdr1 (nodeW0 c) F.idx) ∧
      t.getMem (BitVec.ofNat 64 (WIT+fblk ptr i+24))=FtsRev.rv (heap/2) := by
    simp only [BitVec.ofNat_add_ofNat,h27,hs] at hh
    have e16 : (WIT+ptr+8)+(80*i+16)=WIT+fblk ptr i+16 := by unfold fblk; omega
    have e24 : (WIT+ptr+8)+(80*i+24)=WIT+fblk ptr i+24 := by unfold fblk; omega
    rw [e16,e24] at hh
    exact hh
  refine ⟨t,ht,rung_hashInput F c ptr i heap node t s hc hp (by omega) hp8
    h10 h11t hhdr.1 hhdr.2 ?_ hnd hw he⟩
  intro k hk16 hk24 hk64
  apply ht.rung_frame _ _ h14'
  · rw [BitVec.ofNat_add_ofNat]
    apply ofNat_ne (by unfold WIT fblk; omega) (by unfold WIT; omega)
    unfold fblk; omega
  · rw [BitVec.ofNat_add_ofNat]
    apply ofNat_ne (by unfold WIT fblk; omega) (by unfold WIT; omega)
    unfold fblk; omega

#print axioms scheduled_rung_query
end SigGolfCandidate.T3M.CanonicalNative
