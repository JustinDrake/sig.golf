import SigGolfCandidate.Sign.TreeLevel

/-!
# `sign`, tree_build as a whole (instructions 510 .. 603)

`tree_sim` : from `tb_leaf_loop` (`EP = 0`) the machine refines `buildTree S lay tau h e x`: the
root's two children in the node buffer (`0x1e0 .. 0x1ff`, the input of the root hash), the captured chain
values at `SIGL + 8`, the path at `SIGL + 680`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def treeW (p : TreePar) (a : Nat) : Prop := leavesW p a ∨ tlevW p a

def treeRegs : List Reg := leavesRegs ++ [.x15] ++ tlevRegs

/-- Result of tree_build. -/
def TreePost (p : TreePar) (tt : MachineState) (r : Val × List Val × List Val) (t : MachineState) :
    Prop :=
  t.pc = pcOf 630 ∧ r.1.length = 32 ∧ t.readWords (BitVec.ofNat 64 0x1E0) 4 = wordsOf r.1 ∧
  r.2.1.length = 42 ∧ (∀ v ∈ r.2.1, v.length = 16) ∧ Slots t (p.sigl + 8) r.2.1 ∧
  r.2.2.length = p.h ∧ (∀ v ∈ r.2.2, v.length = 16) ∧ Slots t (p.sigl + 680) r.2.2 ∧
  RegsEq tt t treeRegs ∧ Frame tt t (treeW p)

theorem buildTree_eq (S : List Byte) (lay tau h e : Nat) (x : List Nat) :
    buildTree S lay tau h e x =
      buildLeaves S lay tau h e x >>= fun q =>
        (List.range' 1 (h - 1)).foldlM (levelStep (nodeInput lay tau) e) (q.1, []) >>= fun st =>
          levelStep (nodeInput lay tau) e st h >>= fun st' =>
            pure (st.1.getD 0 [] ++ st.1.getD 1 [], q.2, st'.2) := by
  simp only [buildTree, buildLevels, bind_assoc, pure_bind]

/-- Cycle bound of tree_build. -/
def treeCyc : Nat := 64 * tleafCyc + (4 + 6 * 853)

/-- The non-top tree returns through the shared leaf dispatcher. -/
def treeEntryState (t : MachineState) : MachineState :=
  blk2986.res.toState (blk2980.res.toState (blk591.res.toState t))

theorem tree_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (h1 : 1 ≤ p.h) (hpc : tt.pc = pcOf 522)
    (h20 : tt.getReg .x20 = BitVec.ofNat 64 0) :
    Sim image tt treeCyc (buildTree S p.lay p.tau p.h p.e x) (TreePost p tt) := by
  have hh := ctx.hh
  have h32 := pow_le32 p.h hh
  have hsig := ctx.hsigl
  have hlay := ctx.hlay
  rw [buildTree_eq]
  have hW : 2 ^ p.h * tleafCyc + (4 + p.h * 853) ≤ treeCyc := by
    unfold treeCyc
    have := Nat.mul_le_mul_right tleafCyc h32
    have := Nat.mul_le_mul_right 853 hh
    omega
  refine (Sim.bind (leaves_sim S hS x p tt ctx hpc h20) (fun q t2 h2 => ?_)).mono hW
    (fun _ _ h => h)
  obtain ⟨-, hlv, hlvv, hlvs, hcap, pc2, -, lregs, lframe, -, -⟩ := h2
  obtain ⟨hc1, hc2, hc3⟩ := hcap ctx.he
  have pc2' : t2.pc = pcOf 591 := by rw [pc2, if_neg (lt_irrefl _)]
  have hlay0 : p.lay ≠ 0 := by
    intro hz
    have ht := ctx.hheight
    rw [hz, show height 0 = 11 from rfl] at ht
    omega
  have x28 : t2.getReg .x8 ≠ 0 := by
    rw [lregs.get .x8, ctx.x8]
    intro hz
    have hh0 := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at hh0
    rw [Nat.mod_eq_of_lt (by omega)] at hh0
    exact hlay0 hh0
  have hs30 := symRun_sound blk591 codeAt_591 t2 pc2' (by simp only [blk591.res, rv_simp])
  have hs31 := symRun_sound blk2980 codeAt_2980 (blk591.res.toState t2)
    (by simp only [blk591.res, rv_simp]) (by simp only [blk2980.res, rv_simp])
  have hs32 := symRun_sound blk2986 codeAt_2986 (blk2980.res.toState (blk591.res.toState t2))
    (by
      simp only [blk2980.res, blk591.res, rv_simp, bne_iff_ne]
      split
      · rfl
      · rename_i hn
        exact False.elim (hn x28))
    (by simp only [blk2986.res, rv_simp])
  have hs3 : Steps image t2 4 4 (treeEntryState t2) := hs30.trans (hs31.trans hs32)
  set t3 := treeEntryState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    intro a ha hW
    rfl
  have r3 : RegsEq t2 t3 [.x15] := by
    intro r hr
    simp only [ht3, treeEntryState, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq tt t3 (leavesRegs ++ [.x15]) := lregs.trans r3
  have ft3 : Frame tt t3 (leavesW p) := (lframe.trans f3).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have vctx : TLevCtx p t3 := by
    refine ⟨ctx.hlay, ctx.htau, ⟨h1, hh⟩, ctx.he, ctx.hsigl, ctx.hheight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt3.get .x5, ctx.x5]
    · rw [rt3.get .x8, ctx.x8]
    · rw [rt3.get .x9, ctx.x9]
    · rw [rt3.get .x13, ctx.x13]
    · rw [rt3.get .x18, ctx.x18]
    · rw [rt3.get .x19, ctx.x19]
    · rw [rt3.get .x30, ctx.x30]
    · have := ctx.hsigl
      rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.nbP]
  have e45 : 17 + (2 ^ (p.h - 1 - (p.h - 1)) * 26 + 2) = 45 := by rw [Nat.sub_self]; rfl
  refine (Sim.steps hs3 (Sim.bind (W₂ := 45) (tlevels_sim p t3 vctx q.1 hlv hlvv
    (hlvs.frame f3 (by omega) (by simp)) (by simp only [ht3, treeEntryState, blk2986.res, blk2980.res, blk591.res, rv_simp])
    (by simp only [ht3, treeEntryState, blk2986.res, blk2980.res, blk591.res, rv_simp]) (by rw [rt3.get .x17, ctx.x17])
    (p.h - 1) (by omega))
    (fun st t3' h3' => ?_))).mono (by omega) (fun _ _ h => h)
  -- the last level: the root; its two inputs stay in the node buffer
  have hlast := tlevel_body2 p t3 vctx (p.h - 1) (by omega) st t3' h3'
  rw [show 1 + (p.h - 1) = p.h by omega] at hlast
  obtain ⟨-, hl3, hv3, -, -, -, -, -, -, -, -, -⟩ := h3'
  have hl3' : st.1.length = 2 := by rw [hl3, show p.h - (p.h - 1) = 1 by omega]; rfl
  refine (Sim.bind (W₂ := 0) hlast (fun st' t4 h4 => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨h4, hnL, hnR⟩ := h4
  rw [show p.h - 1 + 1 = p.h by omega] at h4
  rw [show 2 * (2 ^ (p.h - 1 - (p.h - 1)) - 1) = 0 by rw [Nat.sub_self]; rfl] at hnL hnR
  obtain ⟨-, hl4, hv4, hs4, hp4, hpv4, hps4, pc4, -, -, vregs, vframe⟩ := h4
  have hLl : (st.1.getD 0 []).length = 16 := by
    rw [getD_of_lt (by rw [hl3']; norm_num)]; exact hv3 _ (List.getElem_mem _)
  have hRl : (st.1.getD 1 []).length = 16 := by
    rw [getD_of_lt (by rw [hl3']; norm_num)]; exact hv3 _ (List.getElem_mem _)
  refine Sim.pure ⟨by rw [pc4, if_neg (lt_irrefl _)], ?_, ?_, hc1, hc2, ?_, hp4, hpv4, hps4, ?_, ?_⟩
  · show (st.1.getD 0 [] ++ st.1.getD 1 []).length = 32
    rw [List.length_append, hLl, hRl]
  · have e := readWords_ofNat_add t4 0x1E0 2 2
    rw [show (2 + 2 : Nat) = 4 from rfl, show (0x1E0 + 8 * 2 : Nat) = 496 from rfl] at e
    rw [e, wordsOf_append _ _ (by omega)]
    exact congrArg₂ (· ++ ·) hnL hnR
  · refine hc3.frame (f3.trans vframe) (by rw [hc1]; omega) ?_
    intro i hi; rw [hc1] at hi
    have := ctx.hsigl; have := ctx.hlay
    constructor <;> (simp only [tlevW, or_false, false_or]; omega)
  · exact (rt3.trans vregs).mono (by decide)
  · exact (ft3.trans (f3.trans vframe)).mono (by
      intro x hx; simp only [treeW]; rcases hx with h | h | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr h)

end SigGolfCandidate.Sign
