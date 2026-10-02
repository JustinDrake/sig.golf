import SigGolfCandidate.Sign.TreeLeaf

/-! The omitted level-zero cache node is reconstructed by the ordinary full-leaf chains.
The capture leaf differs from the reconstructed sibling, so the signature values are preserved. -/

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def siblingW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨
    (0x140 ≤ a ∧ a < 0x160) ∨ (0x360 ≤ a ∧ a < 0x600) ∨
    (0xBA8 ≤ a ∧ a < 0xBC8)

def siblingRegs : List Reg := chainRegs ++ [.x15, .x17, .x19, .x20]

def SiblingPost (tl : MachineState) (v : Val) (t : MachineState) : Prop :=
  v.length = 16 ∧ Slots t 0xBA8 [v] ∧ t.pc = pcOf 689 ∧
    t.getReg .x15 = 1 ∧ t.getReg .x17 = 16384 ∧ t.getReg .x19 = 0xCB20 ∧
    RegsEq tl t siblingRegs ∧ Frame tl t siblingW

/-- Exit from the shared leaf loop into the positive-level cache path. -/
def siblingExit (t : MachineState) : MachineState :=
  blk2981.res.toState (blk2980.res.toState (blk591.res.toState (blk589.res.toState t)))

theorem sibling_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (e ep : Nat)
    (hne : ep ≠ e) (tl : MachineState) (ctx : ChainCtx S x ⟨0, 0, e, ep, 0x900⟩ tl)
    (hpc : tl.pc = pcOf 529) (h21 : tl.getReg .x21 = 0) (h24 : tl.getReg .x24 = 0)
    (h8 : tl.getReg .x8 = 0) (h17 : tl.getReg .x17 = BitVec.ofNat 64 (ep + 1))
    (h19 : tl.getReg .x19 = BitVec.ofNat 64 0xBA8 - BitVec.ofNat 64 (16 * ep))
    (hlb0 : tl.getMem (BitVec.ofNat 64 0x340) = twWord0 3 1 0 0)
    (hlb8 : tl.getMem (BitVec.ofNat 64 0x348) = BitVec.ofNat 64 (2 ^ 32 * ep))
    (hlbP : tl.readWords (BitVec.ofNat 64 0x350) 2 = [0, 0]) :
    Sim image tl (21 * 844 + (4 + (88 + 9)))
      (Prod.fst <$> buildLeaf S 0 0 ep x) (SiblingPost tl) := by
  have hep : ep < 2048 := ctx.hep
  have he : e < 2048 := ctx.he
  rw [map_eq_bind_pure_comp, buildLeaf_bind]
  simp only [Function.comp_apply, pure_bind]
  refine Sim.bind (chains_sim S hS x ⟨0, 0, e, ep, 0x900⟩ tl ctx hpc h21 h24)
    (fun cs t2 h2 => ?_)
  obtain ⟨-, hc1, hc2, hv1, hv2, hends, hcaps, pc2, -, -, cr, cf, clo1, clo2⟩ := h2
  have pc2' : t2.pc = pcOf 584 := by rw [pc2]; rfl
  have x220 : t2.getReg .x20 = BitVec.ofNat 64 ep := by rw [cr.get .x20, ctx.x20]
  have x219 : t2.getReg .x19 = BitVec.ofNat 64 0xBA8 - BitVec.ofNat 64 (16 * ep) := by
    rw [cr.get .x19, h19]
  have hs3 := symRun_sound blk584 codeAt_584 t2 pc2' (by simp only [blk584.res, rv_simp])
  have hc3 : blk584.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk584.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro a ha hW; simp [blk584.res]
  have r3 : RegsEq t2 t3 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 := symRun_ecall blk584 codeAt_584 t2 (by simp only [blk584.res, rv_simp]) rfl
  have x10 : t3.getReg .x10 = BitVec.ofNat 64 0x340 := by simp only [ht3, blk584.res, rv_simp]
  have x11 : t3.getReg .x11 = BitVec.ofNat 64 704 := by simp only [ht3, blk584.res, rv_simp]
  have x12 : t3.getReg .x12 = BitVec.ofNat 64 0xBA8 := by
    simp only [ht3, blk584.res, rv_simp, x220, x219]
    bvsimp []
    rw [show ep * 16 = 16 * ep by omega, BitVec.sub_add_cancel]
  have x5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, cr.get .x5, ctx.x5]
  have pc3 : t3.pc = pcOf 588 := by simp only [ht3, blk584.res, rv_simp]
  have fl3 : Frame tl t3 (chainW ⟨0, 0, e, ep, 0x900⟩) := (cf.trans f3).mono (by
    intro a ha; rcases ha with h | h; exact h; exact h.elim)
  have hq : hashInput t3 = pad64 (thInput (tweak 3 1 0 0 ep) cs.1.flatten) := by
    obtain ⟨hn, hw⟩ := words_thVals 3 1 0 0 ep cs.1 hv1 10 (by rw [hc1])
    refine hashInput_eq_pad64 t3 _ 10 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (10 + 1) = 1 + 1 + 2 + 2 * 42 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      fl3.getMem (by norm_num) (by simp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega), hlb0,
      fl3.getMem (by norm_num) (by simp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega), hlb8,
      fl3.readWords _ _ (by norm_num)
        (by intro i hi; simp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega), hlbP,
      show (84 : Nat) = 2 * cs.1.length by rw [hc1],
      f3.readWords _ _ (by rw [hc1]; norm_num) (by simp), readWords_slots t2 0x360 cs.1 hends]
    simp only [twWords_eq, twWord0, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨?_, trivial⟩
    congr 1
    rw [Nat.mod_eq_of_lt (by omega : ep < 2 ^ 32)]
    omega
  have hb : (fmt (leafInput 0 0 ep cs.1)).blocks = 11 := by
    rw [show fmt (leafInput 0 0 ep cs.1)=pad64 (leafInput 0 0 ep cs.1) from fmt_thInput _ _ _ _ _ _ (by decide)]
    exact congrArg (· + 1) (words_thVals 2 0 0 0 ep cs.1 hv1 10 (by rw [hc1])).1
  refine (Sim.steps hs3 (Sim.hash16_bindF (W := 9) e3 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)) (hq.trans (addrFmt_leafInput_carry 0 0 ep cs.1 (by decide) (by decide) hc1 hv1).symm) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t4 := writeHash t3 a with ht4
  have f4 : Frame t3 t4 (fun z => 0xBA8 ≤ z ∧ z < 0xBC8) :=
    frame_writeHash t3 a _ x12 (by norm_num)
  have v4 : t4.readWords (BitVec.ofNat 64 0xBA8) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t3 a _ x12 (by norm_num)
  have pc4 : t4.pc = pcOf 589 := by rw [ht4, writeHash_pc, pc3]; apply BitVec.eq_of_toNat_eq; simp
  have x420 : t4.getReg .x20 = BitVec.ofNat 64 ep := by rw [ht4, writeHash_getReg, r3.get .x20, x220]
  have x417 : t4.getReg .x17 = BitVec.ofNat 64 (ep + 1) := by
    rw [ht4, writeHash_getReg, r3.get .x17, cr.get .x17, h17]
  have x48 : t4.getReg .x8 = 0 := by rw [ht4, writeHash_getReg, r3.get .x8, cr.get .x8, h8]
  have hs50 := symRun_sound blk589 codeAt_589 t4 pc4 (by simp only [blk589.res, rv_simp])
  have hs51 := symRun_sound blk591 codeAt_591 (blk589.res.toState t4)
    (by simp only [blk589.res, rv_simp, x420, x417, ofNat_add_ofNat, bne_self_eq_false, Bool.false_eq_true, if_false])
    (by simp only [blk591.res, rv_simp])
  have hs52 := symRun_sound blk2980 codeAt_2980 (blk591.res.toState (blk589.res.toState t4))
    (by simp only [blk591.res, rv_simp]) (by simp only [blk2980.res, rv_simp])
  have hs53 := symRun_sound blk2981 codeAt_2981
    (blk2980.res.toState (blk591.res.toState (blk589.res.toState t4)))
    (by simp only [blk2980.res, blk591.res, blk589.res, rv_simp, x48, bne_self_eq_false, Bool.false_eq_true, if_false])
    (by simp only [blk2981.res, rv_simp])
  have hs5 : Steps image t4 9 9 (siblingExit t4) := hs50.trans (hs51.trans (hs52.trans hs53))
  set t5 := siblingExit t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by intro z hz hW; rfl
  have r5 : RegsEq t4 t5 [.x15, .x17, .x19, .x20] := by
    intro r hr
    simp only [ht5, siblingExit, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine Sim.pure_steps hs5 ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Slots.snoc (Slots.nil _ _) (by simpa using f5.readWords _ _ (by norm_num) (by simp) |>.trans v4)
  · simp only [ht5, siblingExit, blk2981.res, rv_simp]
  · simp only [ht5, siblingExit, blk2981.res, rv_simp]
  · simp only [ht5, siblingExit, blk2981.res, rv_simp]
  · simp only [ht5, siblingExit, blk2981.res, rv_simp]
  · exact (((cr.trans r3).trans (regsEq_writeHash _ _ [])).trans r5).mono (by decide)
  · exact ((fl3.trans f4).trans f5).mono (by
      intro z hz
      simp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl] at hz
      simp only [siblingW]
      rcases hz with (h | h) | h
      · tauto
      · tauto
      · exact h.elim)

end SigGolfCandidate.Sign
