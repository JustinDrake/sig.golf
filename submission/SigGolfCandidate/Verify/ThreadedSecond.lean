import SigGolfCandidate.Verify.ChainHead

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem second_known (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (hsec : isSecond i = true)
    (acc : List Val) (s : MachineState) (hs : HeadInv c i acc s) :
    KnownOK (Threaded.secondK c.lay (i - 1)) s ∧ RB c i s ∧
    s.pc = pcOf (Threaded.secondHead c.lay (i - 1) (dig c i)) := by
  obtain ⟨hG,hK,hR,hCB,hZ,hLB,hlen,hvs,⟨tt,htt,hpc⟩,h14⟩ := hs
  obtain ⟨hi1, -, hsing, hfirst⟩ := isSecond_bounds i hi hsec
  have hp : hasPrep i = false := by simp [hasPrep, hsing, hfirst]
  have hk := KnownOK_append.mp hK
  have h12 : s.getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * (i - 1)) := by
    have h := hk.2 (.x12, BitVec.ofNat 64 (0x350 + 16 * i)) (by simp)
    rw [show 0x360 + 16 * (i - 1) = 0x350 + 16 * i by omega]
    exact h
  have h15 : s.getReg .x15 = BitVec.ofNat 64 (bIn c.lay i) := hk.2 (.x15, BitVec.ofNat 64 (bIn c.lay i)) (by simp)
  have he : bIn c.lay i = bVal c.lay i := by
    have hip : i - 1 + 1 = i := by omega
    have h := (tabOk_spec (tabOk_at c.lay (i - 1) hc.1 (by omega))).2.2.2.2.1
      (by omega) (by simpa [hip] using hp)
    simpa [bIn, show i ≠ 0 by omega, hip] using h.symm
  refine ⟨?_, ⟨h15.trans (congrArg (BitVec.ofNat 64) he), h14 hi hp⟩, ?_⟩
  · apply KnownOK_append.mpr
    exact ⟨hk.1, fun p hp => by rw [List.mem_singleton.mp hp]; exact h12⟩
  · simpa [CCtx.headPc, hsec] using hpc

theorem second_lt7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : ChainEvidence c i) (hlook : LookOK image Threaded.look) (hsec : isSecond i = true)
    (s : MachineState) (hs : HeadInv c i acc s) (hd : dig c i < 7) :
    ∃ t, Steps image s 6 6 t ∧ StepInv c i acc (dig c i + 1) (witChain c.wl c.lay i) t := by
  obtain ⟨hk,hB,hpc⟩ := second_known c hc i hi hsec acc s hs
  obtain ⟨hG,hK,hR,hCB,hZ,hLB,hlen,hvs,-,-⟩ := hs
  obtain ⟨hi1, -, hsing, hfirst⟩ := isSecond_bounds i hi hsec
  have hip : i - 1 + 1 = i := by omega
  obtain ⟨hrun,hok,hkn,hkeep⟩ := okC_spec (hchk.second hsec)
  rw [if_pos hd] at hkn
  obtain ⟨hst,-,hglob⟩ := Threaded.run_post hlook hrun hok s hpc hk (by simp [Threaded.secondExp])
  set r := Threaded.secondExp c.lay (i - 1) (dig c i) with hr
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hmem : r.st.mem =
      [(⟨none, BitVec.ofNat 64 0xF8⟩, ldE (chainAddr c.lay i + 8)),
       (⟨none, BitVec.ofNat 64 0xF0⟩, ldE (chainAddr c.lay i)),
       (⟨none, BitVec.ofNat 64 0xC0⟩, stH 4 (cw (0x360 + 16 * (i - 1))))] := by
    simp [hr, Threaded.secondExp, hd, hip]
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0xF8 → A ≠ 0xF0 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have hptr : chainPtr i < 65536 := chainPtr_lt i hi
  have hptrEq : chainPtr i = 0x360 + 16 * (i - 1) := by
    unfold chainPtr; rw [if_neg (by omega)]; omega
  have m0 : ((r.toState s).getMem (BitVec.ofNat 64 0xC0)).toNat =
      (s.getMem (BitVec.ofNat 64 0xC0)).toNat % 2 ^ 32 + 2 ^ 32 * chainPtr i +
      2 ^ 48 * ((s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 48) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide),
      memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
    change (StoreKind.merge .h (s.getMem (BitVec.ofNat 64 0xC0)) 4
      (BitVec.ofNat 64 (0x360 + 16 * (i - 1)))).toNat = _
    rw [stH4_toNat, ← hptrEq]
    simp only [BitVec.toNat_ofNat]
    have : chainPtr i % 2 ^ 64 % 65536 = chainPtr i := by omega
    rw [this]
  have hoff : chainAddr c.lay i = 0x800 + (witLayerOff c.lay + 16 * i) := by
    unfold chainAddr; rw [witLayerOff_eq _ hc.1]; omega
  have hlb := layBody_le _ hc.1
  have hwl := hc.2.2.2.1
  refine ⟨r.toState s, by simpa [hr, Threaded.secondExp, hd] using hst,
    hglob _ _ hG, hK', Regs_keep hR hkeep', ⟨?_,?_,?_⟩, ?_, RB_keep hB hkeep', ⟨?_,?_⟩,
    ?_, ?_, ?_, hlen, hvs, length_witChain c hc i hi, ?_, by omega⟩
  · rw [m0]; have := hCB.1; omega
  · rw [fr _ (by omega) (by omega) (by omega) (by omega)]; exact hCB.2.1
  · rw [m0]; have := hCB.2.2; omega
  · unfold CBi; rw [m0]; omega
  · rw [fr _ (by omega) (by omega) (by omega) (by omega)]; exact hZ.1
  · rw [fr _ (by omega) (by omega) (by omega) (by omega)]; exact hZ.2
  · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
    simp only [ldE, cw, E.eval]
    rw [hoff, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega)
      (by have := witLayerOff_eq _ hc.1; omega), witChain, vw0_slice]
  · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    simp only [ldE, cw, E.eval]
    rw [hoff, show 0x800 + (witLayerOff c.lay + 16 * i) + 8 = 0x800 + (witLayerOff c.lay + 16 * i + 8) by omega,
      wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega)
      (by have := witLayerOff_eq _ hc.1; omega), witChain, vw1_slice]
  · exact LBOk_frame hLB (fun j hj => by
      rw [hlen] at hj
      exact ⟨fr _ (by omega) (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega) (by omega)⟩)
  · rw [PRes.toState_pc _ _ (by simp [hr, Threaded.secondExp])]
    simp only [hr, Threaded.secondExp, if_pos hd, CCtx.s1, Threaded.chainS1, hsing, hfirst,
      Bool.false_eq_true, if_false, CCtx.d2, Threaded.secondBody, Threaded.secondHead]
    congr 1; omega

theorem second_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : ChainEvidence c i) (hlook : LookOK image Threaded.look) (hsec : isSecond i = true)
    (s : MachineState) (hs : HeadInv c i acc s) (hd : dig c i = 7) :
    ∃ t, Steps image s 5 5 t ∧ ChainDone c i (acc ++ [witChain c.wl c.lay i]) t := by
  obtain ⟨hk,hB,hpc⟩ := second_known c hc i hi hsec acc s hs
  obtain ⟨hG,hK,hR,hCB,hZ,hLB,hlen,hvs,-,-⟩ := hs
  obtain ⟨hi1, -, hsing, hfirst⟩ := isSecond_bounds i hi hsec
  have hip : i - 1 + 1 = i := by omega
  obtain ⟨hrun,hok,hkn,hkeep⟩ := okC_spec (hchk.second hsec)
  rw [if_neg (by omega)] at hkn
  obtain ⟨hst,-,hglob⟩ := Threaded.run_post hlook hrun hok s hpc hk (by simp [Threaded.secondExp])
  set r := Threaded.secondExp c.lay (i - 1) (dig c i) with hr
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hmem : r.st.mem =
      [(⟨none, BitVec.ofNat 64 (0x360 + 16 * i + 8)⟩, ldE (chainAddr c.lay i + 8)),
       (⟨none, BitVec.ofNat 64 (0x360 + 16 * i)⟩, ldE (chainAddr c.lay i))] := by
    simp [hr, Threaded.secondExp, hd, hip]
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0x360 + 16 * i + 8 → A ≠ 0x360 + 16 * i →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have hoff : chainAddr c.lay i = 0x800 + (witLayerOff c.lay + 16 * i) := by
    unfold chainAddr; rw [witLayerOff_eq _ hc.1]; omega
  have hlb := layBody_le _ hc.1
  have hwl := hc.2.2.2.1
  have hv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x360 + 16 * i)) = vw0 (witChain c.wl c.lay i) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by
      intro h; have := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at this; omega),
      memEval_cons_eq _ _ _ _ _ rfl]
    simp only [ldE, cw, E.eval]
    rw [hoff, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega)
      (by have := witLayerOff_eq _ hc.1; omega), witChain, vw0_slice]
  have hv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x360 + 16 * i + 8)) = vw1 (witChain c.wl c.lay i) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    simp only [ldE, cw, E.eval]
    rw [hoff, show 0x800 + (witLayerOff c.lay + 16 * i) + 8 = 0x800 + (witLayerOff c.lay + 16 * i + 8) by omega,
      wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega)
      (by have := witLayerOff_eq _ hc.1; omega), witChain, vw1_slice]
  refine ⟨r.toState s, by simpa [hr, Threaded.secondExp, hd] using hst,
    hglob _ _ hG, KnownOK_chK hK', Regs_keep hR hkeep', ⟨?_,?_,?_⟩, RB_keep hB hkeep', ⟨?_,?_⟩,
    ?_, by simp [hlen], ?_, ?_, ?_⟩
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.1
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.1
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.2
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.1
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.2
  · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
    · rw [hlen] at hj
      exact ⟨fr _ (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega)⟩
    · simpa [hlen] using hv0
    · rw [hlen, show 0x368 + 16 * i = 0x360 + 16 * i + 8 by omega]
      exact hv1
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hvs v hv
    · rw [List.mem_singleton.mp hv]; exact length_witChain c hc i hi
  · rw [PRes.toState_pc _ _ (by simp [hr, Threaded.secondExp])]
    simp [hr, Threaded.secondExp, hd, CCtx.endPc, Threaded.chainEnd, hsing, hfirst, CCtx.d2]
  · exact hK' (.x12, BitVec.ofNat 64 (0x360 + 16 * i))
      (List.mem_append_right _ (List.mem_singleton_self _))

end SigGolfCandidate.Verify
