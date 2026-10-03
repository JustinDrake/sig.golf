import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsHead
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx
/-- **The head of an inline chain** (`B`, `C`, `D`) with its first rung. -/
theorem headR_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hi0 : i ≠ 0) (hd : c.dig i < topMax i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 5)
    (hrun : vrun (c.startPc i) 8 =
      some (headR .x19 (off i) (c.dig i) (if c.dig i = last i then some (slot i) else none) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (if c.dig i = last i then 7 else 6) (if c.dig i = last i then 7 else 6) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headR .x19 (off i) (c.dig i) (if c.dig i = last i then some (slot i) else none) (c.startPc i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl | rfl)
    · show ((E.reg .x19).eval s).toNat % 8 = 0
      simp only [E.eval, h19, BitVec.toNat_ofNat]; have := hc.2.2.1; omega
    · show accessValid ((kAt .x19 (off i) 20).eval s) 1 = true
      rw [keyE 20 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headR])
  have hn : r.steps = (if c.dig i = last i then 7 else 6) ∧ r.cycles = (if c.dig i = last i then 7 else 6) := by
    simp only [hr, headR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := headR_keeps .x19 (off i) (c.dig i) (if c.dig i = last i then some (slot i) else none) (c.startPc i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have bumpv : bumpE.eval s = BitVec.ofNat 64 (w0 i) := by
    simp only [bumpE, E.eval, BinOp.eval]
    rw [h25 hi0, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headR]
    rw [memEval_two s _ _ _ _ (c.blk i + 16) (c.blk i + 24) A (keyE 16 (by omega)) (keyE 24 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval, BinOp.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), bumpv, c.posE_eval hk hR i _ (by omega)]
    split
    · obtain ⟨hl, hj⟩ := w0_low0 i hi
      rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
      congr 1; unfold w0; ring
    · rfl
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_self _ _ (by decide), bumpv]
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    by_cases h2 : c.dig i = last i
    · simp only [h2, if_true, E.eval]
    · simp only [h2, if_false]
      rw [addC_eval, a0e, show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  · rw [Result.toState_pc]; simp only [hr, headR, hrp]
    by_cases h2 : c.dig i = last i <;> simp [h2, E.eval]

/-- **The head of an inline chain** (`B`, `C`, `D`) with its first rung. -/
theorem headRTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hi0 : i ≠ 0) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hrp : c.rungPc i (c.dig i) = c.startPc i + 4)
    (hrun : vrun (c.startPc i) 8 =
      some (headRTerm .x19 (off i) (c.dig i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headRTerm .x19 (off i) (c.dig i) (slot i) (c.startPc i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headRTerm, headR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl | rfl)
    · show ((E.reg .x19).eval s).toNat % 8 = 0
      simp only [E.eval, h19, BitVec.toNat_ofNat]; have := hc.2.2.1; omega
    · show accessValid ((kAt .x19 (off i) 20).eval s) 1 = true
      rw [keyE 20 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp0 s hpc hobl
  have hec := piece_ecall45 hrun hp0 s hobl (by simp [hr, headRTerm, headR])
  have hn : r.steps = 6 ∧ r.cycles = 6 := by
    exact ⟨rfl, rfl⟩
  rw [hn.1, hn.2] at hst
  have hkeep := headR_keeps .x19 (off i) (c.dig i) (some (slot i)) (c.startPc i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have bumpv : bumpE.eval s = BitVec.ofNat 64 (w0 i) := by
    simp only [bumpE, E.eval, BinOp.eval]
    rw [h25 hi0, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, headRTerm, headR]
    rw [memEval_two s _ _ _ _ (c.blk i + 16) (c.blk i + 24) A (keyE 16 (by omega)) (keyE 24 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval, BinOp.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), bumpv, c.posE_eval hk hR i _ (by omega)]
    split
    · obtain ⟨hl, hj⟩ := w0_low0 i hi
      rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
      congr 1; unfold w0; ring
    · rfl
  have hfr : Frame s (r.toState s) (fun A => A = c.blk i + 16 ∨ A = c.blk i + 24) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx),
    (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, ?_, ?_, ?_, hv0.frame hfr (by omega) (by omega) (by omega),
    ?_, ?_, ?_, hec⟩⟩
  · intro A _ h
    rcases h with h | h
    · exact Or.inl h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [Result.toState_getReg]; simp only [hr, headRTerm, headR]
    rw [RegFile.get_set_self _ _ (by decide), bumpv]
  · rw [tmem _ (by omega), if_pos rfl]
  · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [Result.toState_getReg]; simp only [hr, headRTerm, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  · rw [Result.toState_getReg]; simp only [hr, headRTerm, headR]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]
    simp only [hd, if_true, E.eval]
  · rw [Result.toState_pc]; simp only [hr, headRTerm, headR, hrp]
    simp [hd, E.eval]


end NCtx
end SigGolfCandidate.T3M.Nonbinary
