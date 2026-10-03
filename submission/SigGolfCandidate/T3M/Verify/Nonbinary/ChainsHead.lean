import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCopy
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headJTerm_keeps (rb : Reg) (o : Word) (first : Bool) (tgt : Nat) :
    Keeps (headJTerm rb o first tgt) [.x10, .x25] := by
  intro x hx
  simp only [headJTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

namespace NCtx
/-- **The head of a table-slot chain** (`A = 4q`, or chain 48 in `q48tab`) with its first rung. -/
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < topMax i) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJ .x19 (off i) first (c.rungPc i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i)) 3 =
      some (rungR (c.dig i) (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (6 + (if c.dig i = last i then 2 else 1)) (6 + (if c.dig i = last i then 2 else 1)) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headJ .x19 (off i) first (c.rungPc i (c.dig i)) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJ, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJ_keeps .x19 (off i) first (c.rungPc i (c.dig i))
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  have s9 := c.s9v hk hR i hi first hfirst hfirst' h25
  have t25 : t1.getReg .x25 = BitVec.ofNat 64 (w0 i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJ]
    rw [RegFile.get_set_self _ _ (by decide), s9]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJ]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), s9]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hH : c.HdrOk i t1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).1
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).2
    · rw [tmem _ (by omega), if_pos rfl]
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i)) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, h12b, h16, hfr2, hpc2⟩ :=
    c.rung_piece hc hk i (c.dig i) (c.rungPc i (c.dig i)) hi (by omega) hp1 hrun2 t1 hpc1 hR1 t10 hH
  have hsteps : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, hst1.trans hst2, ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t25
  · rw [hfr2 _ (by omega) (by omega), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t10
  · by_cases h2 : c.dig i = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), t12, if_neg h2]
  · rw [hpc2]

/-- **The head of a table-slot chain** (`A = 4q`, or chain 48 in `q48tab`) with its first rung. -/
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJTerm .x19 (off i) first (c.rungPc i (c.dig i))))
    (hrun2 : vrun (c.rungPc i (c.dig i)) 3 =
      some (rungR (c.dig i) (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i))))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s (5 + (if c.dig i = last i then 2 else 1)) (5 + (if c.dig i = last i then 2 else 1)) t ∧
      c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  set r := headJTerm .x19 (off i) first (c.rungPc i (c.dig i)) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJTerm_keeps .x19 (off i) first (c.rungPc i (c.dig i))
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJTerm]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
  have s9 := c.s9v hk hR i hi first hfirst hfirst' h25
  have t25 : t1.getReg .x25 = BitVec.ofNat 64 (w0 i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJTerm]
    rw [RegFile.get_set_self _ _ (by decide), s9]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1 else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJTerm]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    simp only [E.eval]
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), s9]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hH : c.HdrOk i t1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).1
    · rw [tmem _ (by omega), if_neg (by omega), if_pos rfl]
      exact (w0_low0 i hi).2
    · rw [tmem _ (by omega), if_pos rfl]
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i)) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, h12b, h16, hfr2, hpc2⟩ :=
    c.rung_piece hc hk i (c.dig i) (c.rungPc i (c.dig i)) hi (by omega) hp1 hrun2 t1 hpc1 hR1 t10 hH
  have hsteps : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, hst1.trans hst2, ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_, h16,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t25
  · rw [hfr2 _ (by omega) (by omega), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]


end NCtx
end SigGolfCandidate.T3M.Nonbinary
