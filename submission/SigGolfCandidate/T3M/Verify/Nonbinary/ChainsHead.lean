import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsCopy
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem headJD_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJD rb o tgt i d) [.x10, .x12, .x25] := by
  intro x hx
  simp only [headJD]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)),
    RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

theorem headJDTerm_keeps (rb : Reg) (o : Word) (tgt i d : Nat) :
    Keeps (headJDTerm rb o tgt i d) [.x10, .x25] := by
  intro x hx
  simp only [headJDTerm]
  rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp)), RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]

namespace NCtx
/-- **The head of a table-slot chain** (`A = 3q`; T3Z: the header word of chain `i` with its first digit read from
the header table, then `j` past the first rung's `sb`) up to the first `ecall` (6 steps). -/
theorem headJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i < last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJD .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJD, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJD_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide),
      a0e]
  have t12 : t1.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJD]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), addC_eval, a0e,
      show (48 : Word) = BitVec.ofNat 64 48 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJD]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, -, h12b, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 6 ∧ r.cycles = 6 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  have hn : c.dig i ≠ last i := by omega
  rw [if_neg hn] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12b hn, t12, if_neg hn]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)

/-- **The head of a table-slot chain at the penultimate digit** (`A = 3q`; no `addi a2, a0, 48`; T3Z: the header
word with the first digit read from the header table, then `j` to the rung's `li a2, slot`) up to the `ecall`
(6 steps). -/
theorem headJTerm_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hd : c.dig i = last i)
    (hp0 : c.startPc i < 210432) (hp1 : c.rungPc i (c.dig i) + 1 < 210432)
    (hrun1 : vrun (c.startPc i) 7 = some (headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)))
    (hrun2 : vrun (c.rungPc i (c.dig i) + 1) 2 =
      some (tailR (if c.dig i = last i then some (slot i) else none) (c.rungPc i (c.dig i) + 1)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.PreHash s0 i acc (c.dig i) (c.val i) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  have keyE := c.kAt_eval hc h19 i hi
  have htable := c.header_load hc h0 i (c.dig i) hi (by omega) hF (kr _ _ (by simp [known]) (by decide))
  set r := headJDTerm .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i) with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, headJDTerm, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl | rfl)
    · show accessValid ((kAt .x19 (off i) 24).eval s) 8 = true
      rw [keyE 24 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · show accessValid ((kAt .x19 (off i) 16).eval s) 8 = true
      rw [keyE 16 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
    · exact htable.1
  have hst1 := piece_steps45 hrun1 hp0 s hpc hobl
  set t1 := r.toState s with ht1
  have hkeep := headJDTerm_keeps .x19 (off i) (c.rungPc i (c.dig i) + 1) i (c.dig i)
  have a0e : (addC (E.reg .x19) (off i)).eval s = BitVec.ofNat 64 (c.blk i) := by
    rw [addC_eval]; simp only [E.eval, h19]; exact c.base_off0 hc i hi
  have t10 : t1.getReg .x10 = BitVec.ofNat 64 (c.blk i) := by
    rw [ht1, Result.toState_getReg]; simp only [hr, headJDTerm]
    rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide), a0e]
  have tmem : ∀ A, A < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 24 then BitVec.ofNat 64 c.w1
      else if A = c.blk i + 16 then BitVec.ofNat 64 (w0 i + 2 ^ 32 * c.dig i)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [ht1, Result.toState_getMem]
    simp only [hr, headJDTerm]
    rw [memEval_two s _ _ _ _ (c.blk i + 24) (c.blk i + 16) A (keyE 24 (by omega)) (keyE 16 (by omega))
      (by omega) (by omega) hA]
    change (if A = c.blk i + 24 then s.getReg .x4 else if A = c.blk i + 16 then (hLoad i (c.dig i)).eval s
      else s.getMem (BitVec.ofNat 64 A)) = _
    rw [kr .x4 (BitVec.ofNat 64 c.w1) (by simp [known]) (by decide), htable.2]
  have hfr1 : Frame s t1 (fun A => A = c.blk i + 24 ∨ A = c.blk i + 16) := by
    intro A hA hn
    rw [tmem A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  have hR1 : ∀ x ∉ chainRegs, t1.getReg x = s0.getReg x := fun x hx =>
    (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx)
  have hpc1 : t1.pc = pcOf (c.rungPc i (c.dig i) + 1) := by rw [ht1, Result.toState_pc]; rfl
  obtain ⟨t, hst2, hec, hreg, h12a, -, hfr2, hpc2⟩ :=
    tail_piece i (c.dig i) (c.rungPc i (c.dig i) + 1) hp1 hrun2 t1 hpc1
  have hsteps : r.steps = 5 ∧ r.cycles = 5 := ⟨rfl, rfl⟩
  rw [hsteps.1, hsteps.2] at hst1
  rw [if_pos hd] at hst2
  have hv0 : DigAt s (c.blk i + 48) (c.val i) := val_at hc h0 hi hF
  refine ⟨t, (hst1.trans hst2).of_eq (by norm_num) (by norm_num),
    ⟨⟨fun x hx => ?_, ((hF.trans hfr1).trans hfr2).mono ?_, fun j hj => ?_⟩, hlen, ?_,
    ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR1 x hx
  · intro A _ h
    rcases h with (h | h) | h
    · exact Or.inl h
    · right; left; omega
    · exact False.elim h
  · have hsj := slot_props j (by omega)
    exact ((hS j hj).frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [hfr2 _ (by omega) (by simp), tmem _ (by omega), if_pos rfl]
  · exact (hv0.frame hfr1 (by omega) (by omega) (by omega)).frame hfr2 (by omega) (by simp) (by simp)
  · rw [hreg _ (by decide)]; exact t10
  · rw [h12a hd, if_pos hd]
  · rw [hpc2]; all_goals (congr 1 <;> split_ifs <;> omega)


end NCtx
end SigGolfCandidate.T3M.Nonbinary
