import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsSem

namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false

theorem tailR_keeps (slot : Option Nat) (p : Nat) : Keeps (tailR slot p) [.x12] := by
  intro x hx
  simp only [tailR]
  split
  · rw [RegFile.get_set_ne _ _ (ne_of_not_mem hx (by simp))]
  · rfl

namespace NCtx

/-- **The HASH of step `m` of chain `i`.** -/
theorem prehash_step (c : NCtx) (hc : c.ok) (s0 : MachineState) (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hd : c.dig i ≤ m)
    (acc : List Digest) (v : Digest) (t : MachineState) (ht : c.PreHash s0 i acc m v t) :
    t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = toQ (chainInputP 0 c.tree c.leaf i m (c.pad0 i) (c.pad1 i) v) ∧
      ∀ a : BitVec 256,
        (m < last i → c.StepInv s0 i acc (m + 1) (a.extractLsb' 0 128) (writeHash t a)) ∧
        (m = last i → c.EndInv s0 i (acc ++ [a.extractLsb' 0 128]) (writeHash t a)) := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h16, h24, hv, h10, h12, hpc, -⟩ := ht
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  have hs := slot_props i hi
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → t.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have t5 : t.getReg .x5 = 0 := kr _ _ (by simp [known]) (by decide)
  have t11 : t.getReg .x11 = BitVec.ofNat 64 64 := kr _ _ (by simp [known]) (by decide)
  obtain ⟨p0, p1⟩ := pads_at hc h0 hi hF
  refine ⟨t5, ?_, ?_, ?_⟩
  · apply hashArgs_const t (c.blk i) 64 (if m = last i then slot i else c.blk i + 48) h10 t11 h12 (by omega)
      (by omega) (by omega)
    · split <;> omega
    · split <;> omega
  · exact c.chain_hashInput hc i m hi (by omega) v t h10 t11 p0 p1 h16 h24 hv
  · intro a
    have hdst : ∀ (B : Nat), t.getReg .x12 = BitVec.ofNat 64 B → B + 32 < 2 ^ 64 →
        Frame t (writeHash t a) (fun A => B ≤ A ∧ A < B + 32) := fun B hB hB' => Frame.writeHash t a B hB hB'
    refine ⟨fun hm2 => ?_, fun hm2 => ?_⟩
    · have d12 : t.getReg .x12 = BitVec.ofNat 64 (c.blk i + 48) := by rw [h12, if_neg (by omega)]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.WrIn i) := (hF.trans fr).mono (by
        intro A _ h; rcases h with h | h
        · exact h
        · right; right; omega)
      have fget : ∀ A, A < 2 ^ 64 → ¬ (c.blk i + 48 ≤ A ∧ A < c.blk i + 48 + 32) →
          (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := fun A hA hn => fr A hA hn
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, hlen,
        ⟨?_, ?_, ?_⟩, DigAt.writeHash_lo t a _ d12 (by omega),
        by rw [getReg_writeHash]; exact h10, fun _ => by rw [getReg_writeHash]; exact d12, ?_⟩
      · have hj' := hS j hj
        have hsj := slot_props j (by omega)
        exact hj'.frame fr (by omega) (by omega) (by omega)
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega), h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (w0_lt i m hi (by omega))]
        unfold w0; omega
      · rw [fget _ (by omega) (by omega)]; exact h24
      · rw [pc_writeHash, hpc, if_neg (by omega), c.rungPc_succ i m hd, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1
    · subst hm2
      have d12 : t.getReg .x12 = BitVec.ofNat 64 (slot i) := by rw [h12, if_pos rfl]
      have fr := hdst _ d12 (by omega)
      have fW : Frame s0 (writeHash t a) (c.Wr (i + 1)) := (hF.trans fr).mono (by
        intro A _ h
        have := c.blk_le hc i hi
        have hlo := hc.2.2.2.1
        unfold WrIn Wr blk at *
        omega)
      refine ⟨⟨fun x hx => by rw [getReg_writeHash]; exact hR x hx, fW, fun j hj => ?_⟩, by simp [hlen], ?_⟩
      · rw [List.length_append, List.length_singleton] at hj
        by_cases hjl : j < acc.length
        · have hj' := hS j hjl
          have hsj := slot_props j (by omega)
          have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
          exact hj'.frame fr (by omega) (by omega) (by omega)
        · have hj2 : j = acc.length := by omega
          subst hj2
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
          exact DigAt.writeHash_lo t a _ d12 (by omega)
      · have hd3 : c.dig i < topMax i := by omega
        rw [pc_writeHash, hpc, if_pos rfl, ← c.rungPc_end i hi hd3, show (4 : Word) = BitVec.ofNat 64 4 from rfl,
          ofNat_add_ofNat]
        congr 1

/-- **One rung**: `sb POS_m, 20(a0)` (and `li a2, slot` for the last step), up to the `ecall`. -/
theorem rung_piece (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m p : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : p < 210432)
    (hrun : vrun p 3 = some (rungR m (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 (c.blk i)) (hH : c.HdrOk i s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ fetch vimage t = some (.base .ECALL) ∧
      (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m < last i → t.getReg .x12 = s.getReg .x12) ∧
      t.getMem (BitVec.ofNat 64 (c.blk i + 16)) = BitVec.ofNat 64 (w0 i + 2 ^ 32 * m) ∧
      Frame s t (fun A => A = c.blk i + 16) ∧ t.pc = pcOf (p + (if m = last i then 2 else 1)) := by
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  set r := rungR m (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by
    simp only [hr, rungR, List.mem_cons, List.not_mem_nil, or_false]
    rintro o (rfl | rfl)
    · show ((E.reg .x10).eval s).toNat % 8 = 0
      simp only [E.eval, h10, BitVec.toNat_ofNat]; omega
    · show accessValid (Addr.eval s ⟨some (.reg .x10), 20⟩) 1 = true
      simp only [Addr.eval, E.eval, h10]
      rw [show (20 : Word) = BitVec.ofNat 64 20 from rfl, ofNat_add_ofNat]
      exact valid_ofNat _ _ (by omega) (by omega)
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, rungR])
  have hn : r.steps = (if m = last i then 2 else 1) ∧ r.cycles = (if m = last i then 2 else 1) := by
    simp only [hr, rungR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := rungR_keeps m (if m = last i then some (slot i) else none) p
  have key : (⟨some (.reg .x10), 16⟩ : Addr).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
    simp only [Addr.eval, E.eval, h10]
    rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
  have tmem : ∀ A, A < 2 ^ 64 → (r.toState s).getMem (BitVec.ofNat 64 A) =
      if A = c.blk i + 16 then
        StoreKind.merge .b (s.getMem (BitVec.ofNat 64 (c.blk i + 16))) 4 (BitVec.ofNat 64 m)
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [Result.toState_getMem]
    simp only [hr, rungR]
    rw [memEval_one s _ _ (c.blk i + 16) A key (by omega) hA]
    split
    · have e1 : (addC (E.reg .x10) 16).eval s = BitVec.ofNat 64 (c.blk i + 16) := by
        rw [addC_eval]; simp only [E.eval, h10]
        rw [show (16 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_add_ofNat]
      simp only [E.eval, BinOp.eval]
      rw [e1, c.posE_eval hk hR i m hm]
    · rfl
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_, ?_,
    fun A hA hn => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, rungR, if_neg (show m ≠ last i by omega)]
    rw [RegFile.init_get_eval]
  · rw [tmem _ (by omega), if_pos rfl]
    obtain ⟨hl, hj, -⟩ := hH
    rw [stepByte _ _ _ _ (by omega) (by omega) (by omega) hl hj]
    congr 1; unfold w0; ring
  · rw [tmem _ hA, if_neg hn]
  · rw [Result.toState_pc]; simp only [hr, rungR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- T3Z: **the rest of a table-slot chain's first rung** after its `sb` (the head's jump target): `[li a2, slot]`,
up to the `ecall`. -/
theorem tail_piece (i m p : Nat) (hp : p < 210432)
    (hrun : vrun p 2 = some (tailR (if m = last i then some (slot i) else none) p)) (s : MachineState)
    (hpc : s.pc = pcOf p) :
    ∃ t, Steps vimage s (if m = last i then 1 else 0) (if m = last i then 1 else 0) t ∧
      fetch vimage t = some (.base .ECALL) ∧ (∀ x, x ≠ .x12 → t.getReg x = s.getReg x) ∧
      (m = last i → t.getReg .x12 = BitVec.ofNat 64 (slot i)) ∧ (m ≠ last i → t.getReg .x12 = s.getReg .x12) ∧
      Frame s t (fun _ => False) ∧ t.pc = pcOf (p + (if m = last i then 1 else 0)) := by
  set r := tailR (if m = last i then some (slot i) else none) p with hr
  have hobl : ∀ o ∈ r.st.obl, o.holds s := by simp [hr, tailR]
  have hst := piece_steps45 hrun hp s hpc hobl
  have hec := piece_ecall45 hrun hp s hobl (by simp [hr, tailR])
  have hn : r.steps = (if m = last i then 1 else 0) ∧ r.cycles = (if m = last i then 1 else 0) := by
    simp only [hr, tailR]; split <;> simp_all
  rw [hn.1, hn.2] at hst
  have hkeep := tailR_keeps (if m = last i then some (slot i) else none) p
  refine ⟨r.toState s, hst, hec, fun x hx => hkeep.reg s (by simpa using hx), fun h2 => ?_, fun h2 => ?_,
    fun A hA _ => ?_, ?_⟩
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_pos h2]
    rw [RegFile.get_set_self _ _ (by decide)]; rfl
  · rw [Result.toState_getReg]
    simp only [hr, tailR, if_neg h2]
    rw [RegFile.init_get_eval]
  · rw [Result.toState_getMem]; simp [hr, tailR, memEval]
  · rw [Result.toState_pc]; simp only [hr, tailR]
    by_cases h2 : m = last i <;> simp [h2, E.eval]

/-- **A rung after a step's hash.** -/
theorem rung_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (i m : Nat) (hi : i < 54) (hm : m ≤ last i) (hp : c.rungPc i m < 210432)
    (hrun : vrun (c.rungPc i m) 3 = some (rungR m (if m = last i then some (slot i) else none) (c.rungPc i m)))
    (acc : List Digest) (v : Digest) (s : MachineState) (hs : c.StepInv s0 i acc m v s) :
    ∃ t, Steps vimage s (if m = last i then 2 else 1) (if m = last i then 2 else 1) t ∧ c.PreHash s0 i acc m v t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hH, hv, h10, h12, hpc⟩ := hs
  have hb := c.blk_props hc i hi
  have hlast := last_bounds i
  have hmax := topMax_bounds i
  have hlastEq : last i + 1 = topMax i := by unfold last; omega
  obtain ⟨t, hst, hec, hreg, h12a, h12b, h16, hfr, hpc'⟩ :=
    c.rung_piece hc hk i m (c.rungPc i m) hi hm hp hrun s hpc hR h10 hH
  refine ⟨t, hst, ⟨⟨fun x hx => ?_, (hF.trans hfr).mono ?_, fun j hj => ?_⟩, hlen, h16, ?_, ?_, ?_, ?_, ?_, hec⟩⟩
  · rw [hreg x (ne_of_not_mem hx (by simp [chainRegs]))]; exact hR x hx
  · intro A _ h; rcases h with h | h
    · exact h
    · right; left; omega
  · have hsj := slot_props j (by omega)
    exact (hS j hj).frame hfr (by omega) (by omega) (by omega)
  · rw [hfr _ (by omega) (by omega)]; exact hH.2.2
  · exact hv.frame hfr (by omega) (by omega) (by omega)
  · rw [hreg _ (by decide)]; exact h10
  · by_cases h2 : m = last i
    · rw [h12a h2, if_pos h2]
    · rw [h12b (by omega), h12 (by omega), if_neg h2]
  · rw [hpc']

end NCtx
end SigGolfCandidate.T3M.Nonbinary
