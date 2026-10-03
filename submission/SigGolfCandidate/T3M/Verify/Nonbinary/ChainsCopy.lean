import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsHash
namespace SigGolfCandidate.T3M.Nonbinary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option linter.unusedSimpArgs false
namespace NCtx

theorem kAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) : (kAt .x19 (off i) k).eval s = BitVec.ofNat 64 (c.blk i + k) := by
  simp only [kAt, Addr.eval, E.eval, h19]
  exact c.base_off hc i hi k hk

theorem lAt_eval (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (k : Nat) (hk : k ≤ 80) :
    (lAt .x19 (off i) k).eval s = s.getMem (BitVec.ofNat 64 (c.blk i + k)) := by
  simp only [lAt, E.eval, addC_eval, h19]
  rw [c.base_off hc i hi k hk]

/-- T3Z (BIG3, the table-load proof of erickeigen's 59cbf8ec / our T3X `LCtx.header_load` on the top layer): a
head's header load `ld s9, hOff i d(t3)` reads word `8 i + d` of the header table's bank 0, which the chain phase
never writes (its frame lies below `0x7000`). -/
theorem header_load (c : NCtx) (hc : c.ok) {s0 s : MachineState} (h0 : c.Orig0 s0) (i d : Nat)
    (hi : i < 54) (hd : d < 8) (hF : Frame s0 s (c.Wr i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (Verify.headerBank 0 0)) :
    (Oblig.valid (hKey i d) 8).holds s ∧
      (hLoad i d).eval s = BitVec.ofNat 64 (w0 i + 2 ^ 32 * d) := by
  have hb := c.blk_props hc 0 (by omega)
  have hA : 2 ^ 23 + 4096 ≤ Verify.HDATA + 4096 * 0 + 64 * i + 8 * d ∧
      Verify.HDATA + 4096 * 0 + 64 * i + 8 * d + 8 ≤ 2 ^ 24 := by
    unfold Verify.HDATA; omega
  have key : (hKey i d).eval s = BitVec.ofNat 64 (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
    simp only [hKey, Addr.eval, E.eval, h28, hOff]
    change BitVec.ofNat 64 (Verify.headerBank 0 0) +
      (BitVec.ofNat 64 (64 * i + 8 * d) - BitVec.ofNat 64 2048) =
        BitVec.ofNat 64 (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)
    rw [ofNat_add_off0 (Verify.headerBank 0 0) (64 * i + 8 * d) 2048
      (by unfold Verify.headerBank Verify.HDATA; omega)
      (by unfold Verify.headerBank Verify.HDATA; omega)]
    apply congrArg (BitVec.ofNat 64)
    unfold Verify.headerBank Verify.HDATA
    omega
  have fr : s.getMem (BitVec.ofNat 64 (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) =
      s0.getMem (BitVec.ofNat 64 (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d)) := by
    apply hF (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) (by omega)
    unfold Wr
    intro h
    rcases h with h | h <;> omega
  refine ⟨?_, ?_⟩
  · show accessValid ((hKey i d).eval s) 8 = true
    rw [key]
    exact valid_ofNat _ 8 hA.2 (by unfold Verify.HDATA; omega)
  · have he : (addC (.reg .x28) (hOff i d)).eval s =
        BitVec.ofNat 64 (Verify.HDATA + 4096 * 0 + 64 * i + 8 * d) := by
      simpa only [hKey, Addr.eval, addC_eval, E.eval] using key
    change s.getMem ((addC (.reg .x28) (hOff i d)).eval s) = _
    rw [he, fr, h0.2.header 0 i d (by norm_num) (by omega) hd]
    all_goals (congr 1 <;> unfold w0 <;> omega)

theorem copy_mem (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) (A : Nat) (hA : A < 2 ^ 64) :
    memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) := by
  have hs := slot_props i hi
  unfold copyMem
  rw [memEval_two s _ _ _ _ (slot i + 8) (slot i) A rfl rfl (by omega) (by omega) hA,
    c.lAt_eval hc h19 i hi 56 (by omega), c.lAt_eval hc h19 i hi 48 (by omega)]

theorem copy_obl (c : NCtx) (hc : c.ok) {s : MachineState} (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3) (i : Nat)
    (hi : i < 54) : ∀ o ∈ copyObl .x19 (off i), o.holds s := by
  have hb := c.blk_props hc i hi
  simp only [copyObl, List.mem_cons, List.not_mem_nil, or_false]
  rintro o (rfl | rfl)
  · show accessValid ((kAt .x19 (off i) 56).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 56 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)
  · show accessValid ((kAt .x19 (off i) 48).eval s) 8 = true
    rw [c.kAt_eval hc h19 i hi 48 (by omega)]; exact valid_ofNat _ _ (by omega) (by omega)

theorem copy_post (c : NCtx) (hc : c.ok) {s0 s t : MachineState} (h0 : c.Orig0 s0) (i : Nat)
    (hi : i < 54) (acc : List Digest) (hlen : acc.length = i) (hF : Frame s0 s (c.Wr i))
    (hS : ∀ j < acc.length, DigAt s (slot j) (acc.getD j 0))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3)
    (htm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) = memEval s (copyMem .x19 (off i) (slot i)) (BitVec.ofNat 64 A)) :
    Frame s0 t (c.Wr (i + 1)) ∧ ∀ j < (acc ++ [c.val i]).length,
      DigAt t (slot j) ((acc ++ [c.val i]).getD j 0) := by
  have hb := c.blk_props hc i hi
  have hs := slot_props i hi
  have tm : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = slot i + 8 then s.getMem (BitVec.ofNat 64 (c.blk i + 56))
      else if A = slot i then s.getMem (BitVec.ofNat 64 (c.blk i + 48)) else s.getMem (BitVec.ofNat 64 A) :=
    fun A hA => (htm A hA).trans (c.copy_mem hc h19 i hi A hA)
  have hfr : Frame s t (fun A => A = slot i + 8 ∨ A = slot i) := by
    intro A hA hn
    rw [tm A hA, if_neg (fun h => hn (Or.inl h)), if_neg (fun h => hn (Or.inr h))]
  refine ⟨(hF.trans hfr).mono ?_, fun j hj => ?_⟩
  · intro A _ h
    have := c.blk_le hc i hi
    have hlo := hc.2.2.2.1
    rcases h with h | h
    · unfold Wr at h ⊢; unfold blk at h this ⊢; omega
    · left; omega
  · rw [List.length_append, List.length_singleton] at hj
    by_cases hjl : j < acc.length
    · have hsj := slot_props j (by omega)
      have hmono : slot j + 16 ≤ slot i := by unfold slot; split_ifs <;> omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      exact (hS j hjl).frame hfr (by omega) (by omega) (by omega)
    · have hj2 : j = acc.length := by omega
      subst hj2
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self, hlen]
      have hv := val_at hc h0 hi hF
      refine ⟨?_, ?_⟩
      · rw [tm _ (by omega), if_neg (by omega), if_pos rfl]; exact hv.1
      · rw [tm _ (by omega), if_pos rfl]; exact hv.2

/-- **The max-digit copy of a table-slot chain** (`A = 3q`; T3Z: no `s9` update), then `j` past the shared
block's `A` rungs (5 steps). -/
theorem copyN_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54)
    (hp0 : c.startPc i < 210432)
    (hrun : vrun (c.startPc i) 7 = some (copyN .x19 (off i) (slot i) (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyN .x19 (off i) (slot i) (c.endPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyN] using c.copy_obl hc h19 i hi)
  have hkeep := copyN_keeps .x19 (off i) (slot i) (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`; T3Z: no bump, 4 instructions). -/
theorem copyFH_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hp0 : c.startPc i < 210432)
    (hend : c.startPc i + 4 = c.endPc i)
    (hrun : vrun (c.startPc i) 4 = some (copyFH .x19 (off i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 4 4 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyFH .x19 (off i) (slot i) (c.startPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyFH] using c.copy_obl hc h19 i hi)
  have hkeep := copyFH_keeps .x19 (off i) (slot i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_⟩⟩
  rw [Result.toState_pc]; simp only [hr, copyFH, E.eval]; rw [hend]


end NCtx
end SigGolfCandidate.T3M.Nonbinary
