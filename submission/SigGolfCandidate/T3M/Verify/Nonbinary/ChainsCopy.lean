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

/-- `s9` of a head or copy in a table slot: `mv s9, s11` (chain 0) or the bump. -/
theorem s9v (c : NCtx) {s0 s : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (hR : ∀ x ∉ chainRegs, s.getReg x = s0.getReg x) (i : Nat) (hi : i < 54) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (h25 : i ≠ 0 → s.getReg .x25 = BitVec.ofNat 64 (w0 (i - 1))) :
    (s9E first).eval s = BitVec.ofNat 64 (w0 i) := by
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  cases first
  · simp only [s9E, bumpE, Bool.false_eq_true, if_false, E.eval, BinOp.eval]
    have hne := hfirst' rfl
    rw [h25 hne, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  · obtain rfl := hfirst rfl
    simp only [s9E, if_true, E.eval]
    rw [kr .x27 (BitVec.ofNat 64 0x101) (by simp [known]) (by decide)]
    rfl

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

/-- **The max-digit copy of a table-slot chain** (`A = 4q`, chain 48). -/
theorem copyJ_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (first : Bool)
    (hfirst : first = true → i = 0) (hfirst' : first = false → i ≠ 0)
    (hp0 : c.startPc i < 210432)
    (hrun : vrun (c.startPc i) 7 = some (copyJ .x19 (off i) (slot i) first (c.endPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 6 6 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyJ .x19 (off i) (slot i) first (c.endPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyJ] using c.copy_obl hc h19 i hi)
  have hkeep := copyJ_keeps .x19 (off i) (slot i) first (c.endPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  have s9 := c.s9v hk hR i hi first hfirst hfirst' h25
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_, ?_⟩⟩
  · rw [Result.toState_getReg]; simp only [hr, copyJ]
    rw [RegFile.get_set_self _ _ (by decide), s9]
  · rw [Result.toState_pc]; rfl

/-- **The max-digit copy of an inline chain** (`B`, `C`, `D`). -/
theorem copyF_step (c : NCtx) (hc : c.ok) {s0 : MachineState} (hk : ∀ p ∈ c.known, s0.getReg p.1 = p.2)
    (h0 : c.Orig0 s0) (i : Nat) (hi : i < 54) (hi0 : i ≠ 0) (hp0 : c.startPc i < 210432)
    (hend : c.startPc i + 5 = c.endPc i)
    (hrun : vrun (c.startPc i) 5 = some (copyF .x19 (off i) (slot i) (c.startPc i)))
    (acc : List Digest) (s : MachineState) (hs : c.ChainIn s0 i acc s) :
    ∃ t, Steps vimage s 5 5 t ∧ c.EndInv s0 i (acc ++ [c.val i]) t := by
  obtain ⟨⟨hR, hF, hS⟩, hlen, h25, hpc⟩ := hs
  have kr : ∀ r v, (r, v) ∈ c.known → r ∉ chainRegs → s.getReg r = v := fun r v hm hn =>
    (hR r hn).trans (hk _ hm)
  have h19 : s.getReg .x19 = BitVec.ofNat 64 c.S3 := kr _ _ (by simp [known]) (by decide)
  set r := copyF .x19 (off i) (slot i) (c.startPc i) with hr
  have hst := piece_steps45 hrun hp0 s hpc (by simpa [hr, copyF] using c.copy_obl hc h19 i hi)
  have hkeep := copyF_keeps .x19 (off i) (slot i) (c.startPc i)
  obtain ⟨hF', hS'⟩ := c.copy_post (t := r.toState s) hc h0 i hi acc hlen hF hS h19
    (fun A _ => by rw [Result.toState_getMem]; rfl)
  refine ⟨r.toState s, hst, ⟨⟨fun x hx => (hkeep.reg s (LCtx.not_mem_sub hx (by decide))).trans (hR x hx), hF', hS'⟩,
    by simp [hlen], ?_, ?_⟩⟩
  · rw [Result.toState_getReg]; simp only [hr, copyF]
    rw [RegFile.get_set_self _ _ (by decide)]
    simp only [bumpE, E.eval, BinOp.eval]
    rw [h25 hi0, kr .x28 (BitVec.ofNat 64 (2 ^ 40)) (by simp [known]) (by decide), ofNat_add_ofNat]
    congr 1; unfold w0; omega
  · rw [Result.toState_pc]; simp only [hr, copyF, E.eval]; rw [hend]


end NCtx
end SigGolfCandidate.T3M.Nonbinary
