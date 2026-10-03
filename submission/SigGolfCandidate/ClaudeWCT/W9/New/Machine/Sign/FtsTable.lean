import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsTableCheck

namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem pk_digit (r : Fin 728) (i : Fin 7) : pk.getD r.val 0 / 4 ^ i.val % 4 = WCT9.digit r i := by
  have hl : (WCT9.compositions 4 7 6).length = 728 := WCT9.codebook_card
  have hr1 : r.val < (WCT9.compositions 4 7 6).length := by rw [hl]; exact r.isLt
  have hr2 : r.val < pk.length := by rw [pk_length]; exact r.isLt
  have hz : r.val < ((WCT9.compositions 4 7 6).zip pk).length := by simp [hl, pk_length]
  have h := List.all_eq_true.mp pk_digits_all _ (List.getElem_mem hz)
  simp only [List.getElem_zip] at h
  have h2 := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  simp only [beq_iff_eq] at h2
  rw [List.getD_eq_getElem _ _ hr2, h2]
  unfold WCT9.digit WCT9.codeword
  rfl
theorem rowsOK_get : ∀ (rows : List (List (BitVec 8))) (k0 : Nat), rowsOK k0 rows = true →
    ∀ k (hk : k < rows.length), rowOK (k0 + k) rows[k] = true
  | [], _, _, k, hk => absurd hk (by simp)
  | r :: rs, k0, h, k, hk => by
    simp only [rowsOK, Bool.and_eq_true] at h
    rcases k with _ | k
    · simpa using h.1
    · have := rowsOK_get rs (k0 + 1) h.2 k (by simpa using hk)
      simpa [show k0 + (k + 1) = k0 + 1 + k by omega] using this
theorem flatten_drop_take : ∀ (rows : List (List (BitVec 8))), (∀ r ∈ rows, r.length = 8) →
    ∀ k (hk : k < rows.length), (rows.flatten.drop (8 * k)).take 8 = rows[k]
  | [], _, k, hk => absurd hk (by simp)
  | r :: rs, h, k, hk => by
    have hr : r.length = 8 := h r (by simp)
    rcases k with _ | k
    · simp only [List.flatten_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    · simp only [List.flatten_cons, List.getElem_cons_succ]
      rw [show 8 * (k + 1) = r.length + 8 * k by omega, List.drop_length_add_append]
      exact flatten_drop_take rs (fun r' hr' => h r' (by simp [hr'])) k (by simpa using hk)
theorem table_dw {t : MachineState} (h : TableAt t) {k : Nat} (hk : k < 8192) :
    t.getMem (BitVec.ofNat 64 (TBL + 8 * k)) = bytesToWordLE (tblRows[k]'(by rw [tblRows_length]; exact hk)) := by
  rw [h k hk]
  congr 1
  exact flatten_drop_take tblRows (fun r hr => by simpa using List.all_eq_true.mp tblRows_len8 r hr) k _
theorem table_word {t : MachineState} (h : TableAt t) {f : Nat} (hf : f < 16384) :
    t.getWord32 (BitVec.ofNat 64 (TBL + 4 * f)) = BitVec.ofNat 32 (pkAt f) := by
  have hk : f / 2 < 8192 := by omega
  have hlt : TBL + 4 * f < 2 ^ 64 := by unfold TBL; omega
  unfold MachineState.getWord32
  have ha : alignToDword (BitVec.ofNat 64 (TBL + 4 * f)) = BitVec.ofNat 64 (TBL + 8 * (f / 2)) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, toNat_ofNat_lt hlt, toNat_ofNat_lt (by unfold TBL; omega)]
    unfold TBL; omega
  have hb : byteOffset (BitVec.ofNat 64 (TBL + 4 * f)) / 4 = f % 2 := by
    rw [byteOffset_eq, toNat_ofNat_lt hlt]; unfold TBL; omega
  rw [ha, hb, table_dw h hk]
  have hr := rowsOK_get tblRows 0 tbl_rows_ok (f / 2) (by rw [tblRows_length]; exact hk)
  simp only [rowOK, Bool.and_eq_true, beq_iff_eq, Nat.zero_add] at hr
  rcases Nat.mod_two_eq_zero_or_one f with h0 | h1
  · rw [h0, hr.1.2, show 2 * (f / 2) = f by omega]
  · rw [h1, hr.2, show 2 * (f / 2) + 1 = f by omega]
theorem pkAt_lt (f : Nat) : pkAt f < 2 ^ 32 := by
  unfold pkAt
  split_ifs
  · exact pk_lt_all _ (Nat.mod_lt _ (by norm_num))
  · norm_num
theorem pkAt_digit (f : Nat) (hf : f < 16016) (i : Fin 7) :
    pkAt f / 4 ^ i.val % 4 = WCT9.digit ⟨f % 728, Nat.mod_lt _ (by norm_num)⟩ i := by
  unfold pkAt; rw [if_pos hf]; exact pk_digit ⟨f % 728, _⟩ i
theorem decode_lwu : decodeInstruction 0x000e6c83 = some (.base (.LWU .x25 .x28 0)) := by rfl
theorem step_lwu {im : Image} (hcode : NewCodeAt im) {c : Nat} (hc : c < 9) (s : MachineState)
    (hpc : s.pc = pcOf (lwuI c)) {f : Nat} (hf : f < 16384) (h28 : s.getReg .x28 = BitVec.ofNat 64 (TBL + 4 * f))
    (ht : TableAt s) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf (lwuI c + 1) ∧ t.getReg .x25 = BitVec.ofNat 64 (pkAt f) ∧
      RegsExcept s t [.x25] ∧ Frame s t (fun _ => False) := by
  have hl := coordLook_ok hcode hc
  have hlw := lwuI_lt c hc
  have hpc' : (s.pc.toNat < 0x1000 || s.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : coordLook c ((s.pc.toNat - 0x1000) / 4) = some 0x000e6c83 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * lwuI c - 0x1000) / 4 = lwuI c by omega]
    exact lwu_word c hc
  have hf' : fetch im s = some (.base (.LWU .x25 .x28 0)) :=
    (fetch_of_look hl hpc' hw s rfl).trans decode_lwu
  have hcl : classify (.base (.LWU .x25 .x28 0)) = some (.load .wu .x25 .x28 (signExtend12 0)) := rfl
  have hacc : accessValid (s.getReg .x28 + signExtend12 0) LoadKind.wu.width = true := by
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show TBL + 4 * f < 2 ^ 64 by unfold TBL; omega), MEMORY_BYTES]
    unfold TBL; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide)]
    have e : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (TBL + 4 * f) := by
      rw [h28]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
    simp only [LoadKind.read, e, table_word ht hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := pkAt_lt f
    omega
  · intro r hr
    have hne : Reg.x25 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
end ClaudeWCT.W9.Machine.Sign
