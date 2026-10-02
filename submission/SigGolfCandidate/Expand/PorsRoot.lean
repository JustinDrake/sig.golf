import SigGolfCandidate.Expand.PorsLeaf

/-!
# `expand`, phase 2: `pors_init` and the whole PORS root (instructions 495 .. 638)

`porsRoot_sim` : from `pors_init` (495) with the digest's low dword at `0x160`, the sorted keys
at `0x6E0` and the witness in its buffer, the machine refines `Ref.porsRoot idx v w` and stops at
`pors_ok` (639) with the root at `OUT`, or HALT(1).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.ExP
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Sign

/-- `(a << k) >> k` keeps the low `64 - k` bits. -/
theorem shl_shr (a k : Nat) (ha : a < 2 ^ 64) (hk : k ≤ 64) :
    (BitVec.ofNat 64 a <<< k) >>> k = BitVec.ofNat 64 (a % 2 ^ (64 - k)) := by
  apply BitVec.eq_of_toNat_eq
  have h : (2 : Nat) ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hlt : a % 2 ^ (64 - k) < 2 ^ 64 :=
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by norm_num) (by omega))
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hlt]
  rw [h, Nat.mul_mod_mul_right, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-- 495 .. 528 (`pors_init`): the constant registers and `LB` / `PB` words, the leaf loop's
initial state. -/
theorem blk495_run (w : List Byte) (K : Nat → Nat) (t : MachineState) (hpc : t.pc = pcOf 495) (N0 : Nat)
    (hN0 : N0 < 2 ^ 64) (h160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 N0) (hw : WitMem w t)
    (hk : ∀ p < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (K p))
    (hkl : ∀ p < 15, K p < 2 ^ 22) (hTable:SmallBandTable t) :
    ∃ t', Steps eimg t 34 34 t' ∧ LeafInv w (N0 % 2 ^ 34) K 0 ⟨5504, 0, 0, 0, [], []⟩ t' ∧
      Frame t t' (fun a => a = 0x30000 ∨ a = 0x30010 ∨ a = 0x30018 ∨ a = 0x30030 ∨ a = 0x30038 ∨
        a = 0x30040 ∨ a = 0x30050 ∨ a = 0x30058) := by
  set idx := N0 % 2 ^ 34 with hidx
  have hidx' : idx < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
  have x4 : (Expand.blk495.res.toState t).getReg .x4 = BitVec.ofNat 64 idx := by
    simp only [Expand.blk495.res, rv_simp, h160, show (30#64 : Word).toNat % 64 = 30 from rfl]
    rw [shl_shr _ _ hN0 (by norm_num)]
  have hfr : Frame t (Expand.blk495.res.toState t) (fun a => a = 0x30000 ∨ a = 0x30010 ∨ a = 0x30018 ∨
      a = 0x30030 ∨ a = 0x30038 ∨ a = 0x30040 ∨ a = 0x30050 ∨ a = 0x30058) := by
    apply frame_toState; intro x hx hW
    simp only [Expand.blk495.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_add_ofNat, ofNat_eq_iff]
    bvomega
  have hA : ∀ a, (a = 0x30000 ∨ a = 0x30010 ∨ a = 0x30018 ∨ a = 0x30030 ∨ a = 0x30038 ∨ a = 0x30040 ∨
      a = 0x30050 ∨ a = 0x30058) → a < 0x6E0 ∨ 0x24B00 ≤ a := by intro a h; omega
  refine ⟨_, symRun_sound Expand.blk495 Expand.codeAt_495 t hpc (by simp only [Expand.blk495.res, rv_simp]),
    ⟨⟨hidx', x4, by simp only [Expand.blk495.res, rv_simp], by pnum [Expand.blk495.res],
      by simp only [Expand.blk495.res, rv_simp], ?_, by simp only [Expand.blk495.res, rv_simp], ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, hw.frame hfr (fun a h1 h2 => by unfold witA at h1; omega), ?_, hkl, hTable.frame hfr (by intro a ha hb;omega)⟩,
    by simp only [Expand.blk495.res, rv_simp]; rw [if_pos (by norm_num)], by norm_num, by simp only [Expand.blk495.res, rv_simp],
    by pnum [Expand.blk495.res], by simp only [Expand.blk495.res, rv_simp],
    by simp only [Expand.blk495.res, rv_simp], by simp only [Expand.blk495.res, rv_simp],
    by pnum [Expand.blk495.res, List.length_nil], fun j hj => by simp at hj, le_refl _, by simp, rfl, by simp, by simp,
    by norm_num, by norm_num, fun h => absurd h (by norm_num)⟩, hfr⟩
  · simp only [Expand.blk495.res, rv_simp]
    apply BitVec.eq_of_toNat_eq
    unfold Ref.tauH
    simp only [BitVec.toNat_ofNat, BitVec.toNat_zero]
    omega
  · pnum [Expand.blk495.res, h160, show (30#64 : Word).toNat % 64 = 30 from rfl,
      show (32#64 : Word).toNat % 64 = 32 from rfl, show (24#64 : Word).toNat % 64 = 24 from rfl,
      show (8#64 : Word).toNat % 64 = 8 from rfl]
    rw [shl_shr _ _ hN0 (by norm_num)]
    try rw [shl32_ofNat]
    bvsimp []
    exact ofNat_congr (by omega)
  · pnum [Expand.blk495.res]
  · pnum [Expand.blk495.res]
  · pnum [Expand.blk495.res]
  · pnum [Expand.blk495.res]
  · pnum [Expand.blk495.res, h160, show (30#64 : Word).toNat % 64 = 30 from rfl,
      show (32#64 : Word).toNat % 64 = 32 from rfl, show (24#64 : Word).toNat % 64 = 24 from rfl,
      show (8#64 : Word).toNat % 64 = 8 from rfl]
    rw [shl_shr _ _ hN0 (by norm_num)]
    try rw [shl32_ofNat]
    bvsimp []
    exact ofNat_congr (by omega)
  · pnum [Expand.blk495.res]
  · pnum [Expand.blk495.res]
  · intro p hp
    rw [hfr.getMem (by omega) (by omega), hk p hp]

/-- The PORS root at `pors_ok` (639), in `OUT`. -/
def RootOut (w : List Byte) (idx : Nat) (K : Nat → Nat) (M : Val) (t : MachineState) : Prop :=
  t.pc = pcOf 639 ∧ PCtx w idx K t ∧ M.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x30080) 2 = wordsOf M

/-- **The PORS root** (`Ref.porsRoot`), from `pors_init` to `pors_ok` or HALT(1). -/
theorem porsRoot_sim (w : List Byte) (K : Nat → Nat) (v : List Nat) (t : MachineState) (hpc : t.pc = pcOf 495)
    (N0 : Nat) (hN0 : N0 < 2 ^ 64) (h160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 N0)
    (hw : WitMem w t) (hk : ∀ p < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (K p))
    (hkl : ∀ p < 15, K p < 2 ^ 22) (hTable:SmallBandTable t) (hwl : 4096 ≤ w.length)
    (hx : ∀ s < 15, (v ++ [porsT]).getD (witPi w s / 8 % 16) 0 = K s / 256) :
    Sim eimg t 400000 (porsRoot (N0 % 2 ^ 34) v w) (OPost (RootOut w (N0 % 2 ^ 34) K)) := by
  obtain ⟨t1, hs1, hinv, hfr⟩ := blk495_run w K t hpc N0 hN0 h160 hw hk hkl hTable
  have hl := porsLeaves_sim w (N0 % 2 ^ 34) K v hwl hx 15 0 ⟨5504, 0, 0, 0, [], []⟩ t1 (by norm_num) hinv
  unfold porsRoot
  rw [show List.range porsK = List.range' 0 15 from List.range_eq_range', show wStream = 5504 from rfl]
  refine (Sim.steps hs1 (Sim.bind hl (W₂ := 10) (fun r t2 h2 => ?_))).mono (by norm_num) (fun _ _ h => h)
  rcases r with _ | st
  · dsimp only
    exact (Sim.pure (a := none) (Q := OPost (RootOut w (N0 % 2 ^ 34) K)) h2).mono (by omega) (fun _ _ h => h)
  dsimp only
  have hc := h2.ctx
  have tpc : t2.pc = pcOf 633 := by rw [h2.pc, if_neg (by norm_num)]
  have hf := h2.hf
  have hk14 := h2.hk14
  obtain ⟨t3, hs3, p3, r3, m3⟩ := blk633_run t2 tpc st.folds (by omega) h2.x20
  by_cases c1 : st.folds > porsM
  · rw [if_pos (Or.inl c1)]
    rw [if_pos (by unfold porsM at c1; omega)] at p3
    exact (fail_sim_steps hs3 p3).mono (by omega) (fun _ _ h => h)
  rw [if_neg (by unfold porsM at c1; omega)] at p3
  obtain ⟨t4, hs4, p4, r4, m4⟩ := blk635_run t3 p3 st.E h2.hE (by rw [r3.get .x19, h2.x19])
  by_cases c2 : st.E ≠ 1
  · rw [if_pos (Or.inr (Or.inl c2))]
    rw [if_pos c2] at p4
    exact (Sim.steps hs3 (fail_sim_steps hs4 p4)).mono (by omega) (fun _ _ h => h)
  rw [if_neg c2] at p4
  obtain ⟨t5, hs5, p5, r5, m5⟩ := blk637_run t4 p4 st.stack.length (by omega)
    (by rw [r4.get .x21, r3.get .x21, h2.x21]) (by rw [r4.get .x22, r3.get .x22, hc.x22])
  by_cases c3 : st.stack ≠ []
  · rw [if_pos (Or.inr (Or.inr c3))]
    rw [if_pos (by simpa using c3)] at p5
    exact (Sim.steps hs3 (Sim.steps hs4 (fail_sim_steps hs5 p5))).mono (by omega) (fun _ _ h => h)
  rw [if_neg (by tauto)]
  rw [if_neg (by simpa using c3)] at p5
  obtain ⟨t6, hs6, p6, r6, m6⟩ := blk638_run t5 p5
  have g6 : ∀ x, t6.getMem x = t2.getMem x := fun x => by rw [m6, m5, m4, m3]
  obtain ⟨hn, hout⟩ := h2.out (by norm_num)
  refine (Sim.pure_steps (hs3.trans (hs4.trans (hs5.trans hs6))) ⟨p6, ?_, hn, ?_⟩).mono (by omega)
    (fun _ _ h => h)
  · exact hc.frame (W := fun _ => False) (fun x _ _ => g6 _) (((r3.trans r4).trans r5).trans r6)
      (fun _ _ h => h)
  · rw [readWords_ofNat_two, g6, g6, ← readWords_ofNat_two, hout]

end SigGolfCandidate.ExP
