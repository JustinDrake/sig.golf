import SigGolfCandidate.Expand.Copy

/-!
# `expand`: the copy phase (instructions 139 .. 182)

`rho` (4 words), the pi bytes (`pi_loop`: byte `s` = low byte of `KEYS[s]`), the secrets (60 words),
then the five layer bodies in one copy (976 words: signature bytes `2144 ..` to witness bytes
`2424 ..`; the counters are no longer in the signature); then `j pors_init` (instruction 495). The
witness buffer's byte view afterwards is `applyCopies copyRest (piF A 15 (applyCopy rho f0))` of
the byte view `f0` before the phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem


/-- The pi bytes on top of `g`. -/
def piF (A : Nat → Nat) (j : Nat) (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0x810 ≤ a ∧ a < 0x810 + j then byte (A (a - 0x810)) else g a

/-- The copies after the pi loop: the secrets, then the five layer bodies (one block). -/
def copyRest : List (Nat × Nat × Nat) := [(0x3310, 0x820, 60), (0x3B60, 0x1178, 976)]

theorem pi_loop (A : Nat → Nat) (g : Nat → Byte) :
    ∀ k (v : MachineState), k ≤ 15 → (v.pc = if k = 0 then pcOf 160 else pcOf 153) →
      v.getReg .x8 = BitVec.ofNat 64 (15 - k) → v.getReg .x25 = BitVec.ofNat 64 0x810 →
      BytesEq v (piF A (15 - k) g) → ArrOk v A →
      Run v (7 * k) (fun w => w.pc = pcOf 160 ∧ BytesEq w (piF A 15 g) ∧ ArrOk w A) := by
  intro k
  induction k with
  | zero => intro v _ hpc _ _ hb ha; exact Run.done' ⟨by simpa using hpc, by simpa using hb, ha⟩
  | succ k ih =>
    intro v hk hpc h8 h25 hb ha
    rw [if_neg (Nat.succ_ne_zero k)] at hpc
    have hj : 15 - (k + 1) < 15 := by omega
    have := pi_body v hpc (15 - (k + 1)) (A (15 - (k + 1))) hj h8 h25 (ha _ hj)
    refine (Run.bind this (fun w ⟨w8, w25, wpc, wb, wm⟩ => ih w (by omega) ?_ ?_ w25 ?_ ?_)).mono
      (by ring_nf; omega) (fun _ h => h)
    · rw [wpc]; by_cases h0 : k = 0
      · rw [if_pos (by omega), if_pos h0]
      · rw [if_neg (by omega), if_neg h0]
    · rw [w8]; exact ofNat_congr (by omega)
    · intro a ha'
      rw [wb a ha', hb a ha']
      unfold piF
      by_cases h1 : a = 0x810 + (15 - (k + 1))
      · rw [if_pos h1, if_pos (by omega), show a - 0x810 = 15 - (k + 1) by omega]; rfl
      · rw [if_neg h1]
        by_cases h2 : 0x810 ≤ a ∧ a < 0x810 + (15 - (k + 1))
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · intro p hp
      rw [wm _ (by rw [Ne, ofNat_eq_iff]; omega)]; exact ha p hp




/-- The copy phase (instructions 139 .. 182): witness bytes, then the jump to `pors_init`. -/
theorem copy_run (A : Nat → Nat) (u : MachineState) (hpc : u.pc = pcOf 139) (hA : ArrOk u A) :
    Run u 6364 (fun v => v.pc = pcOf 495 ∧
      BytesEq v (applyCopies copyRest (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun a => u.getByte (BitVec.ofNat 64 a)))))) := by
  have hf0 : BytesEq u (fun a => u.getByte (BitVec.ofNat 64 a)) := fun a _ => rfl
  have s1 := stageRun (e := 150) blk139 codeAt_139 rfl rfl rfl rfl rfl rfl codeAt_144 (by decide) (by decide) u hpc _ hf0
  refine Run.seq (B₂ := 6335) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk139.res.cycles = 5 by kernel_rfl]; norm_num)
  -- the keys are untouched by the rho copy
  have hAv : ArrOk v A := by
    intro p hp
    rw [getMem_eq_of_bytes u v (0x6E0 + 8 * p) (by omega) (by omega) (fun k hk => by
      rw [vb _ (by omega)]; unfold applyCopy; dsimp only; rw [if_neg (by omega)]), hA p hp]
  set g := applyCopy (0x3300, 0x800, 4) (fun a => u.getByte (BitVec.ofNat 64 a)) with hg
  refine Run.seq (B₂ := 6332) (Run.steps (symRun_sound blk150 codeAt_150 v vpc (by simp only [blk150.res, rv_simp]))
    (Run.done (P := fun x => x = blk150.res.toState v) rfl)) (fun v1 hv1 => ?_)
    (by simp only [show blk150.res.cycles = 3 by kernel_rfl]; norm_num)
  subst hv1
  have p1 : (blk150.res.toState v).pc = pcOf 153 := by simp only [blk150.res, rv_simp]
  have m1 : ∀ a, (blk150.res.toState v).getMem a = v.getMem a := toState_getMem_nil rfl v
  have hb1 : BytesEq (blk150.res.toState v) (piF A (15 - 15) g) := by
    intro a ha; rw [getByte_ofNat _ _ ha, m1, ← getByte_ofNat _ _ ha, vb a ha]
    simp [piF]
  have pl := pi_loop A g 15 _ le_rfl (by rw [p1]; rfl) (by simp only [blk150.res, rv_simp])
    (by simp only [blk150.res, rv_simp]) hb1 (hAv.frame m1)
  refine Run.seq (B₂ := 6227) pl (fun w ⟨wpc, wb, _⟩ => ?_) (by norm_num)
  set F := piF A 15 g
  have st1 := stageRun (e := 171) blk160 codeAt_160 rfl rfl rfl rfl rfl rfl codeAt_165 (by decide) (by decide) w wpc F wb
  refine Run.seq (B₂ := 5862) st1 (fun w1 ⟨p1, b1⟩ => ?_) (by simp only [show blk160.res.cycles = 5 by kernel_rfl]; norm_num)
  have st2 := stageRun (e := 182) blk171 codeAt_171 rfl rfl rfl rfl rfl rfl codeAt_176 (by decide) (by decide) w1 p1 _ b1
  refine Run.seq (B₂ := 1) st2 (fun w2 ⟨p2, b2⟩ => ?_) (by simp only [show blk171.res.cycles = 5 by kernel_rfl]; norm_num)
  refine Run.of (symRun_sound blk182 codeAt_182 w2 p2 (by simp only [blk182.res, rv_simp]))
    (by simp only [show blk182.res.cycles = 1 by kernel_rfl]; norm_num) ⟨by simp only [blk182.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, b2 a ha]
  rfl


end SigGolfCandidate.Expand
