import SigGolfCandidate.Expand.Copy

/-!
# `expand`: the copy phase through the aligned bodies (instructions 139 .. 225)

`rho` (4 words), the pi bytes (`pi_loop`: byte `s` = low byte of `KEYS[s]`), the secrets (60 words),
then five aligned bodies. The subsequent tail decoder checks canonicality and reconstructs
five LE32 counters in the witness. The body-only run ends at PC 226.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem


/-- Live secret and aligned body copies; the old interleaved `copyRest` below is retained only
until the witness proof is migrated. -/
def copyBodies : List (Nat × Nat × Nat) :=
  [(0x3310, 0x820, 60), (0x3B60, 0x1178, 212), (0x3EB0, 0x14C8, 192), (0x41B0, 0x17C8, 192),
    (0x44B0, 0x1AC8, 192), (0x47B0, 0x1DC8, 188)]

theorem copyBodies_layout :
    copyBodies = (0x3310, 0x820, 60) :: CounterUnpackLayout.bodyCopies := by decide

/-- The pi bytes on top of `g`. -/
def piF (A : Nat → Nat) (j : Nat) (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0x810 ≤ a ∧ a < 0x810 + j then byte (A (a - 0x810)) else g a

/-- Neither the secret/body copies nor the pi/rho setup writes into the
signature source buffer. This carries the input tail bytes to PC 226. -/
theorem copyBodies_signature (A : Nat → Nat) (u : MachineState) (a : Nat)
    (ha : 0x3300 ≤ a) :
    applyCopies copyBodies
      (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun x => u.getByte (BitVec.ofNat 64 x)))) a =
      u.getByte (BitVec.ofNat 64 a) := by
  have hmiss : ∀ c ∈ copyBodies,
      ¬ (c.2.1 ≤ a ∧ a < c.2.1 + 4 * c.2.2) := by
    intro c hc
    simp only [copyBodies, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
  rw [applyCopies_frame copyBodies _ a hmiss]
  unfold piF
  rw [if_neg (by omega)]
  unfold applyCopy
  dsimp only [Prod.fst, Prod.snd]
  rw [if_neg (by omega)]

/-- Byte preservation at a concrete copied state, ready for `SigOK`. -/
theorem copied_signature_byte (A : Nat → Nat) (u v : MachineState)
    (hbytes : BytesEq v
      (applyCopies copyBodies (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun x => u.getByte (BitVec.ofNat 64 x))))))
    (a : Nat) (ha : 0x3300 ≤ a) (hlim : a < 2 ^ 64) :
    v.getByte (BitVec.ofNat 64 a) = u.getByte (BitVec.ofNat 64 a) := by
  rw [hbytes a hlim, copyBodies_signature A u a ha]

/-- The live copy phase preserves all 6,062 signature bytes for the decoder. -/
theorem copied_sigOK (A : Nat → Nat) (u v : MachineState) (sig : List Byte)
    (hu : SigOK u sig)
    (hbytes : BytesEq v
      (applyCopies copyBodies (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun x => u.getByte (BitVec.ofNat 64 x)))))) :
    SigOK v sig := by
  intro j hj
  rw [copied_signature_byte A u v hbytes (0x3300 + j) (by omega) (by omega)]
  exact hu j hj

/-- The copies after the pi loop: secrets, then per layer the counter word and the body. -/
def copyRest : List (Nat × Nat × Nat) :=
  [(0x3310, 0x820, 60), (0x3B60, 0x20B8, 1), (0x3B64, 0x1178, 212), (0x3EB4, 0x20BC, 1),
    (0x3EB8, 0x14C8, 192), (0x41B8, 0x20C0, 1), (0x41BC, 0x17C8, 192), (0x44BC, 0x20C4, 1),
    (0x44C0, 0x1AC8, 192), (0x47C0, 0x20C8, 1), (0x47C4, 0x1DC8, 188)]

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




/-- The live copy phase through the five aligned bodies, ending at the packed tail. -/
theorem copy_bodies_run (A : Nat → Nat) (u : MachineState)
    (hpc : u.pc = pcOf 139) (hA : ArrOk u A) :
    Run u 6383 (fun v => v.pc = pcOf 226 ∧
      v.getReg .x6 = BitVec.ofNat 64 0x4aa0 ∧
      v.getReg .x7 = BitVec.ofNat 64 0x20b8 ∧
      BytesEq v (applyCopies copyBodies (piF A 15 (applyCopy (0x3300, 0x800, 4)
        (fun a => u.getByte (BitVec.ofNat 64 a)))))) := by
  have hf0 : BytesEq u (fun a => u.getByte (BitVec.ofNat 64 a)) := fun a _ => rfl
  have s1 := stageRun (e := 150) blk139 codeAt_139 rfl rfl rfl rfl rfl rfl codeAt_144
    (by decide) (by decide) u hpc _ hf0
  refine Run.seq (B₂ := 6354) s1 (fun v ⟨vpc, vb⟩ => ?_)
    (by simp only [show blk139.res.cycles = 5 by kernel_rfl]; norm_num)
  have hAv : ArrOk v A := by
    intro p hp
    rw [getMem_eq_of_bytes u v (0x6E0 + 8 * p) (by omega) (by omega) (fun k hk => by
      rw [vb _ (by omega)]; unfold applyCopy; dsimp only; rw [if_neg (by omega)]), hA p hp]
  set g := applyCopy (0x3300, 0x800, 4) (fun a => u.getByte (BitVec.ofNat 64 a)) with hg
  refine Run.seq (B₂ := 6351)
    (Run.steps (symRun_sound blk150 codeAt_150 v vpc (by simp only [blk150.res, rv_simp]))
      (Run.done (P := fun x => x = blk150.res.toState v) rfl)) (fun v1 hv1 => ?_)
      (by simp only [show blk150.res.cycles = 3 by kernel_rfl]; norm_num)
  subst hv1
  have p1 : (blk150.res.toState v).pc = pcOf 153 := by simp only [blk150.res, rv_simp]
  have m1 : ∀ a, (blk150.res.toState v).getMem a = v.getMem a := toState_getMem_nil rfl v
  have hb1 : BytesEq (blk150.res.toState v) (piF A (15 - 15) g) := by
    intro a ha; rw [getByte_ofNat _ _ ha, m1, ← getByte_ofNat _ _ ha, vb a ha]
    simp [piF]
  have pl := pi_loop A g 15 _ le_rfl (by rw [p1]; rfl)
    (by simp only [blk150.res, rv_simp]) (by simp only [blk150.res, rv_simp])
    hb1 (hAv.frame m1)
  refine Run.seq (B₂ := 6246) pl (fun w ⟨wpc, wb, _⟩ => ?_) (by norm_num)
  set F := piF A 15 g
  have st1 := stageRun (e := 171) blk160 codeAt_160 rfl rfl rfl rfl rfl rfl codeAt_165
    (by decide) (by decide) w wpc F wb
  refine Run.seq (B₂ := 5881) st1 (fun w1 ⟨p1, b1⟩ => ?_)
    (by simp only [show blk160.res.cycles = 5 by kernel_rfl]; norm_num)
  have st2 := stageRun (e := 182) blk171 codeAt_171 rfl rfl rfl rfl rfl rfl codeAt_176
    (by decide) (by decide) w1 p1 _ b1
  refine Run.seq (B₂ := 4604) st2 (fun w2 ⟨p2, b2⟩ => ?_)
    (by simp only [show blk171.res.cycles = 5 by kernel_rfl]; norm_num)
  have st3 := stageRun (e := 193) blk182 codeAt_182 rfl rfl rfl rfl rfl rfl codeAt_187
    (by decide) (by decide) w2 p2 _ b2
  refine Run.seq (B₂ := 3447) st3 (fun w3 ⟨p3, b3⟩ => ?_)
    (by simp only [show blk182.res.cycles = 5 by kernel_rfl]; norm_num)
  have st4 := stageRun (e := 204) blk193 codeAt_193 rfl rfl rfl rfl rfl rfl codeAt_198
    (by decide) (by decide) w3 p3 _ b3
  refine Run.seq (B₂ := 2290) st4 (fun w4 ⟨p4, b4⟩ => ?_)
    (by simp only [show blk193.res.cycles = 5 by kernel_rfl]; norm_num)
  have st5 := stageRun (e := 215) blk204 codeAt_204 rfl rfl rfl rfl rfl rfl codeAt_209
    (by decide) (by decide) w4 p4 _ b4
  refine Run.seq (B₂ := 1133) st5 (fun w5 ⟨p5, b5⟩ => ?_)
    (by simp only [show blk204.res.cycles = 5 by kernel_rfl]; norm_num)
  have st6 := stageRun_pointers (e := 226) blk215 codeAt_215 rfl rfl rfl rfl rfl rfl codeAt_220
    (by decide) (by decide) w5 p5 _ b5
  refine Run.seq (B₂ := 0) st6 (fun w6 ⟨p6, x6, x7, b6⟩ => ?_)
    (by simp only [show blk215.res.cycles = 5 by kernel_rfl]; norm_num)
  exact Run.done' ⟨p6,
    by simpa only [show 0x47b0 + 4 * 188 = 0x4aa0 by decide] using x6,
    by simpa only [show 0x1dc8 + 4 * 188 = 0x20b8 by decide] using x7,
    by simpa [copyBodies, applyCopies] using b6⟩

end SigGolfCandidate.Expand
