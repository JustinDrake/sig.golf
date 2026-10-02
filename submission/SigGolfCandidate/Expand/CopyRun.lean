import SigGolfCandidate.Expand.Copy

/-!
# `expand`: the copy phase (instructions 139 .. 173, then the scatter 860 .. 988)

`rho` (4 words, W1: into the tweak slot of chain block `(0, 1)`, `0x13C0`), the pi bytes (`pi_loop`:
byte `s` = low byte of `KEYS[s]`, at `0x1270 + s`), the secrets (W1: the 16-byte stride-64 loop, secret
`s` into the tweak slot of chain block `(0, 2 + s)`, `0x1400 + 64 s`), then `j scatter` (173): per
layer, the 42 chain values (16 bytes each, signature stride 16, witness stride 64: into the value slot
`block(lay, i) + 48` of the W1a chain array) and the path (word copy to `pathOff lay`); then
`j pors_init` (988 -> 495). The witness buffer's byte view afterwards is
`applyCopies copyRest (piF A 15 (applyCopy rho f0))` of the byte view `f0` before the phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem


/-- The pi bytes on top of `g`. -/
def piF (A : Nat → Nat) (j : Nat) (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0x1270 ≤ a ∧ a < 0x1270 + j then byte (A (a - 0x1270)) else g a

/-- Signature offsets of the layer bodies (`sigLayerOff`), witness path offsets (`pathOff`), path words. -/
def sgOff (lay : Nat) : Nat := [2128, 2976, 3744, 4512, 5280].getD lay 0
def pOff (lay : Nat) : Nat := [2704, 4032, 4416, 4800, 5184].getD lay 0
def pWords (lay : Nat) : Nat := [44, 24, 24, 24, 20].getD lay 0

/-- The scatter copies of layer `lay`: the 42 chain values into the value slots, then the path. -/
def chainCp (lay : Nat) : List (Nat × Nat × Nat) :=
  strideCopies (0x24B00 + sgOff lay) (0x800 + 2992 + 2688 * lay) 42
def pathCp (lay : Nat) : Nat × Nat × Nat := (0x24B00 + sgOff lay + 672, 0x800 + pOff lay, pWords lay)
def pathCps (lay : Nat) : List (Nat × Nat × Nat) :=
  if lay = 0 then [pathCp lay]
  else strideCopies (0x24B00 + sgOff lay + 672) (0x800 + pOff lay) (pWords lay / 4)
def layCp (lay : Nat) : List (Nat × Nat × Nat) := chainCp lay ++ pathCps lay

/-- The secret copies (W1): secret `s` into the tweak slot of chain block `(0, 2 + s)`. -/
def secCp : List (Nat × Nat × Nat) := strideCopies 0x24B10 0x1400 15

/-- The copies after the pi loop: the secrets, then the scatter of layers 0 .. 4. -/
def copyRest : List (Nat × Nat × Nat) :=
  secCp ++ (layCp 0 ++ layCp 1 ++ layCp 2 ++ layCp 3 ++ layCp 4)

theorem pi_loop (A : Nat → Nat) (g : Nat → Byte) :
    ∀ k (v : MachineState), k ≤ 15 → (v.pc = if k = 0 then pcOf 160 else pcOf 153) →
      v.getReg .x8 = BitVec.ofNat 64 (15 - k) → v.getReg .x25 = BitVec.ofNat 64 0x1270 →
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
      by_cases h1 : a = 0x1270 + (15 - (k + 1))
      · rw [if_pos h1, if_pos (by omega), show a - 0x1270 = 15 - (k + 1) by omega]; rfl
      · rw [if_neg h1]
        by_cases h2 : 0x1270 ≤ a ∧ a < 0x1270 + (15 - (k + 1))
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · intro p hp
      rw [wm _ (by rw [Ne, ofNat_eq_iff]; omega)]; exact ha p hp




/-- One layer of the scatter: the stride copy of the chain values, then the path word copy. -/
theorem scat_0 (u : MachineState) (hpc : u.pc = pcOf 860) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 610 (fun v => v.pc = pcOf 884 ∧ BytesEq v (applyCopies (layCp 0) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 0) (dst := 0x800 + 2992 + 2688 * 0) (n := 42) (e := 873)
    blkAuth860 codeAt_auth860 rfl rfl rfl rfl rfl rfl codeAt_auth865 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 269) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blkAuth860.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun (src := 0x24B00 + sgOff 0 + 672) (dst := 0x800 + pOff 0) (n := pWords 0) (e := 884)
    blkAuth873 codeAt_auth873 rfl rfl rfl rfl rfl rfl codeAt_auth878 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blkAuth873.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCps
  rw [if_pos rfl, applyCopies_append, applyCopies_single]
  unfold pathCp
  exact wb

theorem scat_1 (u : MachineState) (hpc : u.pc = pcOf 884) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 910 ∧ BytesEq v (applyCopies (layCp 1) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 1) (dst := 0x800 + 2992 + 2688 * 1) (n := 42) (e := 897)
    blkAuth884 codeAt_auth884 rfl rfl rfl rfl rfl rfl codeAt_auth889 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blkAuth884.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 1 + 672) (dst := 0x800 + pOff 1) (n := pWords 1 / 4) (e := 910)
    blkAuth897 codeAt_auth897 rfl rfl rfl rfl rfl rfl codeAt_auth902 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blkAuth897.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCps
  rw [if_neg (by decide : ¬ (1 : Nat) = 0), applyCopies_append]
  exact wb

theorem scat_2 (u : MachineState) (hpc : u.pc = pcOf 910) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 936 ∧ BytesEq v (applyCopies (layCp 2) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 2) (dst := 0x800 + 2992 + 2688 * 2) (n := 42) (e := 923)
    blkAuth910 codeAt_auth910 rfl rfl rfl rfl rfl rfl codeAt_auth915 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blkAuth910.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 2 + 672) (dst := 0x800 + pOff 2) (n := pWords 2 / 4) (e := 936)
    blkAuth923 codeAt_auth923 rfl rfl rfl rfl rfl rfl codeAt_auth928 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blkAuth923.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCps
  rw [if_neg (by decide : ¬ (2 : Nat) = 0), applyCopies_append]
  exact wb

theorem scat_3 (u : MachineState) (hpc : u.pc = pcOf 936) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 962 ∧ BytesEq v (applyCopies (layCp 3) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 3) (dst := 0x800 + 2992 + 2688 * 3) (n := 42) (e := 949)
    blkAuth936 codeAt_auth936 rfl rfl rfl rfl rfl rfl codeAt_auth941 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blkAuth936.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 3 + 672) (dst := 0x800 + pOff 3) (n := pWords 3 / 4) (e := 962)
    blkAuth949 codeAt_auth949 rfl rfl rfl rfl rfl rfl codeAt_auth954 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blkAuth949.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCps
  rw [if_neg (by decide : ¬ (3 : Nat) = 0), applyCopies_append]
  exact wb

theorem scat_4 (u : MachineState) (hpc : u.pc = pcOf 962) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 466 (fun v => v.pc = pcOf 988 ∧ BytesEq v (applyCopies (layCp 4) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 4) (dst := 0x800 + 2992 + 2688 * 4) (n := 42) (e := 975)
    blkAuth962 codeAt_auth962 rfl rfl rfl rfl rfl rfl codeAt_auth967 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 125) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blkAuth962.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 4 + 672) (dst := 0x800 + pOff 4) (n := pWords 4 / 4) (e := 988)
    blkAuth975 codeAt_auth975 rfl rfl rfl rfl rfl rfl codeAt_auth980 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blkAuth975.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCps
  rw [if_neg (by decide : ¬ (4 : Nat) = 0), applyCopies_append]
  exact wb

/-- The scatter (860 .. 988): the five layers, then `j pors_init`. -/
theorem scat_run (u : MachineState) (hpc : u.pc = pcOf 860) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 2547 (fun v => v.pc = pcOf 495 ∧
      BytesEq v (applyCopies (layCp 0 ++ layCp 1 ++ layCp 2 ++ layCp 3 ++ layCp 4) F)) := by
  refine Run.seq (B₂ := 1937) (scat_0 u hpc F hF) (fun u0 ⟨p0, b0⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 1447) (scat_1 u0 p0 _ b0) (fun u1 ⟨p1, b1⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 957) (scat_2 u1 p1 _ b1) (fun u2 ⟨p2, b2⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 467) (scat_3 u2 p2 _ b2) (fun u3 ⟨p3, b3⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 1) (scat_4 u3 p3 _ b3) (fun u4 ⟨p4, b4⟩ => ?_) (by norm_num)
  refine Run.of (symRun_sound blkAuth988 codeAt_auth988 u4 p4 (by simp only [blkAuth988.res, rv_simp]))
    (by simp only [show blkAuth988.res.cycles = 1 by kernel_rfl]; norm_num) ⟨by simp only [blkAuth988.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, b4 a ha]
  simp only [applyCopies_append]

/-- The copy phase (instructions 139 .. 173, the scatter): witness bytes, then the jump to `pors_init`. -/
theorem copy_run (A : Nat → Nat) (u : MachineState) (hpc : u.pc = pcOf 139) (hA : ArrOk u A) :
    Run u 3050 (fun v => v.pc = pcOf 495 ∧
      BytesEq v (applyCopies copyRest (piF A 15 (applyCopy (0x24B00, 0x13C0, 4)
        (fun a => u.getByte (BitVec.ofNat 64 a)))))) := by
  have hf0 : BytesEq u (fun a => u.getByte (BitVec.ofNat 64 a)) := fun a _ => rfl
  have s1 := stageRun (e := 150) blk139 codeAt_139 rfl rfl rfl rfl rfl rfl codeAt_144 (by decide) (by decide) u hpc _ hf0
  refine Run.seq (B₂ := 3021) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk139.res.cycles = 5 by kernel_rfl]; norm_num)
  -- the keys are untouched by the rho copy
  have hAv : ArrOk v A := by
    intro p hp
    rw [getMem_eq_of_bytes u v (0x6E0 + 8 * p) (by omega) (by omega) (fun k hk => by
      rw [vb _ (by omega)]; unfold applyCopy; dsimp only; rw [if_neg (by omega)]), hA p hp]
  set g := applyCopy (0x24B00, 0x13C0, 4) (fun a => u.getByte (BitVec.ofNat 64 a)) with hg
  refine Run.seq (B₂ := 3018) (Run.steps (symRun_sound blk150 codeAt_150 v vpc (by simp only [blk150.res, rv_simp]))
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
  refine Run.seq (B₂ := 2913) pl (fun w ⟨wpc, wb, _⟩ => ?_) (by norm_num)
  set F := piF A 15 g
  -- W1: the secrets, 16 bytes each, into the tweak slots of chain blocks `(0, 2 .. 16)`
  have st1 := stageRun16 (src := 0x24B10) (dst := 0x1400) (n := 15) (e := 173) blk160 codeAt_160 rfl rfl rfl rfl
    rfl rfl codeAt_165 (by decide) (by decide) w wpc F wb
  refine Run.seq (B₂ := 2788) st1 (fun w1 ⟨p1, b1⟩ => ?_) (by simp only [show blk160.res.cycles = 5 by kernel_rfl]; norm_num)
  refine (Run.steps (B := 2547) (symRun_sound blk173 codeAt_173 w1 p1 (by simp only [blk173.res, rv_simp])) ?_).mono
    (by simp only [show blk173.res.cycles = 1 by kernel_rfl]; norm_num) (fun _ h => h)
  have p2 : (blk173.res.toState w1).pc = pcOf 860 := by simp only [blk173.res, rv_simp]
  have b2 : BytesEq (blk173.res.toState w1) (applyCopies secCp F) := by
    intro a ha; rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, b1 a ha]; rfl
  refine (scat_run _ p2 _ b2).mono (le_refl _) (fun x ⟨xpc, xb⟩ => ⟨xpc, ?_⟩)
  intro a ha
  rw [xb a ha, ← applyCopies_append]
  rfl


end SigGolfCandidate.Expand
