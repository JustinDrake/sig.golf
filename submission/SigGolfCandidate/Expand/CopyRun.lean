import SigGolfCandidate.Expand.Copy

/-!
# `expand`: the copy phase (instructions 139 .. 173, then the scatter 683 .. 803)

`rho` (4 words, W1: into the tweak slot of chain block `(0, 1)`, `0x13C0`), the pi bytes (`pi_loop`:
byte `s` = low byte of `KEYS[s]`, at `0xA00 + s`), the secrets (W1: the 16-byte stride-64 loop, secret
`s` into the tweak slot of chain block `(0, 2 + s)`, `0x1400 + 64 s`), then `j scatter` (173): per
layer, the 42 chain values (16 bytes each, signature stride 16, witness stride 64: into the value slot
`block(lay, i) + 48` of the W1a chain array) and the path (contiguous at layer 0, stride 64 below layer 0); then
`j pors_init` (803 -> 495). The witness buffer's byte view afterwards is
`applyCopies copyRest (piF A 15 (applyCopy rho f0))` of the byte view `f0` before the phase.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem


def pathCode720 : List (BitVec 32) := seg720 ++ [0xf64ff06f]
sym_block blkPath720 := symRun { noAlias := true } pathCode720 (pcOf 720) 7
theorem codeAt_path720 : CodeAt image (pcOf 720) pathCode720 := by unfold CodeAt; decide +kernel
theorem codeAt_stub174 : CodeAt image (pcOf 174) loop16Code := by unfold CodeAt; decide +kernel
def retCode182 : List (BitVec 32) := [0x0950006f]
sym_block blkRet182 := symRun { noAlias := true } retCode182 (pcOf 182) 2
theorem codeAt_ret182 : CodeAt image (pcOf 182) retCode182 := by unfold CodeAt; decide +kernel

def pathCode744 : List (BitVec 32) := seg744 ++ [0xf28ff06f]
sym_block blkPath744 := symRun { noAlias := true } pathCode744 (pcOf 744) 7
theorem codeAt_path744 : CodeAt image (pcOf 744) pathCode744 := by unfold CodeAt; decide +kernel
theorem codeAt_stub183 : CodeAt image (pcOf 183) loop16Code := by unfold CodeAt; decide +kernel
def retCode191 : List (BitVec 32) := [0x0d10006f]
sym_block blkRet191 := symRun { noAlias := true } retCode191 (pcOf 191) 2
theorem codeAt_ret191 : CodeAt image (pcOf 191) retCode191 := by unfold CodeAt; decide +kernel

def pathCode768 : List (BitVec 32) := seg768 ++ [0xeecff06f]
sym_block blkPath768 := symRun { noAlias := true } pathCode768 (pcOf 768) 7
theorem codeAt_path768 : CodeAt image (pcOf 768) pathCode768 := by unfold CodeAt; decide +kernel
theorem codeAt_stub192 : CodeAt image (pcOf 192) loop16Code := by unfold CodeAt; decide +kernel
def retCode200 : List (BitVec 32) := [0x10d0006f]
sym_block blkRet200 := symRun { noAlias := true } retCode200 (pcOf 200) 2
theorem codeAt_ret200 : CodeAt image (pcOf 200) retCode200 := by unfold CodeAt; decide +kernel

def pathCode792 : List (BitVec 32) := seg792 ++ [0xeb0ff06f]
sym_block blkPath792 := symRun { noAlias := true } pathCode792 (pcOf 792) 7
theorem codeAt_path792 : CodeAt image (pcOf 792) pathCode792 := by unfold CodeAt; decide +kernel
theorem codeAt_stub201 : CodeAt image (pcOf 201) loop16Code := by unfold CodeAt; decide +kernel
def retCode209 : List (BitVec 32) := [0x1490006f]
sym_block blkRet209 := symRun { noAlias := true } retCode209 (pcOf 209) 2
theorem codeAt_ret209 : CodeAt image (pcOf 209) retCode209 := by unfold CodeAt; decide +kernel

/-- The pi bytes on top of `g`. -/
def piF (A : Nat → Nat) (j : Nat) (g : Nat → Byte) : Nat → Byte := fun a =>
  if 0xA00 ≤ a ∧ a < 0xA00 + j then byte (A (a - 0xA00)) else g a

/-- Signature offsets of the layer bodies (`sigLayerOff`), witness path offsets (`pathOff`), path words. -/
def sgOff (lay : Nat) : Nat := [2128, 2976, 3744, 4512, 5280].getD lay 0
def pOff (lay : Nat) : Nat := [2656, 4992, 7680, 10368, 13056].getD lay 0
def pWords (lay : Nat) : Nat := [44, 24, 24, 24, 20].getD lay 0

/-- The scatter copies of layer `lay`: the 42 chain values into the value slots, then the path. -/
def chainCp (lay : Nat) : List (Nat × Nat × Nat) :=
  strideCopies (0x24B00 + sgOff lay) (0x800 + 2992 + 2688 * lay) 42
def pathCp (lay : Nat) : Nat × Nat × Nat := (0x24B00 + sgOff lay + 672, 0x800 + pOff lay, pWords lay)
def layCp (lay : Nat) : List (Nat × Nat × Nat) := chainCp lay ++ (if lay = 0 then [pathCp lay] else
  strideCopies (0x24B00 + sgOff lay + 672) (0x800 + pOff lay) (height lay))

/-- The secret copies (W1): secret `s` into the tweak slot of chain block `(0, 2 + s)`. -/
def secCp : List (Nat × Nat × Nat) := strideCopies 0x24B10 0x1400 15

/-- The copies after the pi loop: the secrets, then the scatter of layers 0 .. 4. -/
def copyRest : List (Nat × Nat × Nat) :=
  secCp ++ (layCp 0 ++ layCp 1 ++ layCp 2 ++ layCp 3 ++ layCp 4)

theorem pi_loop (A : Nat → Nat) (g : Nat → Byte) :
    ∀ k (v : MachineState), k ≤ 15 → (v.pc = if k = 0 then pcOf 160 else pcOf 153) →
      v.getReg .x8 = BitVec.ofNat 64 (15 - k) → v.getReg .x25 = BitVec.ofNat 64 0xA00 →
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
      by_cases h1 : a = 0xA00 + (15 - (k + 1))
      · rw [if_pos h1, if_pos (by omega), show a - 0xA00 = 15 - (k + 1) by omega]; rfl
      · rw [if_neg h1]
        by_cases h2 : 0xA00 ≤ a ∧ a < 0xA00 + (15 - (k + 1))
        · rw [if_pos h2, if_pos (by omega)]
        · rw [if_neg h2, if_neg (by omega)]
    · intro p hp
      rw [wm _ (by rw [Ne, ofNat_eq_iff]; omega)]; exact ha p hp




/-- One layer of the scatter: the stride copy of the chain values, then the contiguous top path or scattered lower path. -/
theorem scat_0 (u : MachineState) (hpc : u.pc = pcOf 683) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 610 (fun v => v.pc = pcOf 707 ∧ BytesEq v (applyCopies (layCp 0) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 0) (dst := 0x800 + 2992 + 2688 * 0) (n := 42) (e := 696)
    blk683 codeAt_683 rfl rfl rfl rfl rfl rfl codeAt_688 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 269) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk683.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun (src := 0x24B00 + sgOff 0 + 672) (dst := 0x800 + pOff 0) (n := pWords 0) (e := 707)
    blk696 codeAt_696 rfl rfl rfl rfl rfl rfl codeAt_701 (by decide) (by decide) v vpc _ vb
  refine (s2.mono (by simp only [show blk696.res.cycles = 5 by kernel_rfl]; decide) (fun w ⟨wpc, wb⟩ => ⟨wpc, ?_⟩))
  unfold layCp chainCp pathCp
  rw [if_pos rfl, applyCopies_append, applyCopies_single]
  exact wb

theorem scat_1 (u : MachineState) (hpc : u.pc = pcOf 707) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 731 ∧ BytesEq v (applyCopies (layCp 1) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 1) (dst := 0x800 + 2992 + 2688 * 1) (n := 42) (e := 720)
    blk707 codeAt_707 rfl rfl rfl rfl rfl rfl codeAt_712 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk707.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 1 + 672) (dst := 0x800 + pOff 1) (n := 6) (e := 182)
    blkPath720 codeAt_path720 rfl rfl rfl rfl rfl rfl codeAt_stub174 (by decide) (by decide) v vpc _ vb
  refine Run.seq (B₂ := 1) s2 (fun w ⟨wpc, wb⟩ => ?_)
    (by simp only [show blkPath720.res.cycles = 6 by kernel_rfl]; norm_num)
  refine Run.of (symRun_sound blkRet182 codeAt_ret182 w wpc (by simp only [blkRet182.res, rv_simp]))
    (by simp only [show blkRet182.res.cycles = 1 by kernel_rfl]; norm_num)
    ⟨by simp only [blkRet182.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, wb a ha]
  simp only [layCp, chainCp, if_neg (by decide : ¬ 1 = 0), applyCopies_append]
  rfl

theorem scat_2 (u : MachineState) (hpc : u.pc = pcOf 731) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 755 ∧ BytesEq v (applyCopies (layCp 2) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 2) (dst := 0x800 + 2992 + 2688 * 2) (n := 42) (e := 744)
    blk731 codeAt_731 rfl rfl rfl rfl rfl rfl codeAt_736 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk731.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 2 + 672) (dst := 0x800 + pOff 2) (n := 6) (e := 191)
    blkPath744 codeAt_path744 rfl rfl rfl rfl rfl rfl codeAt_stub183 (by decide) (by decide) v vpc _ vb
  refine Run.seq (B₂ := 1) s2 (fun w ⟨wpc, wb⟩ => ?_)
    (by simp only [show blkPath744.res.cycles = 6 by kernel_rfl]; norm_num)
  refine Run.of (symRun_sound blkRet191 codeAt_ret191 w wpc (by simp only [blkRet191.res, rv_simp]))
    (by simp only [show blkRet191.res.cycles = 1 by kernel_rfl]; norm_num)
    ⟨by simp only [blkRet191.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, wb a ha]
  simp only [layCp, chainCp, if_neg (by decide : ¬ 2 = 0), applyCopies_append]
  rfl

theorem scat_3 (u : MachineState) (hpc : u.pc = pcOf 755) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 490 (fun v => v.pc = pcOf 779 ∧ BytesEq v (applyCopies (layCp 3) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 3) (dst := 0x800 + 2992 + 2688 * 3) (n := 42) (e := 768)
    blk755 codeAt_755 rfl rfl rfl rfl rfl rfl codeAt_760 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 149) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk755.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 3 + 672) (dst := 0x800 + pOff 3) (n := 6) (e := 200)
    blkPath768 codeAt_path768 rfl rfl rfl rfl rfl rfl codeAt_stub192 (by decide) (by decide) v vpc _ vb
  refine Run.seq (B₂ := 1) s2 (fun w ⟨wpc, wb⟩ => ?_)
    (by simp only [show blkPath768.res.cycles = 6 by kernel_rfl]; norm_num)
  refine Run.of (symRun_sound blkRet200 codeAt_ret200 w wpc (by simp only [blkRet200.res, rv_simp]))
    (by simp only [show blkRet200.res.cycles = 1 by kernel_rfl]; norm_num)
    ⟨by simp only [blkRet200.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, wb a ha]
  simp only [layCp, chainCp, if_neg (by decide : ¬ 3 = 0), applyCopies_append]
  rfl

theorem scat_4 (u : MachineState) (hpc : u.pc = pcOf 779) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 466 (fun v => v.pc = pcOf 803 ∧ BytesEq v (applyCopies (layCp 4) F)) := by
  have s1 := stageRun16 (src := 0x24B00 + sgOff 4) (dst := 0x800 + 2992 + 2688 * 4) (n := 42) (e := 792)
    blk779 codeAt_779 rfl rfl rfl rfl rfl rfl codeAt_784 (by decide) (by decide) u hpc F hF
  refine Run.seq (B₂ := 125) s1 (fun v ⟨vpc, vb⟩ => ?_) (by simp only [show blk779.res.cycles = 5 by kernel_rfl]; norm_num)
  have s2 := stageRun16 (src := 0x24B00 + sgOff 4 + 672) (dst := 0x800 + pOff 4) (n := 5) (e := 209)
    blkPath792 codeAt_path792 rfl rfl rfl rfl rfl rfl codeAt_stub201 (by decide) (by decide) v vpc _ vb
  refine Run.seq (B₂ := 1) s2 (fun w ⟨wpc, wb⟩ => ?_)
    (by simp only [show blkPath792.res.cycles = 6 by kernel_rfl]; norm_num)
  refine Run.of (symRun_sound blkRet209 codeAt_ret209 w wpc (by simp only [blkRet209.res, rv_simp]))
    (by simp only [show blkRet209.res.cycles = 1 by kernel_rfl]; norm_num)
    ⟨by simp only [blkRet209.res, rv_simp], ?_⟩
  intro a ha
  rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, wb a ha]
  simp only [layCp, chainCp, if_neg (by decide : ¬ 4 = 0), applyCopies_append]
  rfl

/-- The scatter (683 .. 803): the five layers, then `j pors_init`. -/
theorem scat_run (u : MachineState) (hpc : u.pc = pcOf 683) (F : Nat → Byte) (hF : BytesEq u F) :
    Run u 2547 (fun v => v.pc = pcOf 495 ∧
      BytesEq v (applyCopies (layCp 0 ++ layCp 1 ++ layCp 2 ++ layCp 3 ++ layCp 4) F)) := by
  refine Run.seq (B₂ := 1937) (scat_0 u hpc F hF) (fun u0 ⟨p0, b0⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 1447) (scat_1 u0 p0 _ b0) (fun u1 ⟨p1, b1⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 957) (scat_2 u1 p1 _ b1) (fun u2 ⟨p2, b2⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 467) (scat_3 u2 p2 _ b2) (fun u3 ⟨p3, b3⟩ => ?_) (by norm_num)
  refine Run.seq (B₂ := 1) (scat_4 u3 p3 _ b3) (fun u4 ⟨p4, b4⟩ => ?_) (by norm_num)
  refine Run.of (symRun_sound blk803 codeAt_803 u4 p4 (by simp only [blk803.res, rv_simp]))
    (by simp only [show blk803.res.cycles = 1 by kernel_rfl]; norm_num) ⟨by simp only [blk803.res, rv_simp], ?_⟩
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
  have p2 : (blk173.res.toState w1).pc = pcOf 683 := by simp only [blk173.res, rv_simp]
  have b2 : BytesEq (blk173.res.toState w1) (applyCopies secCp F) := by
    intro a ha; rw [getByte_ofNat _ _ ha, toState_getMem_nil rfl, ← getByte_ofNat _ _ ha, b1 a ha]; rfl
  refine (scat_run _ p2 _ b2).mono (le_refl _) (fun x ⟨xpc, xb⟩ => ⟨xpc, ?_⟩)
  intro a ha
  rw [xb a ha, ← applyCopies_append]
  rfl


end SigGolfCandidate.Expand
