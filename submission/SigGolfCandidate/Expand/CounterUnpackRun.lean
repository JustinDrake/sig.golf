import SigGolfCandidate.Expand.Code

/-!
# Machine trace seams for the 14-byte counter tail

The first five aligned body copies reuse `Expand.Copy.copy_loop`. At PC 226,
four instructions load the 64+48-bit tail and expose the two unused bits.
PC 230 branches to the existing failure block 284 if either bit is set.
The accepted branch decodes and stores the five LE32 witness counters, then
jumps to the existing success block 281.
-/

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def counterPrelude : List (BitVec 32) := seg226Packed.take 4
def counterBranch : List (BitVec 32) := (seg226Packed.drop 4).take 1
def counterValidBody : List (BitVec 32) := (seg226Packed.drop 5).take 21

theorem counterPrelude_length : counterPrelude.length = 4 := by decide
theorem counterBranch_length : counterBranch.length = 1 := by decide
theorem counterValidBody_length : counterValidBody.length = 21 := by decide

theorem codeAt_counterPrelude : CodeAt image (pcOf 226) counterPrelude := by
  obtain ⟨hbase, halign, hbound, hprefix⟩ := codeAt_226
  refine ⟨hbase, halign, ?_, ?_⟩
  · have hlen : counterPrelude.length ≤ seg226.length := by decide
    omega
  · exact List.IsPrefix.trans (by decide : counterPrelude <+: seg226) hprefix

theorem codeAt_counterBranch : CodeAt image (pcOf 230) counterBranch := by
  have hprefix := codeAt_226.2.2.2
  change seg226 <+: image.code.drop 226 at hprefix
  obtain ⟨suffix, hwhole⟩ := hprefix
  have hdrop : seg226.drop 4 <+: (image.code.drop 226).drop 4 := by
    refine ⟨suffix, ?_⟩
    rw [← hwhole, List.drop_append_of_le_length (by decide : 4 ≤ seg226.length)]
  have hsmall : counterBranch <+: seg226.drop 4 := by decide
  have hfinal := List.IsPrefix.trans hsmall hdrop
  refine ⟨by decide, by decide, by decide, ?_⟩
  change counterBranch <+: image.code.drop 230
  simpa [List.drop_drop] using hfinal

theorem codeAt_counterValidBody : CodeAt image (pcOf 231) counterValidBody := by
  have hprefix := codeAt_226.2.2.2
  change seg226 <+: image.code.drop 226 at hprefix
  obtain ⟨suffix, hwhole⟩ := hprefix
  have hdrop : seg226.drop 5 <+: (image.code.drop 226).drop 5 := by
    refine ⟨suffix, ?_⟩
    rw [← hwhole, List.drop_append_of_le_length (by decide : 5 ≤ seg226.length)]
  have hsmall : counterValidBody <+: seg226.drop 5 := by decide
  have hfinal := List.IsPrefix.trans hsmall hdrop
  refine ⟨by decide, by decide, by decide, ?_⟩
  change counterValidBody <+: image.code.drop 231
  simpa [List.drop_drop] using hfinal

sym_block blk226PackedPrelude := symRun { noAlias := true } counterPrelude (pcOf 226) 5
sym_block blk230PackedBranch := symRun { noAlias := true } counterBranch (pcOf 230) 2
sym_block blk231PackedBody := symRun { noAlias := true } counterValidBody (pcOf 231) 22

/-- Four reads reconstruct the packed counter tail without writing memory. -/
theorem packedPrelude_run (u : MachineState)
    (hpc : u.pc = pcOf 226)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0) :
    Steps image u 4 4 (blk226PackedPrelude.res.toState u) ∧
      (blk226PackedPrelude.res.toState u).pc = pcOf 230 ∧
      ∀ a, (blk226PackedPrelude.res.toState u).getMem a = u.getMem a := by
  have hobl : blk226PackedPrelude.res.obligs u := by
    simp only [blk226PackedPrelude.res, rv_simp, h6]
    ex_bvsimp [accessValid_ofNat]
    omega
  have hsteps := symRun_sound blk226PackedPrelude codeAt_counterPrelude u hpc hobl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show blk226PackedPrelude.res.steps = 4 by kernel_rfl,
      show blk226PackedPrelude.res.cycles = 4 by kernel_rfl] using hsteps
  · simp only [blk226PackedPrelude.res, rv_simp]
  · intro a
    simp only [Result.toState_getMem, blk226PackedPrelude.res, rv_simp]

theorem packedPrelude_words (u : MachineState)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0) :
    (blk226PackedPrelude.res.toState u).getReg .x11 =
        u.getMem (BitVec.ofNat 64 0x4aa0) ∧
    (blk226PackedPrelude.res.toState u).getReg .x12 =
        LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0 ∧
    (blk226PackedPrelude.res.toState u).getReg .x13 =
        LoadKind.fromWord .hu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4 ∧
    (blk226PackedPrelude.res.toState u).getReg .x14 =
        LoadKind.fromWord .hu (u.getMem (BitVec.ofNat 64 0x4aa8)) 4 >>> 14 := by
  simp only [Result.toState_getReg, blk226PackedPrelude.res, rv_simp, h6]
  have haddr : (19104#64 : Word) + 8#64 = 19112#64 := by decide
  simp only [haddr]
  norm_num

/-- The canonicality branch reads `x14` and changes no registers or memory. -/
theorem packedBranch_run (u : MachineState) (hpc : u.pc = pcOf 230) :
    Steps image u 1 1 (blk230PackedBranch.res.toState u) ∧
      (u.getReg .x14 = 0 → (blk230PackedBranch.res.toState u).pc = pcOf 231) ∧
      (u.getReg .x14 ≠ 0 → (blk230PackedBranch.res.toState u).pc = pcOf 284) ∧
      (∀ r, (blk230PackedBranch.res.toState u).getReg r = u.getReg r) ∧
      ∀ a, (blk230PackedBranch.res.toState u).getMem a = u.getMem a := by
  have hsteps := symRun_sound blk230PackedBranch codeAt_counterBranch u hpc
    (by simp only [blk230PackedBranch.res, rv_simp])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [show blk230PackedBranch.res.steps = 1 by kernel_rfl,
      show blk230PackedBranch.res.cycles = 1 by kernel_rfl] using hsteps
  · intro hzero
    simp only [blk230PackedBranch.res, rv_simp, hzero]
    decide
  · intro hnz
    simp only [blk230PackedBranch.res, rv_simp]
    change (if (u.getReg .x14 != 0#64) = true then 5232#64 else 5020#64) = pcOf 284
    have hb : (u.getReg .x14 != 0#64) = true := bne_iff_ne.mpr hnz
    rw [if_pos hb]
  · intro r
    rw [Result.toState_getReg]
    change (RegFile.init.get r).eval u = u.getReg r
    exact RegFile.init_get_eval u r
  · intro a
    simp only [Result.toState_getMem, blk230PackedBranch.res, rv_simp]

/-- The accepted tail writes five LE32 witness counters and jumps to PC 281. -/
theorem packedBody_run (u : MachineState)
    (hpc : u.pc = pcOf 231)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    Steps image u 21 21 (blk231PackedBody.res.toState u) ∧
      (blk231PackedBody.res.toState u).pc = pcOf 281 := by
  have hobl : blk231PackedBody.res.obligs u := by
    simp only [blk231PackedBody.res, rv_simp, h7]
    ex_bvsimp [accessValid_ofNat]
    omega
  have hsteps := symRun_sound blk231PackedBody codeAt_counterValidBody u hpc hobl
  refine ⟨?_, ?_⟩
  · simpa only [show blk231PackedBody.res.steps = 21 by kernel_rfl,
      show blk231PackedBody.res.cycles = 21 by kernel_rfl] using hsteps
  · simp only [blk231PackedBody.res, rv_simp]

theorem packedBody_frame (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    Frame u (blk231PackedBody.res.toState u)
      (fun a => a = 0x20b8 ∨ a = 0x20c0 ∨ a = 0x20c8) := by
  apply frame_toState
  intro a ha hW p hp
  simp only [blk231PackedBody.res, rv_simp, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    simp only [Addr.eval, E.eval, h7]
    intro heq
    apply hW
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha] at hn
    norm_num at hn
    omega

theorem packedBody_lowCounter (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    lo32 ((blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20b8)) =
      ((u.getReg .x11 <<< 42) >>> 42).truncate 32 := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  have h8 : (8376#64 : Word) + 8#64 = 8384#64 := by decide
  have h16 : (8376#64 : Word) + 16#64 = 8392#64 := by decide
  simp only [h8, h16]
  norm_num
  rw [if_neg (by decide : (8376#64 : Word) ≠ 8392#64),
    if_neg (by decide : (8376#64 : Word) ≠ 8384#64)]
  simp only [lo32_replace1, lo32_replace0]

theorem packedBody_mem0 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20b8) =
      replaceWord32
        (replaceWord32 (u.getMem (BitVec.ofNat 64 0x20b8)) 0
          ((u.getReg .x11 <<< 42 >>> 42).truncate 32)) 1
        ((u.getReg .x11 >>> 22 <<< 42 >>> 42).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  have h8 : (8376#64 : Word) + 8#64 = 8384#64 := by decide
  have h16 : (8376#64 : Word) + 16#64 = 8392#64 := by decide
  simp only [h8, h16]
  rw [if_neg (by decide : (8376#64 : Word) ≠ 8392#64),
    if_neg (by decide : (8376#64 : Word) ≠ 8384#64)]
  rfl

theorem packedBody_mem1 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20c0) =
      replaceWord32
        (replaceWord32 (u.getMem (BitVec.ofNat 64 0x20c0)) 0
          ((u.getReg .x11 >>> 44 |||
            ((u.getReg .x12 ||| u.getReg .x13 <<< 32) &&& 3#64) <<< 20).truncate 32)) 1
        (((u.getReg .x12 ||| u.getReg .x13 <<< 32) >>> 2 <<< 42 >>> 42).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  have h8 : (8376#64 : Word) + 8#64 = 8384#64 := by decide
  have h16 : (8376#64 : Word) + 16#64 = 8392#64 := by decide
  simp only [h8, h16]
  rw [if_neg (by decide : (8384#64 : Word) ≠ 8392#64)]
  simp only [if_true]
  rfl

theorem packedBody_mem2 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20c8) =
      replaceWord32 (u.getMem (BitVec.ofNat 64 0x20c8)) 0
        (((u.getReg .x12 ||| u.getReg .x13 <<< 32) >>> 24).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  have h16 : (8376#64 : Word) + 16#64 = 8392#64 := by decide
  simp only [h16]
  simp only [if_true]
  rfl

/-- Each of the five `SW` results is visible in its corresponding dword half. -/
theorem packedBody_halves (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    let v := blk231PackedBody.res.toState u
    lo32 (v.getMem (BitVec.ofNat 64 0x20b8)) =
        ((u.getReg .x11 <<< 42 >>> 42).truncate 32) ∧
    hi32 (v.getMem (BitVec.ofNat 64 0x20b8)) =
        ((u.getReg .x11 >>> 22 <<< 42 >>> 42).truncate 32) ∧
    lo32 (v.getMem (BitVec.ofNat 64 0x20c0)) =
        ((u.getReg .x11 >>> 44 |||
          ((u.getReg .x12 ||| u.getReg .x13 <<< 32) &&& 3#64) <<< 20).truncate 32) ∧
    hi32 (v.getMem (BitVec.ofNat 64 0x20c0)) =
        (((u.getReg .x12 ||| u.getReg .x13 <<< 32) >>> 2 <<< 42 >>> 42).truncate 32) ∧
    lo32 (v.getMem (BitVec.ofNat 64 0x20c8)) =
        (((u.getReg .x12 ||| u.getReg .x13 <<< 32) >>> 24).truncate 32) := by
  dsimp only
  refine ⟨packedBody_lowCounter u h7, ?_, ?_, ?_, ?_⟩
  · rw [packedBody_mem0 u h7]
    simp only [hi32_replace1]
  · rw [packedBody_mem1 u h7]
    simp only [lo32_replace1, lo32_replace0]
  · rw [packedBody_mem1 u h7]
    simp only [hi32_replace1]
  · rw [packedBody_mem2 u h7]
    simp only [lo32_replace0]

end SigGolfCandidate.Expand
