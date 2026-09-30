import SigGolfCandidate.Expand.Code

/-!
# Machine trace seams for the 12-byte mixed-radix counter tail

Seven instructions at PC 226 load the 96-bit tail and classify its quotient
rank. PC 233 branches to failure at PC 284 for a noncanonical rank. The
39-instruction accepted block decodes and stores five LE32 counters, then
jumps to the existing success block at PC 281.
-/

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def counterPrelude : List (BitVec 32) := seg226Packed.take 7
def counterBranch : List (BitVec 32) := (seg226Packed.drop 7).take 1
def counterValidBody : List (BitVec 32) := (seg226Packed.drop 8).take 39

theorem counterPrelude_length : counterPrelude.length = 7 := by decide
theorem counterBranch_length : counterBranch.length = 1 := by decide
theorem counterValidBody_length : counterValidBody.length = 39 := by decide

theorem codeAt_counterPrelude : CodeAt image (pcOf 226) counterPrelude := by
  obtain ⟨hbase, halign, hbound, hprefix⟩ := codeAt_226
  refine ⟨hbase, halign, ?_, ?_⟩
  · have hlen : counterPrelude.length ≤ seg226.length := by decide
    omega
  · exact List.IsPrefix.trans (by decide : counterPrelude <+: seg226) hprefix

theorem codeAt_counterBranch : CodeAt image (pcOf 233) counterBranch := by
  have hprefix := codeAt_226.2.2.2
  change seg226 <+: image.code.drop 226 at hprefix
  obtain ⟨suffix, hwhole⟩ := hprefix
  have hdrop : seg226.drop 7 <+: (image.code.drop 226).drop 7 := by
    refine ⟨suffix, ?_⟩
    rw [← hwhole, List.drop_append_of_le_length (by decide : 7 ≤ seg226.length)]
  have hsmall : counterBranch <+: seg226.drop 7 := by decide
  have hfinal := List.IsPrefix.trans hsmall hdrop
  refine ⟨by decide, by decide, by decide, ?_⟩
  change counterBranch <+: image.code.drop 233
  simpa [List.drop_drop] using hfinal

theorem codeAt_counterValidBody : CodeAt image (pcOf 234) counterValidBody := by
  have hprefix := codeAt_226.2.2.2
  change seg226 <+: image.code.drop 226 at hprefix
  obtain ⟨suffix, hwhole⟩ := hprefix
  have hdrop : seg226.drop 8 <+: (image.code.drop 226).drop 8 := by
    refine ⟨suffix, ?_⟩
    rw [← hwhole, List.drop_append_of_le_length (by decide : 8 ≤ seg226.length)]
  have hsmall : counterValidBody <+: seg226.drop 8 := by decide
  have hfinal := List.IsPrefix.trans hsmall hdrop
  refine ⟨by decide, by decide, by decide, ?_⟩
  change counterValidBody <+: image.code.drop 234
  simpa [List.drop_drop] using hfinal

sym_block blk226PackedPrelude := symRun { noAlias := true } counterPrelude (pcOf 226) 8
sym_block blk230PackedBranch := symRun { noAlias := true } counterBranch (pcOf 233) 2
sym_block blk231PackedBody := symRun { noAlias := true } counterValidBody (pcOf 234) 40

/-- Load and classify the packed counter tail without writing memory. -/
theorem packedPrelude_run (u : MachineState)
    (hpc : u.pc = pcOf 226)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0) :
    Steps image u 7 7 (blk226PackedPrelude.res.toState u) ∧
      (blk226PackedPrelude.res.toState u).pc = pcOf 233 ∧
      ∀ a, (blk226PackedPrelude.res.toState u).getMem a = u.getMem a := by
  have hobl : blk226PackedPrelude.res.obligs u := by
    simp only [blk226PackedPrelude.res, rv_simp, h6]
    ex_bvsimp [accessValid_ofNat]
    omega
  have hsteps := symRun_sound blk226PackedPrelude codeAt_counterPrelude u hpc hobl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show blk226PackedPrelude.res.steps = 7 by kernel_rfl,
      show blk226PackedPrelude.res.cycles = 7 by kernel_rfl] using hsteps
  · simp only [blk226PackedPrelude.res, rv_simp]
  · intro a
    simp only [Result.toState_getMem, blk226PackedPrelude.res, rv_simp]

def badTailW (hi : Word) : Word :=
  (if BitVec.ult (hi >>> 14) 250563 then 1 else 0) ^^^ 1

theorem packedPrelude_words (u : MachineState)
    (h6 : u.getReg .x6 = BitVec.ofNat 64 0x4aa0) :
    (blk226PackedPrelude.res.toState u).getReg .x11 = u.getMem (BitVec.ofNat 64 0x4aa0) ∧
    (blk226PackedPrelude.res.toState u).getReg .x12 =
      LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0 ∧
    (blk226PackedPrelude.res.toState u).getReg .x13 =
      LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0 >>> 14 ∧
    (blk226PackedPrelude.res.toState u).getReg .x14 =
      badTailW (LoadKind.fromWord .wu (u.getMem (BitVec.ofNat 64 0x4aa8)) 0) := by
  simp only [Result.toState_getReg, blk226PackedPrelude.res, rv_simp, h6, badTailW]
  rw [show (19104#64 : Word) + 8#64 = 19112#64 from by decide]
  norm_num

/-- The canonicality branch reads `x14` and changes no registers or memory. -/
theorem packedBranch_run (u : MachineState) (hpc : u.pc = pcOf 233) :
    Steps image u 1 1 (blk230PackedBranch.res.toState u) ∧
      (u.getReg .x14 = 0 → (blk230PackedBranch.res.toState u).pc = pcOf 234) ∧
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
    change (if (u.getReg .x14 != 0#64) = true then 5232#64 else 5032#64) = pcOf 284
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
    (hpc : u.pc = pcOf 234)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    Steps image u 39 63 (blk231PackedBody.res.toState u) ∧
      (blk231PackedBody.res.toState u).pc = pcOf 281 := by
  have hobl : blk231PackedBody.res.obligs u := by
    simp only [blk231PackedBody.res, rv_simp, h7]
    ex_bvsimp [accessValid_ofNat]
    omega
  have hsteps := symRun_sound blk231PackedBody codeAt_counterValidBody u hpc hobl
  refine ⟨?_, ?_⟩
  · simpa only [show blk231PackedBody.res.steps = 39 by kernel_rfl,
      show blk231PackedBody.res.cycles = 63 by kernel_rfl] using hsteps
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

def quotW (q : Word) : Nat → Word
  | 0 => q
  | n+1 => rv64_divu (quotW q n) 17

def digitW (lo hi q : Word) : Nat → Word
  | 0 => (lo &&& 32767) + (rv64_remu q 17 <<< 15)
  | 1 => ((lo >>> 15) &&& 32767) + (rv64_remu (quotW q 1) 17 <<< 15)
  | 2 => ((lo >>> 30) &&& 32767) + (rv64_remu (quotW q 2) 17 <<< 15)
  | 3 => ((lo >>> 45) &&& 32767) + (rv64_remu (quotW q 3) 17 <<< 15)
  | _ => (lo >>> 60) + ((hi &&& 16383) <<< 4) + (quotW q 4 <<< 18)

theorem packedBody_mem0 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20b8) =
      replaceWord32 (replaceWord32 (u.getMem (BitVec.ofNat 64 0x20b8)) 0 ((digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) 0).truncate 32)) 1 ((digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) 1).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  norm_num
  simp only [digitW, quotW]
  rfl

theorem packedBody_mem1 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20c0) =
      replaceWord32 (replaceWord32 (u.getMem (BitVec.ofNat 64 0x20c0)) 0 ((digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) 2).truncate 32)) 1 ((digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) 3).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  norm_num
  simp only [digitW, quotW]
  rfl

theorem packedBody_mem2 (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    (blk231PackedBody.res.toState u).getMem (BitVec.ofNat 64 0x20c8) =
      replaceWord32 (u.getMem (BitVec.ofNat 64 0x20c8)) 0 ((digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) 4).truncate 32) := by
  simp only [Result.toState_getMem, blk231PackedBody.res, rv_simp, h7]
  norm_num
  simp only [digitW, quotW]
  rfl

theorem packedBody_halves (u : MachineState)
    (h7 : u.getReg .x7 = BitVec.ofNat 64 0x20b8) :
    let v := blk231PackedBody.res.toState u
    let d := fun i => (digitW (u.getReg .x11) (u.getReg .x12) (u.getReg .x13) i).truncate 32
    lo32 (v.getMem (BitVec.ofNat 64 0x20b8)) = d 0 ∧
    hi32 (v.getMem (BitVec.ofNat 64 0x20b8)) = d 1 ∧
    lo32 (v.getMem (BitVec.ofNat 64 0x20c0)) = d 2 ∧
    hi32 (v.getMem (BitVec.ofNat 64 0x20c0)) = d 3 ∧
    lo32 (v.getMem (BitVec.ofNat 64 0x20c8)) = d 4 := by
  dsimp only
  rw [packedBody_mem0 u h7, packedBody_mem1 u h7, packedBody_mem2 u h7]
  simp only [lo32_replace1, lo32_replace0, hi32_replace1, and_self]

end SigGolfCandidate.Expand
