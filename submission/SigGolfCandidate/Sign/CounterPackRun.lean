import SigGolfCandidate.Sign.Code
import SigGolfCandidate.Sign.Bytes
import SigGolfCandidate.Sign.Layer
import SigGolfCandidate.Expand.Copy

/-!
# Machine trace seams for the 13-byte counter tail

The old `PackRun.pack_run` still reaches PC 2841 and proves its 491 mixed
signature dwords. The jump at 2841 starts five five-instruction setup blocks followed by
five copies using the existing polymorphic `Expand.Copy.copy_loop` theorem.
Each copy writes one aligned body range. The final block reloads the five
staged counters and writes 13 bytes before HALT.
-/

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

set_option maxRecDepth 100000

sym_block blk2841PackedJump := symRun { noAlias := true } seg2841 (pcOf 2841) 2
sym_block blk2887Packed := symRun { noAlias := true } seg2887 (pcOf 2887) 6
sym_block blk2898Packed := symRun { noAlias := true } seg2898 (pcOf 2898) 6
sym_block blk2909Packed := symRun { noAlias := true } seg2909 (pcOf 2909) 6
sym_block blk2920Packed := symRun { noAlias := true } seg2920 (pcOf 2920) 6
sym_block blk2931Packed := symRun { noAlias := true } seg2931 (pcOf 2931) 6
sym_block blk2942PackedTail := symRun { noAlias := true } seg2942 (pcOf 2942) 26

/-- The inherited pack's final PC now jumps over the randomizer helper and
enters the body-copy appendix without changing memory or the result registers. -/
theorem packedJump_run (t : MachineState) (hpc : t.pc = pcOf 2841) :
    ∃ u, Steps image t 1 1 u ∧ u.pc = pcOf 2887 ∧
      (∀ a, u.getMem a = t.getMem a) ∧
      u.getReg .x5 = t.getReg .x5 ∧ u.getReg .x10 = t.getReg .x10 := by
  have hs := symRun_sound blk2841PackedJump codeAt_2841 t hpc
    (by simp only [blk2841PackedJump.res, rv_simp])
  refine ⟨blk2841PackedJump.res.toState t, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [show blk2841PackedJump.res.steps = 1 from rfl,
      show blk2841PackedJump.res.cycles = 1 from rfl] using hs
  · simp only [blk2841PackedJump.res, rv_simp]
  · intro a
    rw [Result.toState_getMem, show blk2841PackedJump.res.st.mem = [] from rfl, memEval_nil]
  · simp only [Result.toState_getReg, blk2841PackedJump.res, rv_simp]
  · simp only [Result.toState_getReg, blk2841PackedJump.res, rv_simp]

/-- The five staged body copies performed after the inherited mixed pack. -/
def packedBodyCopies : List (Nat × Nat × Nat) :=
  [(0x908, 0x3b60, 212), (0xc60, 0x3eb0, 192),
   (0xfb8, 0x41b0, 192), (0x1310, 0x44b0, 192),
   (0x1668, 0x47b0, 188)]

theorem packedBodyCopies_layout :
    packedBodyCopies =
      (List.range Ref.nLayers).map (fun l =>
        (CounterPackLayout.stageBodyOffset l,
         CounterPackLayout.signatureBodyOffset l,
         CounterPack.bodyBytes l / 4)) := by decide

private theorem packedBodyCopies_pairwise :
    packedBodyCopies.Pairwise (fun c c' =>
      Expand.Disj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) := by decide

private theorem packedBodyCopies_srcdst :
    ∀ c ∈ packedBodyCopies, ∀ c' ∈ packedBodyCopies,
      Expand.Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by decide

/-- Every output byte of a copied body equals its staged source byte. -/
theorem packedBodies_range (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a))))
    (c : Nat × Nat × Nat) (hc : c ∈ packedBodyCopies) :
    bytesAt u c.2.1 (4 * c.2.2) = bytesAt t c.1 (4 * c.2.2) := by
  have hdst : c.2.1 + 4 * c.2.2 < 2 ^ 64 := by
    simp only [packedBodyCopies, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hsrc : c.1 + 4 * c.2.2 < 2 ^ 64 := by
    simp only [packedBodyCopies, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> norm_num
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [hbytes _ (by omega),
    Expand.applyCopies_hit packedBodyCopies _ packedBodyCopies_pairwise
      packedBodyCopies_srcdst c hc (c.2.1 + i) (by omega) (by omega)]
  simp only [Nat.add_comm, Nat.add_sub_cancel_right]

/-- The loop destinations start after the 2144-byte signature head and all
staged source data. In particular, the five counter words remain available
to the final tail block. -/
theorem packedBodies_before (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a))))
    (a : Nat) (ha : a < 0x3b60) :
    u.getByte (BitVec.ofNat 64 a) = t.getByte (BitVec.ofNat 64 a) := by
  rw [hbytes a (by omega)]
  exact Expand.applyCopies_frame packedBodyCopies _ a (by
    intro c hc
    simp only [packedBodyCopies, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)

/-- The five word-copy loops leave the complete 2144-byte prefix intact. -/
theorem packedBodies_head (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a)))) :
    bytesAt u 0x3300 2144 = bytesAt t 0x3300 2144 := by
  unfold bytesAt
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  exact packedBodies_before t u hbytes (0x3300 + i) (by omega)

/-- The five destination ranges are consecutive, yielding the exact 3904
body bytes consumed by the compact reference serializer. -/
theorem packedBodies_bytes (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a)))) :
    bytesAt u 0x3b60 3904 =
      bytesAt t 0x908 848 ++
      (bytesAt t 0xc60 768 ++
      (bytesAt t 0xfb8 768 ++
      (bytesAt t 0x1310 768 ++ bytesAt t 0x1668 752))) := by
  have h0 : bytesAt u 0x3b60 848 = bytesAt t 0x908 848 := by
    simpa only [Nat.reduceMul] using
      packedBodies_range t u hbytes (0x908, 0x3b60, 212) (by decide)
  have h1 : bytesAt u 0x3eb0 768 = bytesAt t 0xc60 768 := by
    simpa only [Nat.reduceMul] using
      packedBodies_range t u hbytes (0xc60, 0x3eb0, 192) (by decide)
  have h2 : bytesAt u 0x41b0 768 = bytesAt t 0xfb8 768 := by
    simpa only [Nat.reduceMul] using
      packedBodies_range t u hbytes (0xfb8, 0x41b0, 192) (by decide)
  have h3 : bytesAt u 0x44b0 768 = bytesAt t 0x1310 768 := by
    simpa only [Nat.reduceMul] using
      packedBodies_range t u hbytes (0x1310, 0x44b0, 192) (by decide)
  have h4 : bytesAt u 0x47b0 752 = bytesAt t 0x1668 752 := by
    simpa only [Nat.reduceMul] using
      packedBodies_range t u hbytes (0x1668, 0x47b0, 188) (by decide)
  rw [show (3904 : Nat) = 848 + (768 + (768 + (768 + 752))) from rfl,
    bytesAt_add, show (0x3b60 + 848 : Nat) = 0x3eb0 from rfl,
    bytesAt_add, show (0x3eb0 + 768 : Nat) = 0x41b0 from rfl,
    bytesAt_add, show (0x41b0 + 768 : Nat) = 0x44b0 from rfl,
    bytesAt_add, show (0x44b0 + 768 : Nat) = 0x47b0 from rfl,
    h0, h1, h2, h3, h4]

/-- The 8-byte-aligned staged counter words survive the body-copy phase. -/
theorem packedBodies_stageWord (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a))))
    (d : Nat) (hd : d % 8 = 0) (hrange : d + 8 ≤ 0x3b60) :
    u.getMem (BitVec.ofNat 64 d) = t.getMem (BitVec.ofNat 64 d) := by
  apply Expand.getMem_eq_of_bytes t u d hd (by omega)
  intro k hk
  exact packedBodies_before t u hbytes (d + k) (by omega)

/-- All five staged layer records survive the body copies. In particular the
tail block can reload the original bounded counter words. -/
theorem packedBodies_stageAt (t u : MachineState)
    (hbytes : Expand.BytesEq u
      (Expand.applyCopies packedBodyCopies
        (fun a => t.getByte (BitVec.ofNat 64 a))))
    (l : Nat) (hl : l < 5) (ls : LayerSig) (h : StageAt t l ls) :
    StageAt u l ls := by
  obtain ⟨hcounter, hbound, hchain, hvals, hslots, hpath, hvals2, hslots2⟩ := h
  have hh := height_le l (by omega : l < 6)
  have hm : ∀ d, d % 8 = 0 → d + 8 ≤ 0x3b60 →
      u.getMem (BitVec.ofNat 64 d) = t.getMem (BitVec.ofNat 64 d) := by
    intro d hd hr
    exact packedBodies_stageWord t u hbytes d hd hr
  refine ⟨?_, hbound, hchain, hvals, ?_, hpath, hvals2, ?_⟩
  · rw [hm _ (by omega) (by omega), hcounter]
  · intro i hi
    rw [readWords_congr t u (0x900 + 856 * l + 8 + 16 * i) 2 (fun k hk =>
      hm _ (by omega) (by omega))]
    exact hslots i hi
  · intro i hi
    rw [readWords_congr t u (0x900 + 856 * l + 680 + 16 * i) 2 (fun k hk =>
      hm _ (by omega) (by omega))]
    exact hslots2 i hi

private theorem bodyLoopCodeAt_2892 : CodeAt image (pcOf 2892) Expand.loopCode := by
  simpa [seg2892, seg2892Packed, Expand.loopCode] using codeAt_2892
private theorem bodyLoopCodeAt_2903 : CodeAt image (pcOf 2903) Expand.loopCode := by
  simpa [seg2903, seg2903Packed, Expand.loopCode] using codeAt_2903
private theorem bodyLoopCodeAt_2914 : CodeAt image (pcOf 2914) Expand.loopCode := by
  simpa [seg2914, seg2914Packed, Expand.loopCode] using codeAt_2914
private theorem bodyLoopCodeAt_2925 : CodeAt image (pcOf 2925) Expand.loopCode := by
  simpa [seg2925, seg2925Packed, Expand.loopCode] using codeAt_2925
private theorem bodyLoopCodeAt_2936 : CodeAt image (pcOf 2936) Expand.loopCode := by
  simpa [seg2936, seg2936Packed, Expand.loopCode] using codeAt_2936

/-- A small symbolic setup and the previously proved polymorphic word-copy loop. -/
private theorem packedBodyStage {code : List (BitVec 32)} {i l e fuel : Nat}
    {r : Result} {src dst n : Nat}
    (hrun : symRun { noAlias := true } code (pcOf i) fuel = some r)
    (hcode : CodeAt image (pcOf i) code)
    (hmem : r.st.mem = []) (hobl : r.st.obl = [])
    (h6 : r.st.regs.get .x6 = .c (BitVec.ofNat 64 src))
    (h7 : r.st.regs.get .x7 = .c (BitVec.ofNat 64 dst))
    (h22 : r.st.regs.get .x22 = .c (BitVec.ofNat 64 n))
    (hpcl : r.pc = .c (pcOf l))
    (hloop : CodeAt image (pcOf l) Expand.loopCode)
    (hcond : 0 < n ∧ src % 4 = 0 ∧ dst % 4 = 0 ∧
      src + 4 * n ≤ 2 ^ 24 ∧ dst + 4 * n ≤ 2 ^ 24 ∧
      (src + 4 * n ≤ dst ∨ dst + 4 * n ≤ src))
    (hexit : pcOf l + 24 = pcOf e)
    (t : MachineState) (htpc : t.pc = pcOf i) (f : Nat → Byte)
    (hf : Expand.BytesEq t f) :
    ∃ u, Steps image t (r.steps + n * 6) (r.cycles + n * 6) u ∧
      u.pc = pcOf e ∧ Expand.BytesEq u (Expand.applyCopy (src, dst, n) f) := by
  obtain ⟨u, hsteps, hpc, hbytes⟩ :=
    Expand.stage hrun hcode hmem hobl h6 h7 h22 hpcl hloop hcond t htpc f hf
  exact ⟨u, hsteps, by rw [hpc, hexit], hbytes⟩

/-- The complete loop-based body phase. The tail pack starts at PC 2942. -/
theorem packedBodies_run (t : MachineState) (htpc : t.pc = pcOf 2887)
    (f : Nat → Byte) (hf : Expand.BytesEq t f) :
    ∃ u, Steps image t 5881 5881 u ∧ u.pc = pcOf 2942 ∧
      Expand.BytesEq u (Expand.applyCopies packedBodyCopies f) := by
  obtain ⟨u1, hs1, hp1, hb1⟩ := packedBodyStage (e := 2898) blk2887Packed codeAt_2887
    rfl rfl rfl rfl rfl rfl bodyLoopCodeAt_2892 (by decide) (by decide) t htpc f hf
  obtain ⟨u2, hs2, hp2, hb2⟩ := packedBodyStage (e := 2909) blk2898Packed codeAt_2898
    rfl rfl rfl rfl rfl rfl bodyLoopCodeAt_2903 (by decide) (by decide) u1 hp1 _ hb1
  obtain ⟨u3, hs3, hp3, hb3⟩ := packedBodyStage (e := 2920) blk2909Packed codeAt_2909
    rfl rfl rfl rfl rfl rfl bodyLoopCodeAt_2914 (by decide) (by decide) u2 hp2 _ hb2
  obtain ⟨u4, hs4, hp4, hb4⟩ := packedBodyStage (e := 2931) blk2920Packed codeAt_2920
    rfl rfl rfl rfl rfl rfl bodyLoopCodeAt_2925 (by decide) (by decide) u3 hp3 _ hb3
  obtain ⟨u5, hs5, hp5, hb5⟩ := packedBodyStage (e := 2942) blk2931Packed codeAt_2931
    rfl rfl rfl rfl rfl rfl bodyLoopCodeAt_2936 (by decide) (by decide) u4 hp4 _ hb4
  refine ⟨u5, ?_, hp5, ?_⟩
  · simpa only [show blk2887Packed.res.steps = 5 by kernel_rfl,
      show blk2898Packed.res.steps = 5 by kernel_rfl,
      show blk2909Packed.res.steps = 5 by kernel_rfl,
      show blk2920Packed.res.steps = 5 by kernel_rfl,
      show blk2931Packed.res.steps = 5 by kernel_rfl,
      show blk2887Packed.res.cycles = 5 by kernel_rfl,
      show blk2898Packed.res.cycles = 5 by kernel_rfl,
      show blk2909Packed.res.cycles = 5 by kernel_rfl,
      show blk2920Packed.res.cycles = 5 by kernel_rfl,
      show blk2931Packed.res.cycles = 5 by kernel_rfl,
      Nat.reduceAdd, Nat.reduceMul] using
      ((((hs1.trans hs2).trans hs3).trans hs4).trans hs5)
  · simpa [packedBodyCopies, Expand.applyCopies] using hb5

end SigGolfCandidate.Sign
