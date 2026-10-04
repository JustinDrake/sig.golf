import SigGolfCandidate.T3M.Search.TopAlu
import SigGolfCandidate.T3M.Search.TopTail

section

namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
abbrev foldRegs : List Reg := [.x25, .x28, .x29, .x30]
def rankPartial (v : Digest) : Nat → Nat
  | 0 => 0
  | n + 1 => rankPartial v n + rankLookup (topRank v n)
theorem rankPartial_seventeen (v : Digest) :
    rankPartial v 17 = ((rankDigits v).map rankLookup).sum := by
  simp only [rankPartial, rankDigits, List.range_succ, List.range_zero, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil]
  omega
theorem rankLoad_placement {image : Image} {b : Nat} (h : KernAt image b) (j : Fin 16) :
    CodeAt image (pcOf (b + rankStart (j.val + 1) + 2)) [0x000ece83] := by
  fin_cases j
  · exact codeAt_top273 h
  · exact codeAt_top278 h
  · exact codeAt_top283 h
  · exact codeAt_top288 h
  · exact codeAt_top293 h
  · exact codeAt_top298 h
  · exact codeAt_top303 h
  · exact codeAt_top308 h
  · exact codeAt_top315 h
  · exact codeAt_top320 h
  · exact codeAt_top325 h
  · exact codeAt_top330 h
  · exact codeAt_top335 h
  · exact codeAt_top340 h
  · exact codeAt_top345 h
  · exact codeAt_top350 h
theorem rankTail_placement {image : Image} {b : Nat} (h : KernAt image b) (j : Fin 16) :
    CodeAt image (pcOf (b + rankStart (j.val + 1) + 3)) rankTailCode := by
  fin_cases j
  · exact codeAt_top274 h
  · exact codeAt_top279 h
  · exact codeAt_top284 h
  · exact codeAt_top289 h
  · exact codeAt_top294 h
  · exact codeAt_top299 h
  · exact codeAt_top304 h
  · exact codeAt_top309 h
  · exact codeAt_top316 h
  · exact codeAt_top321 h
  · exact codeAt_top326 h
  · exact codeAt_top331 h
  · exact codeAt_top336 h
  · exact codeAt_top341 h
  · exact codeAt_top346 h
  · exact codeAt_top351 h
theorem rankStep_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (j : Fin 16) (s : MachineState) (v : Digest) (sum : Nat)
    (hpc : s.pc = pcOf (b + rankStart (j.val + 1)))
    (h28 : s.getReg .x28 = topWindow v (j.val + 1))
    (h25 : s.getReg .x25 = BitVec.ofNat 64 sum)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 TOP_DATA) (ht : SumTableOK s) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = pcOf (b + rankStart (j.val + 1) + 5) ∧
      t.getReg .x28 = topWindow v (j.val + 1) >>> 7 ∧
      t.getReg .x25 = BitVec.ofNat 64 (sum + rankLookup (topRank v (j.val + 1))) ∧
      RegsExcept s t [.x25,.x28,.x29] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, a1, r1, f1⟩ := rankPtr_spec s _
    (rankPtr_placement hK ⟨j.val + 1, by omega⟩) hpc v _ (by omega) h28 h30
  have hp1 : t1.pc = pcOf (b + rankStart (j.val + 1) + 2) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using p1
  obtain ⟨t2, e2, p2, a2, r2, f2⟩ := top_lbu_spec t1 _ 0x000ece83 .x29
    (rankLoad_placement hK j) hp1 (by rfl) (by decide) _ (topRank_lt v _)
    a1 (ht.frame f1 (by simp))
  have hp2 : t2.pc = pcOf (b + rankStart (j.val + 1) + 3) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using p2
  obtain ⟨t3, e3, p3, a3, b3, r3, f3⟩ := rankTail_spec t2 _
    (rankTail_placement hK j) hp2 (topWindow v (j.val + 1)) sum _
    (by rw [r2.get (by decide), r1.get (by decide), h28])
    (by rw [r2.get (by decide), r1.get (by decide), h25]) a2
  refine ⟨t3, (e1.trans e2).trans e3, ?_, a3, b3,
    ((r1.trans r2).trans r3).mono (by decide), ((f1.trans f2).trans f3).mono (by simp)⟩
  simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using p3
theorem topFold_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hpc : s.pc = pcOf (b + 265))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (ht : SumTableOK s) :
    ∃ t, Steps image s 88 88 t ∧ t.pc = pcOf (b + 353) ∧
      t.getReg .x28 = topWindow v 17 ∧
      t.getReg .x25 = BitVec.ofNat 64 (rankPartial v 17) ∧
      t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧ RegsExcept s t foldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨s0, e0, p0, w0, a0, r0, f0⟩ := topInit_spec s _ (codeAt_top265 hK) hpc v h6
  have hp0 : s0.pc = pcOf (b + 267) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using p0
  obtain ⟨u0, eu0, pu0, au0, ru0, fu0⟩ := rankPtr_spec s0 _ (codeAt_top267 hK) hp0 v 0 (by decide) w0 a0
  have hpu0 : u0.pc = pcOf (b + 269) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pu0
  obtain ⟨u1, eu1, pu1, au1, ru1, fu1⟩ := top_lbu_spec u0 _ 0x000ecc83 .x25
    (codeAt_top269 hK) hpu0 (by rfl) (by decide) _ (topRank_lt v _) au0
    (ht.frame (f0.trans fu0) (by simp))
  have hpu1 : u1.pc = pcOf (b + 270) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pu1
  obtain ⟨s1, es1, ps1, ws1, rs1, fs1⟩ := rankShift_spec u1 _ (codeAt_top270 hK) hpu1
    (topWindow v 0) (by rw [ru1.get (by decide), ru0.get (by decide), w0])
  have hpc1 : s1.pc = pcOf (b + rankStart 1) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using ps1
  have w1 : s1.getReg .x28 = topWindow v 1 := ws1.trans (topWindow_shift v 0 (by decide) (by decide))
  have a1 : s1.getReg .x25 = BitVec.ofNat 64 (rankPartial v 1) := by
    rw [rs1.get (by decide), au1]; simp [rankPartial]
  have r1 : RegsExcept s s1 foldRegs := (((r0.trans ru0).trans ru1).trans rs1).mono (by decide)
  have f1 : Frame s s1 (fun _ => False) := (((f0.trans fu0).trans fu1).trans fs1).mono (by simp)
  have x301 : s1.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rs1.get (by decide), ru1.get (by decide), ru0.get (by decide), a0]
  have e1 : Steps image s 6 6 s1 := ((e0.trans eu0).trans eu1).trans es1
  obtain ⟨q2, eq2, pq2, wq2, aq2, rq2, fq2⟩ := rankStep_spec hK ⟨0, by decide⟩ s1 v (rankPartial v 1)
    hpc1 w1 a1 x301
    (ht.frame f1 (by simp))
  let s2 := q2
  have hpc2 : s2.pc = pcOf (b + rankStart 2) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq2
  have w2 : s2.getReg .x28 = topWindow v 2 := wq2.trans (topWindow_shift v 1 (by decide) (by decide))
  have a2 : s2.getReg .x25 = BitVec.ofNat 64 (rankPartial v 2) := aq2
  have r2 : RegsExcept s s2 foldRegs := (r1.trans rq2).mono (by decide)
  have f2 : Frame s s2 (fun _ => False) := (f1.trans fq2).mono (by simp)
  have x302 : s2.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq2.get (by decide), x301]
  have e2 : Steps image s 11 11 s2 := e1.trans eq2
  obtain ⟨q3, eq3, pq3, wq3, aq3, rq3, fq3⟩ := rankStep_spec hK ⟨1, by decide⟩ s2 v (rankPartial v 2)
    hpc2 w2 a2 x302
    (ht.frame f2 (by simp))
  let s3 := q3
  have hpc3 : s3.pc = pcOf (b + rankStart 3) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq3
  have w3 : s3.getReg .x28 = topWindow v 3 := wq3.trans (topWindow_shift v 2 (by decide) (by decide))
  have a3 : s3.getReg .x25 = BitVec.ofNat 64 (rankPartial v 3) := aq3
  have r3 : RegsExcept s s3 foldRegs := (r2.trans rq3).mono (by decide)
  have f3 : Frame s s3 (fun _ => False) := (f2.trans fq3).mono (by simp)
  have x303 : s3.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq3.get (by decide), x302]
  have e3 : Steps image s 16 16 s3 := e2.trans eq3
  obtain ⟨q4, eq4, pq4, wq4, aq4, rq4, fq4⟩ := rankStep_spec hK ⟨2, by decide⟩ s3 v (rankPartial v 3)
    hpc3 w3 a3 x303
    (ht.frame f3 (by simp))
  let s4 := q4
  have hpc4 : s4.pc = pcOf (b + rankStart 4) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq4
  have w4 : s4.getReg .x28 = topWindow v 4 := wq4.trans (topWindow_shift v 3 (by decide) (by decide))
  have a4 : s4.getReg .x25 = BitVec.ofNat 64 (rankPartial v 4) := aq4
  have r4 : RegsExcept s s4 foldRegs := (r3.trans rq4).mono (by decide)
  have f4 : Frame s s4 (fun _ => False) := (f3.trans fq4).mono (by simp)
  have x304 : s4.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq4.get (by decide), x303]
  have e4 : Steps image s 21 21 s4 := e3.trans eq4
  obtain ⟨q5, eq5, pq5, wq5, aq5, rq5, fq5⟩ := rankStep_spec hK ⟨3, by decide⟩ s4 v (rankPartial v 4)
    hpc4 w4 a4 x304
    (ht.frame f4 (by simp))
  let s5 := q5
  have hpc5 : s5.pc = pcOf (b + rankStart 5) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq5
  have w5 : s5.getReg .x28 = topWindow v 5 := wq5.trans (topWindow_shift v 4 (by decide) (by decide))
  have a5 : s5.getReg .x25 = BitVec.ofNat 64 (rankPartial v 5) := aq5
  have r5 : RegsExcept s s5 foldRegs := (r4.trans rq5).mono (by decide)
  have f5 : Frame s s5 (fun _ => False) := (f4.trans fq5).mono (by simp)
  have x305 : s5.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq5.get (by decide), x304]
  have e5 : Steps image s 26 26 s5 := e4.trans eq5
  obtain ⟨q6, eq6, pq6, wq6, aq6, rq6, fq6⟩ := rankStep_spec hK ⟨4, by decide⟩ s5 v (rankPartial v 5)
    hpc5 w5 a5 x305
    (ht.frame f5 (by simp))
  let s6 := q6
  have hpc6 : s6.pc = pcOf (b + rankStart 6) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq6
  have w6 : s6.getReg .x28 = topWindow v 6 := wq6.trans (topWindow_shift v 5 (by decide) (by decide))
  have a6 : s6.getReg .x25 = BitVec.ofNat 64 (rankPartial v 6) := aq6
  have r6 : RegsExcept s s6 foldRegs := (r5.trans rq6).mono (by decide)
  have f6 : Frame s s6 (fun _ => False) := (f5.trans fq6).mono (by simp)
  have x306 : s6.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq6.get (by decide), x305]
  have e6 : Steps image s 31 31 s6 := e5.trans eq6
  obtain ⟨q7, eq7, pq7, wq7, aq7, rq7, fq7⟩ := rankStep_spec hK ⟨5, by decide⟩ s6 v (rankPartial v 6)
    hpc6 w6 a6 x306
    (ht.frame f6 (by simp))
  let s7 := q7
  have hpc7 : s7.pc = pcOf (b + rankStart 7) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq7
  have w7 : s7.getReg .x28 = topWindow v 7 := wq7.trans (topWindow_shift v 6 (by decide) (by decide))
  have a7 : s7.getReg .x25 = BitVec.ofNat 64 (rankPartial v 7) := aq7
  have r7 : RegsExcept s s7 foldRegs := (r6.trans rq7).mono (by decide)
  have f7 : Frame s s7 (fun _ => False) := (f6.trans fq7).mono (by simp)
  have x307 : s7.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq7.get (by decide), x306]
  have e7 : Steps image s 36 36 s7 := e6.trans eq7
  obtain ⟨q8, eq8, pq8, wq8, aq8, rq8, fq8⟩ := rankStep_spec hK ⟨6, by decide⟩ s7 v (rankPartial v 7)
    hpc7 w7 a7 x307
    (ht.frame f7 (by simp))
  let s8 := q8
  have hpc8 : s8.pc = pcOf (b + rankStart 8) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq8
  have w8 : s8.getReg .x28 = topWindow v 8 := wq8.trans (topWindow_shift v 7 (by decide) (by decide))
  have a8 : s8.getReg .x25 = BitVec.ofNat 64 (rankPartial v 8) := aq8
  have r8 : RegsExcept s s8 foldRegs := (r7.trans rq8).mono (by decide)
  have f8 : Frame s s8 (fun _ => False) := (f7.trans fq8).mono (by simp)
  have x308 : s8.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq8.get (by decide), x307]
  have e8 : Steps image s 41 41 s8 := e7.trans eq8
  obtain ⟨q9, eq9, pq9, wq9, aq9, rq9, fq9⟩ := rankStep_spec hK ⟨7, by decide⟩ s8 v (rankPartial v 8)
    hpc8 w8 a8 x308
    (ht.frame f8 (by simp))
  have hpq9 : q9.pc = pcOf (b + 311) := by simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq9
  obtain ⟨s9, ec9, pc9, w9, rc9, fc9⟩ := rankCross_spec q9 _ (codeAt_top311 hK) hpq9 v
    (by simpa [topWindow, ← BitVec.shiftRight_add] using wq9)
    (by rw [rq9.get (by decide), r8.get (by decide), h7])
  have hpc9 : s9.pc = pcOf (b + rankStart 9) := by
    simpa only [pcOf_add4, rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pc9
  have a9 : s9.getReg .x25 = BitVec.ofNat 64 (rankPartial v 9) := by
    rw [rc9.get (by decide), aq9]; rfl
  have r9 : RegsExcept s s9 foldRegs := ((r8.trans rq9).trans rc9).mono (by decide)
  have f9 : Frame s s9 (fun _ => False) := ((f8.trans fq9).trans fc9).mono (by simp)
  have x309 : s9.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rc9.get (by decide), rq9.get (by decide), x308]
  have e9 : Steps image s 48 48 s9 := (e8.trans eq9).trans ec9
  obtain ⟨q10, eq10, pq10, wq10, aq10, rq10, fq10⟩ := rankStep_spec hK ⟨8, by decide⟩ s9 v (rankPartial v 9)
    hpc9 w9 a9 x309
    (ht.frame f9 (by simp))
  let s10 := q10
  have hpc10 : s10.pc = pcOf (b + rankStart 10) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq10
  have w10 : s10.getReg .x28 = topWindow v 10 := wq10.trans (topWindow_shift v 9 (by decide) (by decide))
  have a10 : s10.getReg .x25 = BitVec.ofNat 64 (rankPartial v 10) := aq10
  have r10 : RegsExcept s s10 foldRegs := (r9.trans rq10).mono (by decide)
  have f10 : Frame s s10 (fun _ => False) := (f9.trans fq10).mono (by simp)
  have x3010 : s10.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq10.get (by decide), x309]
  have e10 : Steps image s 53 53 s10 := e9.trans eq10
  obtain ⟨q11, eq11, pq11, wq11, aq11, rq11, fq11⟩ := rankStep_spec hK ⟨9, by decide⟩ s10 v (rankPartial v 10)
    hpc10 w10 a10 x3010
    (ht.frame f10 (by simp))
  let s11 := q11
  have hpc11 : s11.pc = pcOf (b + rankStart 11) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq11
  have w11 : s11.getReg .x28 = topWindow v 11 := wq11.trans (topWindow_shift v 10 (by decide) (by decide))
  have a11 : s11.getReg .x25 = BitVec.ofNat 64 (rankPartial v 11) := aq11
  have r11 : RegsExcept s s11 foldRegs := (r10.trans rq11).mono (by decide)
  have f11 : Frame s s11 (fun _ => False) := (f10.trans fq11).mono (by simp)
  have x3011 : s11.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq11.get (by decide), x3010]
  have e11 : Steps image s 58 58 s11 := e10.trans eq11
  obtain ⟨q12, eq12, pq12, wq12, aq12, rq12, fq12⟩ := rankStep_spec hK ⟨10, by decide⟩ s11 v (rankPartial v 11)
    hpc11 w11 a11 x3011
    (ht.frame f11 (by simp))
  let s12 := q12
  have hpc12 : s12.pc = pcOf (b + rankStart 12) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq12
  have w12 : s12.getReg .x28 = topWindow v 12 := wq12.trans (topWindow_shift v 11 (by decide) (by decide))
  have a12 : s12.getReg .x25 = BitVec.ofNat 64 (rankPartial v 12) := aq12
  have r12 : RegsExcept s s12 foldRegs := (r11.trans rq12).mono (by decide)
  have f12 : Frame s s12 (fun _ => False) := (f11.trans fq12).mono (by simp)
  have x3012 : s12.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq12.get (by decide), x3011]
  have e12 : Steps image s 63 63 s12 := e11.trans eq12
  obtain ⟨q13, eq13, pq13, wq13, aq13, rq13, fq13⟩ := rankStep_spec hK ⟨11, by decide⟩ s12 v (rankPartial v 12)
    hpc12 w12 a12 x3012
    (ht.frame f12 (by simp))
  let s13 := q13
  have hpc13 : s13.pc = pcOf (b + rankStart 13) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq13
  have w13 : s13.getReg .x28 = topWindow v 13 := wq13.trans (topWindow_shift v 12 (by decide) (by decide))
  have a13 : s13.getReg .x25 = BitVec.ofNat 64 (rankPartial v 13) := aq13
  have r13 : RegsExcept s s13 foldRegs := (r12.trans rq13).mono (by decide)
  have f13 : Frame s s13 (fun _ => False) := (f12.trans fq13).mono (by simp)
  have x3013 : s13.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq13.get (by decide), x3012]
  have e13 : Steps image s 68 68 s13 := e12.trans eq13
  obtain ⟨q14, eq14, pq14, wq14, aq14, rq14, fq14⟩ := rankStep_spec hK ⟨12, by decide⟩ s13 v (rankPartial v 13)
    hpc13 w13 a13 x3013
    (ht.frame f13 (by simp))
  let s14 := q14
  have hpc14 : s14.pc = pcOf (b + rankStart 14) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq14
  have w14 : s14.getReg .x28 = topWindow v 14 := wq14.trans (topWindow_shift v 13 (by decide) (by decide))
  have a14 : s14.getReg .x25 = BitVec.ofNat 64 (rankPartial v 14) := aq14
  have r14 : RegsExcept s s14 foldRegs := (r13.trans rq14).mono (by decide)
  have f14 : Frame s s14 (fun _ => False) := (f13.trans fq14).mono (by simp)
  have x3014 : s14.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq14.get (by decide), x3013]
  have e14 : Steps image s 73 73 s14 := e13.trans eq14
  obtain ⟨q15, eq15, pq15, wq15, aq15, rq15, fq15⟩ := rankStep_spec hK ⟨13, by decide⟩ s14 v (rankPartial v 14)
    hpc14 w14 a14 x3014
    (ht.frame f14 (by simp))
  let s15 := q15
  have hpc15 : s15.pc = pcOf (b + rankStart 15) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq15
  have w15 : s15.getReg .x28 = topWindow v 15 := wq15.trans (topWindow_shift v 14 (by decide) (by decide))
  have a15 : s15.getReg .x25 = BitVec.ofNat 64 (rankPartial v 15) := aq15
  have r15 : RegsExcept s s15 foldRegs := (r14.trans rq15).mono (by decide)
  have f15 : Frame s s15 (fun _ => False) := (f14.trans fq15).mono (by simp)
  have x3015 : s15.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq15.get (by decide), x3014]
  have e15 : Steps image s 78 78 s15 := e14.trans eq15
  obtain ⟨q16, eq16, pq16, wq16, aq16, rq16, fq16⟩ := rankStep_spec hK ⟨14, by decide⟩ s15 v (rankPartial v 15)
    hpc15 w15 a15 x3015
    (ht.frame f15 (by simp))
  let s16 := q16
  have hpc16 : s16.pc = pcOf (b + rankStart 16) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq16
  have w16 : s16.getReg .x28 = topWindow v 16 := wq16.trans (topWindow_shift v 15 (by decide) (by decide))
  have a16 : s16.getReg .x25 = BitVec.ofNat 64 (rankPartial v 16) := aq16
  have r16 : RegsExcept s s16 foldRegs := (r15.trans rq16).mono (by decide)
  have f16 : Frame s s16 (fun _ => False) := (f15.trans fq16).mono (by simp)
  have x3016 : s16.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq16.get (by decide), x3015]
  have e16 : Steps image s 83 83 s16 := e15.trans eq16
  obtain ⟨q17, eq17, pq17, wq17, aq17, rq17, fq17⟩ := rankStep_spec hK ⟨15, by decide⟩ s16 v (rankPartial v 16)
    hpc16 w16 a16 x3016
    (ht.frame f16 (by simp))
  let s17 := q17
  have hpc17 : s17.pc = pcOf (b + 353) := by
    simpa only [rankStart, Nat.add_assoc, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT, Nat.reduceEqDiff, ↓reduceIte] using pq17
  have w17 : s17.getReg .x28 = topWindow v 17 := wq17.trans (topWindow_shift v 16 (by decide) (by decide))
  have a17 : s17.getReg .x25 = BitVec.ofNat 64 (rankPartial v 17) := aq17
  have r17 : RegsExcept s s17 foldRegs := (r16.trans rq17).mono (by decide)
  have f17 : Frame s s17 (fun _ => False) := (f16.trans fq17).mono (by simp)
  have x3017 : s17.getReg .x30 = BitVec.ofNat 64 TOP_DATA := by
    rw [rq17.get (by decide), x3016]
  have e17 : Steps image s 88 88 s17 := e16.trans eq17
  exact ⟨s17, e17, hpc17, w17, a17, x3017, r17, f17⟩
end SigGolfCandidate.T3M.Search
end

section


namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest)
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false
theorem rankPartial_le (v : Digest) (n : Nat) : rankPartial v n ≤ 255 * n := by
  induction n with
  | zero => simp [rankPartial]
  | succ n ih =>
    rw [rankPartial]
    have := rankLookup_le (topRank v n)
    omega
theorem topCheck_spec {image : Image} {b : Nat} (hK : KernAt image b)
    (s : MachineState) (v : Digest) (hv : v.toNat < 2 ^ 125)
    (hpc : s.pc = pcOf (b + 265))
    (h6 : s.getReg .x6 = v.extractLsb' 0 64) (h7 : s.getReg .x7 = v.extractLsb' 64 64)
    (h17 : s.getReg .x17 = 126#64) (ht : SumTableOK s) :
    ∃ t, Steps image s 97 97 t ∧
      t.pc = (if topLookupSum v = 126 then pcOf (b + 362) else pcOf (b + 468)) ∧
      t.getReg .x25 = BitVec.ofNat 64 (topLookupSum v) ∧
      t.getReg .x30 = BitVec.ofNat 64 TOP_DATA ∧
      RegsExcept s t foldRegs ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, e1, p1, w1, a1, x301, r1, f1⟩ := topFold_spec hK s v hpc h6 h7 ht
  obtain ⟨t2, e2, p2, a2, r2, f2⟩ := topTail_spec hK t1 v (rankPartial v 17)
    (rankPartial_le v 17) hv p1 w1 a1 (by rw [r1.get (by decide), h17])
  have he : rankPartial v 17 + tailWeight v = topLookupSum v := by
    rw [rankPartial_seventeen]; rfl
  refine ⟨t2, e1.trans e2, ?_, ?_, ?_, (r1.trans r2).mono (by decide),
    (f1.trans f2).mono (by simp)⟩
  · simpa only [he] using p2
  · simpa only [he] using a2
  · rw [r2.get (by decide), x301]
end SigGolfCandidate.T3M.Search
end
