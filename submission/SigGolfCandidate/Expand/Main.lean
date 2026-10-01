import SigGolfCandidate.Expand.Init
import SigGolfCandidate.Expand.RefExpand
import SigGolfCandidate.Expand.Phase2

/-!
# `expand` refines `expandRef`

The program makes the digest query (the digest block at `DG = 0x20`, instructions 0 .. 13), runs
deterministically through the key extraction, sort, pass test, schedule, pad check and the partial
witness copies (phase 1, `phase1`: HALT(1) or `pors_init` = 495 with the partial witness in its
buffer), then phase 2 (`ExP.phase2_sim`: verify's PORS root on the partial witness, the counter
phase, the counters written into the witness, HALT).

Main results (namespace `SigGolfCandidate.Expand`):

* `expand_refines_counts` : value, calls, compressions of `submission.run .expand` =
  `countBoth (expandRef m pk σ)` (the `Budget.RefinesCounts` form, with `F = id`);
* `expand_refines` : value and calls = `countCalls (expandRef m pk σ)`;
* `expand_terminates` : every run under every oracle finishes in fewer than `2^32` cycles.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem
  OracleComp


theorem start_mem (s : MachineState) (a : Nat) (ha : a < 2 ^ 64) (h : 0x40 ≤ a) :
    (blk0.res.toState s).getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) := by
  have e : ∀ c : Nat, c < 64 → BitVec.ofNat 64 a ≠ BitVec.ofNat 64 c := by
    intro c hc; rw [Ne, ofNat_eq_iff]; omega
  simp only [blk0.res, rv_simp]
  simp [e 56 (by omega), e 48 (by omega), e 40 (by omega), e 32 (by omega)]

theorem start_hash (s : MachineState) (rho msg : List Byte) (hr : rho.length = 16) (hm : msg.length = 32)
    (hsig : s.readWords (BitVec.ofNat 64 0x24B00) 2 = wordsOf rho)
    (hmsg : s.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf msg) :
    hashInput (blk0.res.toState s) = addrFmt (digestInput rho msg) := by
  have h10 : (blk0.res.toState s).getReg .x10 = BitVec.ofNat 64 32 := by simp only [blk0.res, rv_simp]
  refine hashInput_eq_digest _ _ _ hr hm (by simp only [blk0.res, rv_simp]) (by rw [h10]; decide) ?_
  rw [h10, show 8 = 1 + 1 + 1 + 1 + 4 from rfl, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
    readWords_ofNat_add]
  simp only [Nat.reduceMul, Nat.reduceAdd, readWords_ofNat_one]
  have e : ∀ c : Nat, c < 64 → ∀ d : Nat, d < 64 → c ≠ d → BitVec.ofNat 64 c ≠ BitVec.ofNat 64 d := by
    intro c hc d hd hcd; rw [Ne, ofNat_eq_iff]; omega
  have g32 : (blk0.res.toState s).getMem (BitVec.ofNat 64 32) = BitVec.ofNat 64 3073 := by
    simp only [blk0.res, rv_simp]; simp [e 32 (by omega) 56 (by omega) (by omega),
      e 32 (by omega) 48 (by omega) (by omega), e 32 (by omega) 40 (by omega) (by omega)]
  have g40 : (blk0.res.toState s).getMem (BitVec.ofNat 64 40) = 0 := by
    simp only [blk0.res, rv_simp]; simp [e 40 (by omega) 56 (by omega) (by omega),
      e 40 (by omega) 48 (by omega) (by omega)]
  have g48 : (blk0.res.toState s).getMem (BitVec.ofNat 64 48) = s.getMem (BitVec.ofNat 64 0x24B00) := by
    simp only [blk0.res, rv_simp]; simp [e 48 (by omega) 56 (by omega) (by omega)]
  have g56 : (blk0.res.toState s).getMem (BitVec.ofNat 64 56) = s.getMem (BitVec.ofNat 64 0x24B08) := by
    simp only [blk0.res, rv_simp]; simp
  have w64 : (blk0.res.toState s).readWords (BitVec.ofNat 64 64) 4 = wordsOf msg := by
    rw [← hmsg]
    exact readWords_congr _ _ _ _ (fun i hi => (start_mem s _ (by omega) (by omega)))
  rw [readWords_ofNat_two] at hsig
  rw [g32, g40, g48, g56, w64, ← hsig]
  simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by unfold twWord0; rfl, rfl⟩



/-- The outcome of `expand` in the form `Sim.run_eq` needs. -/
def Qexp (r : Option (Bytes 16128)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
    r = if t.getReg .x10 = 0 then some (readBuffer t 0x900 16128) else none

theorem qexp_none (t : MachineState) (h : Final none t) : Qexp none t := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [if_neg h3]⟩

/-- Phase 1's outcome: a rejection (HALT(1)) or `pors_init` with the partial witness in the buffer. -/
def P1 (sig : List Byte) (N : Nat) (t : MachineState) : Prop :=
  (expandOf sig N = none ∧ Final none t) ∨
  (∃ (A : Nat → Nat) (segs : List Nat), expandOf sig N = some (witnessList sig (leavesOf N) (vsOf A) segs) ∧
    SortedKeys N A ∧ (leavesOf N).Nodup ∧ t.pc = pcOf 495 ∧ ArrOk t A ∧
    t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (N % 2 ^ 64) ∧
    ∀ i < 0x4000, t.getByte (BitVec.ofNat 64 (0x800 + i)) = (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0)

theorem extractLsb'_0_64 (a : BitVec 256) : a.extractLsb' 0 64 = BitVec.ofNat 64 (a.toNat % 2 ^ 64) := by
  unfold BitVec.extractLsb'; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- **Phase 1**: everything after the digest query up to `pors_init` (no queries). -/
theorem phase1 (ans : BitVec 256) (sig : List Byte) (hsig : sig.length = 6032) (s2 : MachineState)
    (hpc : s2.pc = pcOf 14) (hdo : DOk ans s2) (hsok : SigOK s2 sig)
    (hz : ∀ a, 0x800 ≤ a → a < 0x24B00 → s2.getByte (BitVec.ofNat 64 a) = 0) :
    Run s2 15000 (P1 sig ans.toNat) := by
  set N := ans.toNat with hN
  refine Run.seq (B₂ := 14666) (ext_run ans s2 hdo s2 hpc (Frame.refl _ _)) (fun t1 h1 => ?_) (by norm_num)
  refine Run.seq (B₂ := 13139) (sort_run ans s2 t1 h1) (fun t2 h2 => ?_) (by norm_num)
  obtain ⟨t2pc, ⟨A, hA, hF, hs⟩, hsent, hfr2⟩ := h2
  have hSK : SortedKeys N A := by
    refine ⟨?_, hF.lt, hs⟩
    refine List.Perm.trans (List.Perm.of_eq ?_) hF.perm
    apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp; simp [show p ≠ 15 by omega]
  -- bytes of t2 outside KEYS are those of s2
  have hb2 : ∀ a, a < 2 ^ 64 → ¬ (0x6E0 ≤ a ∧ a < 0x760) → t2.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := by
    intro a ha hk
    rw [getByte_ofNat _ _ ha, getByte_ofNat _ _ ha, hfr2 _ (by omega) (by unfold KW; omega)]
  refine Run.seq (B₂ := 12405) (pass_run A hSK.lt t2 t2pc hA) (fun t3 h3 => ?_) (by norm_num)
  by_cases hp : PassOK A
  · rw [if_pos hp] at h3
    obtain ⟨t3pc, t3m⟩ := h3
    have hpo := (passOK_iff hSK).mp hp
    have hv := vsOf_eq hSK
    have hleaves := leaves_vsOf hSK.sorted hSK.lt hp.1
    obtain ⟨hcr, hcs⟩ := schedule_counts hleaves (by simp [vsOf])
    have hoct : octopusSize (vsOf A) ≤ 117 := by rw [hv]; exact hpo.2
    have hb3 : ∀ a, a < 2 ^ 64 → ¬ (0x6E0 ≤ a ∧ a < 0x760) → t3.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := by
      intro a ha hk; rw [getByte_ofNat _ _ ha, t3m, ← getByte_ofNat _ _ ha]; exact hb2 a ha hk
    have hc : SchCtx A sig t3 := ⟨hA.frame t3m, hSK.lt, by rw [t3m]; exact hsent,
      fun j hj => by rw [hb3 _ (by omega) (by omega)]; exact hsok j hj, hsig⟩
    have hz3 : ∀ i < 2152, t3.getByte (BitVec.ofNat 64 (0x910 + i)) = 0 := by
      intro i hi; rw [hb3 _ (by omega) (by omega)]; exact hz _ (by omega) (by omega)
    have hsched := sch_run A sig t3 hc hp.1 t3pc hz3 (by rw [hcr]; exact hoct) (by rw [hcs]; simp [vsOf])
    refine Run.seq (B₂ := 7643) hsched (fun t4 h4 => ?_) (by norm_num)
    set F := (List.range 15).foldl (schedLeaf (vsOf A)) ⟨[], [], []⟩ with hFdef
    have hsch : schedule (vsOf A) = (F.segs, F.reads) := by
      unfold schedule; rw [show (vsOf A).length = 15 by simp [vsOf]]
    rw [hsch] at hcr hcs
    simp only at hcr hcs
    have hn : F.reads.length ≤ 117 := by rw [hcr]; exact hoct
    obtain ⟨t4pc, _, _, _, t4x29, _, _, _, _, _, t4str, t4ns, _, t4fr⟩ := h4
    rw [if_neg (by omega)] at t4pc
    refine Run.seq (B₂ := 6440) (pad_run sig t3 t4 hc.sigok t4fr t4pc F.reads.length hn t4x29)
      (fun t5 h5 => ?_) (by omega)
    have hall := all_iff_padOK sig hsig F.reads.length hn
    have hexp := expandOf_eq (sig := sig) hpo.1 hpo.2
    rw [← hv, hsch] at hexp
    simp only at hexp
    by_cases hpad : PadOK sig F.reads.length
    · obtain ⟨t5pc, t5m⟩ := h5.1 hpad
      rw [if_pos (hall.mpr hpad)] at hexp
      have hA5 : ArrOk t5 A := by
        intro p hp'
        rw [t5m, t4fr _ (by omega) (by unfold SW; omega)]; exact hc.arr p hp'
      -- bytes of t5 outside KEYS and the scheduler's writes are those of s2
      have hb5 : ∀ a, a < 2 ^ 64 → ¬ (0x6E0 ≤ a ∧ a < 0x7E0) → ¬ (0x910 ≤ a ∧ a < 0x910 + 2152) →
          t5.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := by
        intro a ha h1 h2
        rw [getByte_ofNat _ _ ha, t5m, t4fr _ (by omega) (by unfold SW; omega), ← getByte_ofNat _ _ ha,
          hb3 _ ha (by omega)]
      refine (copy_run A t5 t5pc hA5).mono (by norm_num) (fun t6 ⟨h61, h62⟩ => Or.inr ⟨A, F.segs, hexp, hSK, hpo.1,
        h61, ?_, ?_, ?_⟩)
      · intro p hp'
        rw [getMem_eq_of_bytes t5 t6 (0x6E0 + 8 * p) (by omega) (by omega) (fun k hk => by
          rw [h62 _ (by omega), copy_miss _ _ (by omega)]; unfold piF applyCopy; dsimp only
          rw [if_neg (by omega), if_neg (by omega)]), hA5 p hp']
      · rw [getMem_eq_of_bytes s2 t6 0x160 (by norm_num) (by norm_num) (fun k hk => by
          rw [h62 _ (by omega), copy_miss _ _ (by omega)]; unfold piF applyCopy; dsimp only
          rw [if_neg (by omega), if_neg (by omega), hb5 _ (by omega) (by omega) (by omega)])]
        have := hdo 0 (by norm_num)
        simp only [Nat.mul_zero, Nat.add_zero] at this
        rw [this, extractLsb'_0_64]
      · intro i hi
        rw [h62 _ (by omega)]
        have hsl : (segStream sig F.segs).length ≤ 2120 := by
          rw [length_segStream sig hsig F.segs (by omega), hcs]; simp [vsOf]; omega
        refine witness_bytes sig hsig N A hSK hpo.1 F.segs (fun a => t5.getByte (BitVec.ofNat 64 a))
          (fun j hj => ?_) (fun i hi => ?_) ?_ hsl (fun a h1 h2 => ?_) i hi
        · show t5.getByte _ = _
          rw [getByte_ofNat _ _ (by omega), t5m, ← getByte_ofNat _ _ (by omega)]
          rw [getByte_ofNat _ _ (by omega), t4fr _ (by omega) (by unfold SW; omega), ← getByte_ofNat _ _ (by omega)]
          exact hc.sigok j hj
        · show t5.getByte _ = _
          rw [getByte_ofNat _ _ (by omega), t5m, ← getByte_ofNat _ _ (by omega)]
          exact t4str i hi
        · intro a ha1 ha2
          show t5.getByte _ = _
          rw [hb5 _ (by omega) (by omega) (by omega)]
          exact hz _ ha1 (by omega)
        · show t5.getByte _ = _
          rw [hb5 _ (by omega) (by omega) (by omega)]
          exact hz _ (by omega) h2
    · have h5' := h5.2 hpad
      rw [if_neg (fun h => hpad (hall.mp h))] at hexp
      exact Run.done' (Or.inl ⟨hexp, h5'⟩)
  · rw [if_neg hp] at h3
    exact Run.done' (Or.inl ⟨expandOf_none (sig := sig) (fun h => hp ((passOK_iff hSK).mpr h)), h3⟩)

theorem Sim.of_run_bind {s : MachineState} {B W : Nat} {P : MachineState → Prop} {α : Type}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (h : Run s B P) (h2 : ∀ t, P t → Sign.Sim image t W oa Q) : Sign.Sim image s (B + W) oa Q := by
  obtain ⟨t, k, c, hst, hc, hP⟩ := h
  exact (Sign.Sim.steps hst (h2 t hP)).mono (by omega) (fun _ _ h => h)

/-- `expandList` after the digest. -/
def afterD (sig : List Byte) (N : Nat) : OracleComp HashSpec (Option (List Byte)) :=
  match expandOf sig N with
  | none => pure none
  | some w0 => ExP.afterW w0 (idxOf N) (leavesOf N)

/-- The leaf index the pi byte of slot `s` selects is `KEYS[s] >> 8`. -/
theorem x_lemma (sig : List Byte) (hsig : sig.length = 6032) (N : Nat) (A : Nat → Nat) (hSK : SortedKeys N A)
    (hn : (leavesOf N).Nodup) (segs : List Nat) :
    ∀ s < 15, (leavesOf N ++ [porsT]).getD (witPi (witnessList sig (leavesOf N) (vsOf A) segs) s / 8 % 16) 0 =
      A s / 256 := by
  intro s hs
  have hpi : (witnessList sig (leavesOf N) (vsOf A) segs).getD (wPi + s) 0 =
      byte (8 * (leavesOf N).idxOf (lv A s)) := by
    unfold witnessList witnessBody
    simp only [List.append_assoc]
    rw [getD_app, if_neg (show ¬ (wPi + s < (zeros wPi).length) by rw [length_zeros]; omega), length_zeros,
      getD_app, if_pos (by simp [vsOf]; omega)]
    rw [show wPi + s - wPi = s by omega, List.getD_eq_getElem?_getD, List.getElem?_map]
    simp [vsOf, hs]
  have hidx := idxOf_lv hSK hn s hs
  have hlt : (leavesOf N).idxOf (lv A s) < 15 := by
    have : A s % 256 < 256 := Nat.mod_lt _ (by norm_num)
    have hmem : lv A s ∈ leavesOf N := (vsOf_perm hSK).subset (by simp [vsOf]; exact ⟨s, hs, rfl⟩)
    have := List.idxOf_lt_length_of_mem hmem
    have hl : (leavesOf N).length = 15 := by simp [leavesOf, porsK]
    rw [hl] at this; exact this
  unfold witPi
  rw [hpi]
  have hb : (byte (8 * (leavesOf N).idxOf (lv A s))).toNat = 8 * (leavesOf N).idxOf (lv A s) := by
    unfold byte; rw [BitVec.toNat_ofNat]; omega
  rw [hb, show 8 * (leavesOf N).idxOf (lv A s) / 8 % 16 = (leavesOf N).idxOf (lv A s) by omega]
  have hmem : lv A s ∈ leavesOf N := (vsOf_perm hSK).subset (by simp [vsOf]; exact ⟨s, hs, rfl⟩)
  have hl : (leavesOf N).length = 15 := by simp [leavesOf, porsK]
  rw [List.getD_append _ _ _ _ (by rw [hl]; exact hlt), List.getD_eq_getElem _ _ (by rw [hl]; exact hlt),
    List.getElem_idxOf]
  rfl

theorem witMem_of_bytes (w : List Byte) (t : MachineState)
    (h : ∀ i < 0x4000, t.getByte (BitVec.ofNat 64 (0x800 + i)) = w.getD i 0) : ExP.WitMem w t := by
  intro k hk
  have := readWords_of_bytes t (0x800 + 8 * k) (wbytes w (8 * k) 8) 1 (ExP.length_wbytes _ _ _) (by omega)
    (by omega) (fun j hj => by
      rw [show 0x800 + 8 * k + j = 0x800 + (8 * k + j) by omega, h _ (by omega)]
      simp [wbytes, show j < 8 by omega])
  rw [readWords_ofNat_one, wordsOf_eight _ (ExP.length_wbytes _ _ _)] at this
  exact List.head_eq_of_cons_eq this

/-- Everything after the digest query. -/
theorem after_sim (ans : BitVec 256) (sig : List Byte) (hsig : sig.length = 6032) (s2 : MachineState)
    (hpc : s2.pc = pcOf 14) (hdo : DOk ans s2) (hsok : SigOK s2 sig)
    (hz : ∀ a, 0x800 ≤ a → a < 0x24B00 → s2.getByte (BitVec.ofNat 64 a) = 0) :
    Sign.Sim image s2 (15000 + (400000 + (34 + 5 * ExP.LW))) (afterD sig ans.toNat) ExP.QP := by
  refine Sim.of_run_bind (phase1 ans sig hsig s2 hpc hdo hsok hz) (fun t h => ?_)
  rcases h with ⟨hnone, hf⟩ | ⟨A, segs, hsome, hSK, hn, tpc, tA, t160, tb⟩
  · unfold afterD; rw [hnone]
    exact (Sign.Sim.pure (Q := ExP.QP) (a := none) ⟨hf.1, hf.2.1, by rw [if_neg hf.2.2]; rfl⟩).mono
      (by omega) (fun _ _ h => h)
  · unfold afterD; rw [hsome]
    have hlen := length_witnessList sig hsig (leavesOf ans.toNat) (vsOf A) segs (by simp [vsOf, porsK])
    exact ExP.phase2_sim _ hlen (witnessList_c4 sig hsig _ _ segs (by simp [vsOf])) A (leavesOf ans.toNat) ans.toNat t tpc t160 (witMem_of_bytes _ t tb) tA hSK.lt
      (x_lemma sig hsig ans.toNat A hSK hn segs)

/-- `expand` from a state that looks like its initial state. -/
theorem expand_sim (sig msg : List Byte) (hsig : sig.length = 6032) (hmsg : msg.length = 32)
    (s : MachineState) (hpc : s.pc = pcOf 0) (h5 : s.getReg .x5 = 0)
    (hrho : s.readWords (BitVec.ofNat 64 0x24B00) 2 = wordsOf (sigRho sig))
    (hm : s.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf msg) (hsok : SigOK s sig)
    (hz : ∀ a, 0x800 ≤ a → a < 0x24B00 → s.getByte (BitVec.ofNat 64 a) = 0) :
    Sign.Sim image s (13 + (8 + (15000 + (400000 + (34 + 5 * ExP.LW)) + 0)))
      ((liftM (HashSpec.query (addrFmt (digestInput (sigRho sig) msg))) : OracleComp HashSpec _) >>= fun a =>
        afterD sig a.toNat >>= fun r => pure (r.map fun l => ofList 16128 (cutW l))) Qexp := by
  have hr : (sigRho sig).length = 16 := by simp [sigRho, slice, hsig]
  have hst := symRun_sound blk0 codeAt_0 s hpc (by simp only [blk0.res, rv_simp])
  rw [show blk0.res.cycles = 13 by kernel_rfl] at hst
  refine Sign.Sim.steps hst ?_
  set s1 := blk0.res.toState s with hs1
  have e1 : fetch image s1 = some (.base .ECALL) :=
    symRun_ecall blk0 codeAt_0 s (by simp only [blk0.res, rv_simp]) rfl
  have x5 : s1.getReg .x5 = 0 := by simp only [hs1, blk0.res, rv_simp, h5]
  have x10 : s1.getReg .x10 = BitVec.ofNat 64 32 := by simp only [hs1, blk0.res, rv_simp]
  have x11 : s1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [hs1, blk0.res, rv_simp]
  have x12 : s1.getReg .x12 = BitVec.ofNat 64 352 := by simp only [hs1, blk0.res, rv_simp]
  have hv : hashArgumentsValid s1 = true :=
    hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hq := start_hash s (sigRho sig) msg hr hmsg hrho hm
  have hb : (addrFmt (digestInput (sigRho sig) msg)).blocks = 1 :=
    by rw [addrFmt_digestInput]; exact blocks_fmt_digest _ ⟨by simp [digestInput, thInput, hr, hmsg, length_tweak, P, zeros], rfl⟩
  have := Sign.Sim.query_bind (W := 15000 + (400000 + (34 + 5 * ExP.LW)) + 0)
    (f := fun a => afterD sig a.toNat >>= fun r => (pure (r.map fun l => ofList 16128 (cutW l)) : OracleComp HashSpec _))
    (Q := Qexp) e1 x5 hv hq (fun a => ?_)
  · rw [hb] at this; exact this
  set s2 := writeHash s1 a with hs2
  -- memory of `s2` above `0x40` outside `DO`
  have hmem : ∀ x : Nat, x < 2 ^ 64 → 0x40 ≤ x → (x < 0x160 ∨ 0x180 ≤ x) →
      s2.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x) := by
    intro x hx h1 h2
    rw [hs2, writeHash_getMem_frame s1 a 352 x x12 (by norm_num) hx (by omega), hs1, start_mem s x hx h1]
  have hbyte : ∀ x : Nat, x < 2 ^ 64 → 0x40 ≤ x → (x < 0x160 ∨ 0x180 ≤ x) →
      s2.getByte (BitVec.ofNat 64 x) = s.getByte (BitVec.ofNat 64 x) := by
    intro x hx h1 h2
    rw [getByte_ofNat _ _ hx, getByte_ofNat _ _ hx, hmem _ (by omega) (by omega) (by omega)]
  refine Sign.Sim.bind (W₂ := 0) (after_sim a sig hsig s2 ?_ ?_ ?_ ?_) (fun r t h => Sign.Sim.pure h)
  · rw [hs2, writeHash_pc, hs1]; simp only [blk0.res, rv_simp]; rfl
  · intro i hi
    rw [hs2, writeHash_getMem_ofNat s1 a 352 _ x12 (by norm_num) (by omega)]
    interval_cases i <;> simp
  · intro j hj; rw [hbyte _ (by omega) (by omega) (by omega)]; exact hsok j hj
  · intro x h1 h2; rw [hbyte _ (by omega) (by omega) (by omega)]; exact hz x h1 h2

theorem expandRef_eq (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    expandRef m pk σ = (liftM (HashSpec.query (addrFmt (digestInput (sigRho (toList σ)) (toList m)))) :
      OracleComp HashSpec _) >>= fun a => afterD (toList σ) a.toNat >>= fun r =>
        pure (r.map fun l => ofList 16128 (cutW l)) := by
  simp only [expandRef, expandList, digest, H, bind_assoc, pure_bind]
  rfl

theorem sI_words_sig (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    (sI m pk σ).readWords (BitVec.ofNat 64 0x24B00) 2 = wordsOf (sigRho (toList σ)) := by
  have hl : (toList σ).length = 6032 := by simp [toList, length_bytes]
  apply readWords_of_bytes _ _ _ _ (by simp [sigRho, slice, hl]) (by norm_num) (by norm_num)
  intro j hj
  rw [sI_getByte _ _ _ _ (by omega), if_pos (by omega), sigRho, getD_slice' _ _ _ _ (by omega)]
  simp [toList]

theorem sI_words_msg (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    (sI m pk σ).readWords (BitVec.ofNat 64 0x40) 4 = wordsOf (toList m) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, length_bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [sI_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp [toList]

/-- The cycle bound of `expand` (the five counter searches dominate). -/
def expandCyc : Nat := 13 + (8 + (15000 + (400000 + (34 + 5 * ExP.LW)) + 0))

theorem expandCyc_lt : expandCyc + 1 < CYCLE_LIMIT := by
  unfold expandCyc ExP.LW CYCLE_LIMIT; norm_num

theorem sim_sI (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    Sign.Sim image (sI m pk σ) expandCyc (expandRef m pk σ) Qexp := by
  rw [expandRef_eq]
  have hl : (toList σ).length = 6032 := by simp [toList, length_bytes]
  refine expand_sim (toList σ) (toList m) hl (by simp [toList, length_bytes]) (sI m pk σ) (sI_pc m pk σ)
    (sI_getReg m pk σ .x5 (by decide)) (sI_words_sig m pk σ) (sI_words_msg m pk σ) ?_ ?_
  · intro j hj; rw [sI_getByte _ _ _ _ (by omega), if_pos (by omega)]; simp [toList]
  · intro a h1 h2; rw [sI_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem qexp_halt (r : Option (Bytes 16128)) (t : MachineState) (h : Qexp r t) :
    fetch (submission.image .expand) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      id r = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout .expand t) else none :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- **expand refines `expandRef`** (value, oracle calls, compressions; the `Budget.RefinesCounts`
form with `F = id`). -/
theorem expand_refines_counts (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, σ) =
      (fun p => (p.1, p.2.1, p.2.2)) <$> Sign.countBoth (expandRef m pk σ) :=
  Sign.Sim.run_eq submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    (by have := expandCyc_lt; omega) id (fun a t h => qexp_halt a t h)

/-- **expand refines `expandRef`**: value and number of oracle calls. -/
theorem expand_refines (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (m, pk, σ) =
      (fun p => (p.1, p.2)) <$> countCalls (expandRef m pk σ) := by
  have h := congrArg (fun x => (fun t => (t.1, t.2.1)) <$> x) (expand_refines_counts m pk σ)
  simp only [Functor.map_map] at h
  rw [h, ← Sign.countBoth_calls]
  erw [Functor.map_map, Functor.map_map]
  rfl

/-- **expand terminates**: under every oracle, every run finishes in fewer than `2^32` cycles. -/
theorem expand_terminates (hash : Hash) (m : Message) (pk : PublicKey)
    (σ : Bytes 6032) :
    (submission.runWith hash .expand (m, pk, σ)).finished = true ∧
      (submission.runWith hash .expand (m, pk, σ)).cycles < CYCLE_LIMIT := by
  have := Sign.Sim.runWith submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    expandCyc_lt (fun a t h => ⟨h.1, h.2.1⟩) hash
  exact ⟨this.1, lt_of_le_of_lt this.2 (by have := expandCyc_lt; omega)⟩

/-- Every run (every oracle) takes at most `expandCyc + 1` cycles. -/
theorem expand_cycles_le (hash : Hash) (m : Message) (pk : PublicKey) (σ : Bytes 6032) :
    (submission.runWith hash .expand (m, pk, σ)).cycles ≤ expandCyc + 1 :=
  (Sign.Sim.runWith submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    expandCyc_lt (fun a t h => ⟨h.1, h.2.1⟩) hash).2

end SigGolfCandidate.Expand
