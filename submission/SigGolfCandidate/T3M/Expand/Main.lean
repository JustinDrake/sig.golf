import SigGolfCandidate.T3M.Expand.Run
import SigGolfCandidate.T3M.Expand.FtsMain
import SigGolfCandidate.T3M.Submission

/-!
# Expand: the whole phase (stream E)

Given the FTS phase (`FtsSpec 0`, proved as `ftsSpec` in `Expand/FtsMain`; the unconditional forms are
`expand_refines_holds` / `expand_terminates_holds`):
* `expand_refines` : value, calls and compressions of `submission.run .expand (m, pk, s)` are those of
  `countBoth (mrealize 0 (expandN m pk (sigDec s)))`, the value mapped by `witEnc` (the shape of
  `Final/Pending`'s `ExpandRefines`);
* `expand_terminates` : under every fixed oracle the run finishes within `expCost + 1 < 2^32` cycles
  (`ExpandTerminates`).
-/

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (HashOutput Witness)
open SigGolfCandidate.T3M.Search (FailedAt kernAt_expand codeAt_k_2)

set_option autoImplicit false

set_option maxRecDepth 100000 in
theorem initialState_expand (m : Message) (pk : PublicKey) (σ : Bytes 5824) :
    initialState submission .expand (m, pk, σ) = some (einit m pk σ) := by
  have hv := submission_expand_valid
  unfold initialState
  rw [if_pos hv]
  simp only [submission_expand, Images.expandImage, Images.expandData, MachineState.writeBytesAsWords_nil,
    inputBuffers, List.foldl_cons, List.foldl_nil]
  rfl

theorem lcost_four : lcost 4 = 2831201263 := by decide

theorem expCost_lt : expCost + 1 < CYCLE_LIMIT := by
  have h := lcost_four
  unfold expCost ftsCost CYCLE_LIMIT
  omega

theorem witList_length (N : HashOutput) (w : Witness) : (witList N w).length = 8 * 3155 := by
  obtain ⟨l1, l2, l3⟩ := witList_length_parts N w
  have l4 := fun lay : T3.Layer => layerBytes_length lay (T3.route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)
  have hf : (List.finRange 4).flatMap (fun lay : T3.Layer =>
      layerBytes lay (T3.route (N.toNat % 2 ^ 31) lay).1 (w.signature.layers lay)) =
      layerBytes 0 (T3.route (N.toNat % 2 ^ 31) 0).1 (w.signature.layers 0) ++
      layerBytes 1 (T3.route (N.toNat % 2 ^ 31) 1).1 (w.signature.layers 1) ++
      layerBytes 2 (T3.route (N.toNat % 2 ^ 31) 2).1 (w.signature.layers 2) ++
      layerBytes 3 (T3.route (N.toNat % 2 ^ 31) 3).1 (w.signature.layers 3) := by
    simp only [List.finRange_succ, List.finRange_zero, List.flatMap_cons, List.flatMap_nil, List.map_cons,
      List.map_nil, List.append_nil, List.append_assoc]
    rfl
  unfold witList
  rw [hf]
  simp only [List.length_append, l1, l2, l3, l4]
  rfl

/-- The witness at `accept`. -/
theorem expq_output {N : HashOutput} {w : Witness} {t : MachineState}
    (h : t.readWords (BitVec.ofNat 64 0x800) 3155 = wordsOf (witList N w)) :
    readOutput submission.sizes submission.layout .expand t = witEnc N w :=
  readBuffer_of_words t 0x800 3155 (witList N w) (by decide) (by decide) (witList_length N w) h

/-- The final states: at a `HALT` `ECALL` with `t0 = 1`; `a0 = 0` and the witness iff accepted. -/
theorem expq_halt (a : Option (HashOutput × Witness)) (t : MachineState) (h : ExpQ a t) :
    fetch (submission.image .expand) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      (a.map fun x => witEnc x.1 x.2) =
        (if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout .expand t) else none) := by
  rcases a with _ | ⟨N, w⟩
  · obtain ⟨p, x5, x10⟩ := h
    refine ⟨((codeAt_k_2 kernAt_expand).fetch t p).trans rfl, x5, ?_⟩
    rw [x10]; rfl
  · obtain ⟨p, x5, x10, hw⟩ := h
    refine ⟨(codeAt_353.fetch t p).trans rfl, x5, ?_⟩
    rw [x10, if_pos (show (0#64 : BitVec 64) = 0 from rfl), expq_output hw]; rfl

/-- **Expand refinement** (given the FTS phase): value (the witness bytes `witEnc N w`), calls and compressions
of the run are those of `expandN` (Core's `expand` returning the accepted digest answer), for every input. -/
theorem expand_refines (hF : FtsSpec 0) (m : Message) (pk : PublicKey) (s : Bytes 5824) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, s) =
      (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize 0 (expandN m pk (sigDec s))) := by
  have hsim : Sim (submission.image .expand) (einit m pk s) expCost (mrealize 0 (expandN m pk (sigDec s))) ExpQ := by
    rw [submission_expand]
    exact expand_tbsim hF m pk s
  have hW : expCost < CYCLE_LIMIT := Nat.lt_of_succ_lt expCost_lt
  have key := Sim.run_eq submission .expand (m, pk, s) (initialState_expand m pk s) hsim hW _ expq_halt
  exact key

/-- **Expand termination** (given the FTS phase): under every fixed oracle the run finishes within
`expCost + 1 < 2^32` cycles. -/
theorem expand_terminates (hF : FtsSpec 0) (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5824) :
    (submission.runWith hash .expand (m, pk, s)).finished = true ∧
      (submission.runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT := by
  have hsim : Sim (submission.image .expand) (einit m pk s) expCost (mrealize 0 (expandN m pk (sigDec s))) ExpQ :=
    expand_tbsim hF m pk s
  obtain ⟨h1, h2⟩ := Sim.runWith submission .expand (m, pk, s) (initialState_expand m pk s)
    hsim expCost_lt (fun a t h => ⟨(expq_halt a t h).1, (expq_halt a t h).2.1⟩) hash
  exact ⟨h1, lt_of_le_of_lt h2 expCost_lt⟩

/-- **Expand refinement**, unconditional: the statement of `Final/Pending`'s `ExpandRefines`. -/
theorem expand_refines_holds : ∀ (m : Message) (pk : PublicKey) (s : Bytes 5824),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, s) =
      (fun p => (p.1.map (fun x => witEnc x.1 x.2), p.2.1, p.2.2)) <$>
        countBoth (mrealize 0 (expandN m pk (sigDec s))) :=
  expand_refines (ftsSpec 0)

/-- **Expand termination**, unconditional: the statement of `Final/Pending`'s `ExpandTerminates`. -/
theorem expand_terminates_holds : ∀ (hash : Hash) (m : Message) (pk : PublicKey) (s : Bytes 5824),
    (submission.runWith hash .expand (m, pk, s)).finished = true ∧
      (submission.runWith hash .expand (m, pk, s)).cycles < CYCLE_LIMIT :=
  expand_terminates (ftsSpec 0)

end SigGolfCandidate.T3M.Expand
