import SigGolfCandidate.T3.Secc.LargeContactWalk
import SigGolfCandidate.T3.Secc.PairGuessFinal

/-!
# LR-34 (certificate coupling): the verifier's leaf queries in case (C)

Local copy (stream CC, `/projects/golf/sig-t3-secc-c/proofs/CaseCLeaf.lean`, authoritative) of the leaf-query lemmas
`recoverChildP_leaf_queried`, `selLeaf_facts`, `recoverFtsP_leaf_queried`, `verifyP_fts_run`, and
`verifyP_leaf_queried` (CC's `verdict_leaf_entries` stated on the verification's own queries), in the namespace
`LargeCoupling.CertLeaf`. Imports trimmed to modules of this workspace.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling.CertLeaf
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- The leaf query of `recoverChildP` at a selected leaf `g`. -/
def leafQuery (index coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads) (g : Nat) :
    T3.Spec.Domain :=
  .inl (.inr (ftsLeafInputP index coord g
    (pads.leaf ⟨(3 * coord + leaves.idxOf g) % 22, Nat.mod_lt _ (by decide)⟩)
    (values.getD (leaves.idxOf g) 0)
    (pads.leaf ⟨(3 * coord + leaves.idxOf g + 1) % 22, Nat.mod_lt _ (by decide)⟩)))

/-- **A returning subtree run queried every selected leaf below it.** -/
theorem recoverChildP_leaf_queried (answers : Correctness.Answers) (index coord : Nat) (leaves : List Nat)
    (values : List Digest) (proof : Fin 118 → Digest) (pads : Pads) :
    ∀ level node used (v : Digest) (next : Nat),
      evalWithAnswerFn answers (recoverChildP index coord leaves values proof pads level node used) =
        some (v, next) →
      ∀ g ∈ leaves, node * 2 ^ level ≤ g → g < (node + 1) * 2 ^ level →
        leafQuery index coord leaves values pads g ∈
          queried answers (recoverChildP index coord leaves values proof pads level node used) := by
  intro level
  induction level with
  | zero =>
      intro node used v next hrun g hg h0 h1
      by_cases hh : hasLeaf leaves 0 node = true
      · have hprog : recoverChildP index coord leaves values proof pads 0 node used =
            (shortHash (ftsLeafInputP index coord node
              (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
              (values.getD (leaves.idxOf node) 0)
              (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩)) >>=
              fun value => pure (some (value, used))) := by
          simp only [recoverChildP, hh, Bool.not_true, Bool.false_eq_true, if_false]; rfl
        have hgn : g = node := by simp at h0 h1; omega
        subst hgn
        rw [hprog, queried_bind, queried_shortHash, pad64_ftsLeafInputP, queried_pure, List.append_nil]
        exact List.mem_singleton_self _
      · have hh : hasLeaf leaves 0 node = false := by simpa using hh
        exact (FtsExtract.hasLeaf_false hh hg h0 h1).elim
  | succ level ih =>
      intro node used v next hrun g hg h0 h1
      by_cases hh : hasLeaf leaves (level + 1) node = true
      · rw [recoverChildP] at hrun ⊢
        simp only [hh, Bool.not_true, Bool.false_eq_true, if_false] at hrun ⊢
        rw [queried_bind]
        rw [evalWithAnswerFn_bind] at hrun
        rcases hr1 : evalWithAnswerFn answers (recoverChildP index coord leaves values proof pads level (2 * node) used)
          with _ | ⟨left, n1⟩
        · rw [hr1] at hrun; simp at hrun
        try rw [hr1] at hrun
        dsimp only at hrun ⊢
        rw [queried_bind]
        rw [evalWithAnswerFn_bind] at hrun
        rcases hr2 : evalWithAnswerFn answers
            (recoverChildP index coord leaves values proof pads level (2 * node + 1) n1) with _ | ⟨right, n2⟩
        · rw [hr2] at hrun; simp at hrun
        have e0 : node * 2 ^ (level + 1) = 2 * node * 2 ^ level := by rw [pow_succ]; ring
        have e1 : (node + 1) * 2 ^ (level + 1) = (2 * node + 1 + 1) * 2 ^ level := by rw [pow_succ]; ring
        have e2 : (2 * node + 1) * 2 ^ level = 2 * node * 2 ^ level + 2 ^ level := by ring
        by_cases hlo : g < (2 * node + 1) * 2 ^ level
        · exact List.mem_append_left _ (ih (2 * node) used left n1 hr1 g hg (by omega) hlo)
        · exact List.mem_append_right _ (List.mem_append_left _
            (ih (2 * node + 1) n1 right n2 hr2 g hg (by omega) (by omega)))
      · have hh : hasLeaf leaves (level + 1) node = false := by simpa using hh
        exact (FtsExtract.hasLeaf_false hh hg h0 h1).elim

/-- Position facts of the `j`-th selected leaf of a machine-accepted selection. -/
theorem selLeaf_facts (sel : Selection) (hs : SelOk sel) (j : Nat) (hj : j < 3) :
    (selectedLeaves sel).idxOf (selLeaf sel j) = j ∧ selLeaf sel j ∈ selectedLeaves sel ∧
      sel.bucket * 2 ^ 7 ≤ selLeaf sel j ∧ selLeaf sel j < (sel.bucket + 1) * 2 ^ 7 := by
  have hsel := hs.selected
  have h01 := hs.s01
  have h12 := hs.s12
  have h2 := hs.l2
  have e0 : selLeaf sel 0 = sel.bucket * 128 + sel.leaves.getD 0 0 := rfl
  have e1 : selLeaf sel 1 = sel.bucket * 128 + sel.leaves.getD 1 0 := rfl
  have e2 : selLeaf sel 2 = sel.bucket * 128 + sel.leaves.getD 2 0 := rfl
  generalize sel.leaves.getD 0 0 = x0 at h01 e0
  generalize sel.leaves.getD 1 0 = x1 at h01 h12 e1
  generalize sel.leaves.getD 2 0 = x2 at h12 h2 e2
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsel, e0, e1, e2]
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2]
    · exact List.idxOf_cons_self
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
  · rw [hsel]
    rcases hj3 with rfl | rfl | rfl <;> simp
  · rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega
  · rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega

/-- **A returning padded FTS run queried the leaf of every selected position.** -/
theorem recoverFtsP_leaf_queried (answers : Correctness.Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (v : Digest) (hc : ChosenOk chosen)
    (hrun : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some v) :
    ∀ c < 7, ∀ j < 3,
      (.inl (.inr (ftsLeafInputP index c (selLeaf (chosen.getD c ⟨0, []⟩) j)
        (pads.leaf ⟨(3 * c + j) % 22, Nat.mod_lt _ (by decide)⟩)
        (sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
        (pads.leaf ⟨(3 * c + j + 1) % 22, Nat.mod_lt _ (by decide)⟩))) : T3.Spec.Domain) ∈
      queried answers (recoverFtsP sig pads index chosen) := by
  intro c hc7 j hj
  rw [recoverFtsP_eq] at hrun ⊢
  rw [queried_bind]
  rw [evalWithAnswerFn_bind] at hrun
  rcases hs : evalWithAnswerFn answers ((List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0)))
    with _ | ⟨roots, used⟩
  · rw [hs] at hrun; simp at hrun
  apply List.mem_append_left
  obtain ⟨-, us, -, hsteps, hq⟩ := FtsExtract.ftsFold_runs answers sig pads index chosen (fun _ _ => 0) 7 roots used
    (fun c' hc' => (hc c' hc').b) hs
  rw [hq]
  apply List.mem_flatMap.mpr
  refine ⟨c, List.mem_range.mpr hc7, ?_⟩
  have hstep := hsteps c hc7
  rw [ftsStepP_some] at hstep ⊢
  rw [evalWithAnswerFn_bind] at hstep
  rw [queried_bind]
  apply List.mem_append_left
  rcases h1 : evalWithAnswerFn answers (recoverChildP index c (selectedLeaves (chosen.getD c ⟨0, []⟩))
      (FtsExtract.coordValues sig c) sig.proof pads 7 (chosen.getD c ⟨0, []⟩).bucket (us c)) with _ | ⟨value, next⟩
  · simp only [FtsExtract.coordValues] at h1; rw [h1] at hstep; simp at hstep
  obtain ⟨hidx, hmem, hlo, hhi⟩ := selLeaf_facts _ (hc c hc7) j hj
  have hq1 := recoverChildP_leaf_queried answers index c _ _ sig.proof pads 7 _ (us c) value next h1 _ hmem hlo hhi
  simp only [leafQuery, hidx] at hq1
  have hval : (FtsExtract.coordValues sig c).getD j 0 = sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ := by
    simp [FtsExtract.coordValues, hj]
  rw [hval] at hq1
  exact hq1

/-- **An accepting byte verification ran its FTS part to a value**, within its own queries. -/
theorem verifyP_fts_run (answers : Correctness.Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ root, evalWithAnswerFn answers (ftsP w ((evalWithAnswerFn answers (digest (wrho w) m (wdc w))).toNat % 2 ^ 31)
        (selections (evalWithAnswerFn answers (digest (wrho w) m (wdc w))))) = some root ∧
      ∀ q ∈ queried answers (ftsP w ((evalWithAnswerFn answers (digest (wrho w) m (wdc w))).toNat % 2 ^ 31)
        (selections (evalWithAnswerFn answers (digest (wrho w) m (wdc w))))), q ∈ queried answers (verifyP m pk w) := by
  classical
  rw [verifyP_eq_tail] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · have h0 : digestP m w = pure none := by unfold digestP; rw [if_pos hdc]
    rw [h0] at hv; simp at hv
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg hdc]
  rw [hD] at hv ⊢
  rw [Extract.queried_map]
  simp only [evalWithAnswerFn_map] at hv ⊢
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv ⊢
  try simp only at hv ⊢
  unfold verifyTailP at hv ⊢
  simp only at hv ⊢
  by_cases hsel : selectionsOk (selections N) = true
  swap
  · rw [if_pos (by simpa using hsel)] at hv; simp at hv
  rw [if_neg (by simpa using hsel)] at hv ⊢
  by_cases hg : digestGate N = true
  swap
  · rw [if_pos (by simpa using hg)] at hv; simp at hv
  rw [if_neg (by simpa using hg)] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers (ftsP w (N.toNat % 2 ^ 31) (selections N)) = rr at hv ⊢
  rcases rr with _ | root
  · simp at hv
  exact ⟨root, rfl, fun q hq => by simp only [List.mem_append]; tauto⟩

/-- **Case (C): an accepting verification queried the honest leaf input of every opened position** (adapted
from stream CC's `verdict_leaf_entries`, stated on the verification's own queries). -/
theorem verifyP_leaf_queried (answers : Correctness.Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true)
    (hS : Shaped (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w)
    (hF : FtsExtract.FtsShaped answers (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w) :
    ∀ f ∈ BPair.openedPositions (evalWithAnswerFn answers (digest (wrho w) m (wdc w))),
      (.inl (.inr (BPair.probeInput f (BPair.secretAt answers f))) : T3.Spec.Domain) ∈
        queried answers (verifyP m pk w) := by
  set N := evalWithAnswerFn answers (digest (wrho w) m (wdc w)) with hN
  obtain ⟨root, hroot, hfq⟩ := verifyP_fts_run answers m pk w hv
  rw [← hN, ftsP_shaped N w hS] at hroot hfq
  have hc := chosenOk_of N hS.1
  intro f hfo
  unfold BPair.openedPositions at hfo
  rw [List.mem_flatMap] at hfo
  obtain ⟨c, -, hfc⟩ := hfo
  rw [List.mem_map] at hfc
  obtain ⟨leaf, hleaf, rfl⟩ := hfc
  set sel := (selections N).getD c.val ⟨0, []⟩ with hsel
  have hsok : SelOk sel := hc c.val c.isLt
  obtain ⟨j, hj, hjl⟩ : ∃ j < 3, sel.leaves.getD j 0 = leaf := by
    have hl := hsok.leaves_eq
    rw [hl] at hleaf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hleaf
    rcases hleaf with h | h | h
    · exact ⟨0, by decide, h.symm⟩
    · exact ⟨1, by decide, h.symm⟩
    · exact ⟨2, by decide, h.symm⟩
  have hq := recoverFtsP_leaf_queried answers _ _ _ _ root hc hroot c.val c.isLt j hj
  obtain ⟨hsec, hp0, hp1⟩ := hF.2 c.val c.isLt j hj
  have hlt : 3 * c.val + j < 21 := by have := c.isLt; omega
  have hm21 : (c.val * 3 + j) % 21 = 3 * c.val + j := by rw [Nat.mod_eq_of_lt (by omega)]; ring
  have hm22 : (3 * c.val + j) % 22 = 3 * c.val + j := Nat.mod_eq_of_lt (by omega)
  have hm22' : (3 * c.val + j + 1) % 22 = 3 * c.val + j + 1 := Nat.mod_eq_of_lt (by omega)
  have hq' : (.inl (.inr (ftsLeafInputP (N.toNat % 2 ^ 31) c.val (selLeaf sel j) 0
      (Extract.ftsSecret answers (N.toNat % 2 ^ 31) c.val (selLeaf sel j)) 0)) : T3.Spec.Domain) ∈
      queried answers (verifyP m pk w) := by
    apply hfq
    have e1 : (padDecP N w).leaf ⟨(3 * c.val + j) % 22, Nat.mod_lt _ (by decide)⟩ = 0 := by
      show wleafPad w ((3 * c.val + j) % 22) = 0
      rw [hm22]; exact hp0
    have e2 : (padDecP N w).leaf ⟨(3 * c.val + j + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0 := by
      show wleafPad w ((3 * c.val + j + 1) % 22) = 0
      rw [hm22']; exact hp1
    have e3 : (witDecP N w).signature.secrets ⟨(c.val * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ =
        Extract.ftsSecret answers (N.toNat % 2 ^ 31) c.val (selLeaf sel j) := by
      show wsecret w ((c.val * 3 + j) % 21) = _
      rw [hm21]; exact hsec
    rw [e1, e2, e3] at hq
    exact hq
  -- the opened position's probe is this query
  have hb := hsok.b
  have hl256 : leaf < 128 := by
    have := hsok.l2; have := hsok.s01; have := hsok.s12
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> omega
  have hpos : (BPair.leafIndex sel.bucket leaf).val = selLeaf sel j := by
    unfold BPair.leafIndex selLeaf
    simp only [hjl]
    exact Nat.mod_eq_of_lt (by omega)
  have hidx : (BPair.outputIndex N).val = N.toNat % 2 ^ 31 := rfl
  have hprobe : (.inl (.inr (BPair.probeInput (BPair.outputIndex N, c, BPair.leafIndex sel.bucket leaf)
      (BPair.secretAt answers (BPair.outputIndex N, c, BPair.leafIndex sel.bucket leaf)))) : T3.Spec.Domain) =
      .inl (.inr (ftsLeafInputP (N.toNat % 2 ^ 31) c.val (selLeaf sel j) 0
        (Extract.ftsSecret answers (N.toNat % 2 ^ 31) c.val (selLeaf sel j)) 0)) := by
    rw [← BPair.honestInput_ftsLeaf, FtsExtract.honestInput_ftsLeaf]
    simp only [hidx, hpos]
    rfl
  rw [← hprobe] at hq'
  exact hq'

end SigGolfCandidate.T3.Security.LargeCoupling.CertLeaf
