import SigGolfCandidate.T3.Secc.LargeContactWalk
import SigGolfCandidate.T3.Secc.PairGuessFinal
import SigGolfCandidate.T3.Secc.LargeCouplingCertDefs
import SigGolfCandidate.T3.Secc.LargeContactCase
import SigGolfCandidate.T3.Secc.SeccSufRoute

section


namespace SigGolfCandidate.T3.Security.LargeCoupling.CertLeaf
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def leafQuery (index coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads) (g : Nat) :
    T3.Spec.Domain :=
  .inl (.inr (ftsLeafInputP index coord g
    (pads.leaf ⟨(3 * coord + leaves.idxOf g) % 22, Nat.mod_lt _ (by decide)⟩)
    (values.getD (leaves.idxOf g) 0)
    (pads.leaf ⟨(3 * coord + leaves.idxOf g + 1) % 22, Nat.mod_lt _ (by decide)⟩)))
theorem recoverChildP_leaf_queried (answers : Correctness.Answers) (index coord : Nat) (leaves : List Nat)
    (values : List Digest) (proof : Fin 115 → Digest) (pads : Pads) :
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
end

section



namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactCertFold : DecidableEq T3.Cache := Classical.decEq _
def CoverOk (st : RouterState) : Prop :=
  ∀ m c N, st.memo.lookup m = some (some (c, N)) → N ∈ st.exposures ∨ st.reused = true
def signCount : List TaggedStep → Nat
  | [] => 0
  | .world _ :: rest => signCount rest
  | .sign _ _ _ :: rest => signCount rest + 1
def stepLog : List TaggedStep → QueryLog Requests
  | [] => []
  | .world _ :: rest => stepLog rest
  | .sign request output _ :: rest => ⟨request, output⟩ :: stepLog rest
theorem signCount_eq_length (steps : List TaggedStep) : signCount steps = (stepLog steps).length := by
  induction steps with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [signCount, stepLog, ih]
theorem taggedRecord_log {α : Type} (program : OracleComp LazyPrivate.Interaction α) (published : T3.Cache)
    (state : LazyPrivate.State) (t : Tagged α) (ht : t ∈ support (taggedRecord published program state)) :
    t.value.2 = stepLog t.steps := by
  induction program using OracleComp.inductionOn generalizing state t with
  | pure value =>
      rw [taggedRecord_pure, mem_support_pure_iff] at ht
      subst ht
      rfl
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [taggedRecord_world, mem_support_bind_iff] at ht
          obtain ⟨middle, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          exact ih middle.1 middle.2 last hl
      | inr request =>
          rw [taggedRecord_request, mem_support_bind_iff] at ht
          obtain ⟨block, -, ht⟩ := ht
          rw [support_map] at ht
          obtain ⟨last, hl, rfl⟩ := ht
          change ⟨request, block.value⟩ :: last.value.2 = ⟨request, block.value⟩ :: stepLog last.steps
          rw [ih block.value block.state last hl]
theorem sign_mem_stepLog {steps : List TaggedStep} {request : Security.Request} {output : Option Signature}
    {events : List FirstHit.QueryEvent} (h : TaggedStep.sign request output events ∈ steps) :
    (⟨request, output⟩ : (r : Requests.Domain) × Requests.Range r) ∈ stepLog steps := by
  induction steps with
  | nil => cases h
  | cons s rest ih =>
      rcases List.mem_cons.mp h with rfl | h'
      · exact List.mem_cons_self
      · cases s with
        | world e => exact ih h'
        | sign r o ev => exact List.mem_cons_of_mem _ (ih h')
section Fold
variable (U : Finset HashInput) (A : Answers) (published : T3.Cache)
theorem routerEvent_fields (st : RouterState) (e : FirstHit.QueryEvent) :
    (routerEvent U st e).exposures = st.exposures ∧ (routerEvent U st e).reused = st.reused ∧
      (routerEvent U st e).memo = st.memo ∧ (routerEvent U st e).trials = st.trials := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · change (st.next U X y).exposures = _ ∧ (st.next U X y).reused = _ ∧ (st.next U X y).memo = _ ∧
      (st.next U X y).trials = _
    unfold RouterState.next
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩
theorem routerEvents_fields (events : List FirstHit.QueryEvent) (st : RouterState) :
    (events.foldl (routerEvent U) st).exposures = st.exposures ∧ (events.foldl (routerEvent U) st).reused = st.reused ∧
      (events.foldl (routerEvent U) st).memo = st.memo ∧ (events.foldl (routerEvent U) st).trials = st.trials := by
  induction events generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2, h3, h4⟩ := ih (routerEvent U st e)
      obtain ⟨g1, g2, g3, g4⟩ := routerEvent_fields U st e
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩
theorem finishState_bank (st1 : RouterState) (found : Option (BitVec 32 × HashOutput)) :
    (finishState A st1 found).exposures = st1.exposures ∧ (finishState A st1 found).reused = st1.reused ∧
      (finishState A st1 found).memo = st1.memo ∧ (finishState A st1 found).trials = st1.trials := by
  unfold finishState
  cases found with
  | none => exact ⟨rfl, rfl, rfl, rfl⟩
  | some f =>
      obtain ⟨c, N⟩ := f
      dsimp only
      split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩
theorem signedState_bank (nv : Message → Digest) (st : RouterState) (request : Security.Request) :
    (request.cache = published →
      (signedState A nv published st request).exposures = (startState A nv st request.message).exposures ∧
      (signedState A nv published st request).reused = (startState A nv st request.message).reused ∧
      (signedState A nv published st request).memo = (startState A nv st request.message).memo ∧
      (signedState A nv published st request).trials = (startState A nv st request.message).trials) ∧
    (request.cache ≠ published → signedState A nv published st request = st) := by
  rw [signedState_eq]
  constructor
  · intro hc
    rw [if_pos hc]
    exact finishState_bank A _ _
  · intro hc
    rw [if_neg hc]
theorem signed_memo_lookup (st : RouterState) (rho : Digest) (m m' : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (st.signed rho m found).memo.lookup m' = if m' = m then some found else st.memo.lookup m' := by
  rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.2, List.lookup_cons]
  by_cases h : m' = m
  · subst h; simp
  · have hne : (m' == m) = false := by simpa using h
    rw [hne, if_neg h]
theorem signed_exposures_reused (st : RouterState) (rho : Digest) (m : Message)
    (found : Option (BitVec 32 × HashOutput)) :
    (∀ N, N ∈ st.exposures → N ∈ (st.signed rho m found).exposures) ∧
      (st.reused = true → (st.signed rho m found).reused = true) ∧
      (∀ c N, found = some (c, N) → N ∈ (st.signed rho m found).exposures ∨ (st.signed rho m found).reused = true) := by
  unfold RouterState.signed
  split_ifs
  · exact ⟨fun N h => h, fun _ => rfl, fun _ _ _ => Or.inr rfl⟩
  · refine ⟨fun N h => List.mem_append_left _ h, fun h => h, fun c N hf => Or.inl ?_⟩
    subst hf
    simp
theorem coverOk_startState (nv : Message → Digest) (st : RouterState) (m : Message) (h : CoverOk st)
    (hmemo : MemoOk A st) : CoverOk (startState A nv st m) ∧ MemoOk A (startState A nv st m) := by
  unfold startState
  split_ifs with hs
  · exact ⟨h, hmemo⟩
  · obtain ⟨hx, hr, hnew⟩ := signed_exposures_reused st (nv m) m (LargeResidual.signDigest A m)
    constructor
    · intro m' c N hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · exact hnew c N (Option.some.inj hl)
      · rcases h m' c N hl with h1 | h1
        · exact Or.inl (hx N h1)
        · exact Or.inr (hr h1)
    · intro m' f hl
      rw [signed_memo_lookup] at hl
      split_ifs at hl with hm
      · subst hm; exact (Option.some.inj hl).symm
      · exact hmemo m' f hl
theorem coverOk_signedState (st : RouterState) (request : Security.Request) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (signedState A (honestNonce A) published st request) := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · obtain ⟨h1, h2, h3, -⟩ := hpub hc
    intro m c N hl
    rw [h1, h2]
    rw [h3] at hl
    exact (coverOk_startState A (honestNonce A) st request.message h hmemo).1 m c N hl
  · rw [hnpub hc]; exact h
theorem coverOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : CoverOk st) : CoverOk (routerEvent U st e) := by
  obtain ⟨h1, h2, h3, -⟩ := routerEvent_fields U st e
  intro m c N hl
  rw [h1, h2]
  rw [h3] at hl
  exact h m c N hl
theorem memoOk_event (st : RouterState) (e : FirstHit.QueryEvent) (h : MemoOk A st) : MemoOk A (routerEvent U st e) := by
  intro m f hl
  rw [(routerEvent_fields U st e).2.2.1] at hl
  exact h m f hl
theorem invariants_steps (steps : List TaggedStep) (st : RouterState) (h : CoverOk st) (hmemo : MemoOk A st) :
    CoverOk (steps.foldl (routerStep U A (honestNonce A) published) st) ∧
      MemoOk A (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      · cases s with
        | world e => exact coverOk_event U st e h
        | sign request out evs => exact coverOk_signedState A published st request h hmemo
      · cases s with
        | world e => exact memoOk_event U A st e hmemo
        | sign request out evs => exact signedState_memo A (honestNonce A) published st request hmemo
theorem invariants_events (events : List FirstHit.QueryEvent) (st : RouterState) (h : CoverOk st)
    (hmemo : MemoOk A st) :
    CoverOk (events.foldl (routerEvent U) st) ∧ MemoOk A (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact ⟨h, hmemo⟩
  | cons e rest ih =>
      rw [List.foldl_cons]
      exact ih _ (coverOk_event U st e h) (memoOk_event U A st e hmemo)
theorem memo_isSome_event (st : RouterState) (e : FirstHit.QueryEvent) (m : Message)
    (h : (st.memo.lookup m).isSome) : ((routerEvent U st e).memo.lookup m).isSome := by
  rw [(routerEvent_fields U st e).2.2.1]; exact h
theorem memo_isSome_sign (st : RouterState) (request : Security.Request) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((signedState A (honestNonce A) published st request).memo.lookup m).isSome := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.1]
    unfold startState
    split_ifs with hs
    · exact h
    · rw [signed_memo_lookup]
      split_ifs <;> simp_all
  · rw [hnpub hc]; exact h
theorem memo_isSome_signed_self (st : RouterState) (request : Security.Request) (hc : request.cache = published) :
    ((signedState A (honestNonce A) published st request).memo.lookup request.message).isSome := by
  rw [((signedState_bank A published (honestNonce A) st request).1 hc).2.2.1]
  unfold startState
  split_ifs with hs
  · exact hs
  · rw [signed_memo_lookup, if_pos rfl]; rfl
theorem memo_isSome_steps (steps : List TaggedStep) (st : RouterState) (m : Message)
    (h : (st.memo.lookup m).isSome) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup m).isSome := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact memo_isSome_event U st e m h
      | sign request out evs => exact memo_isSome_sign A published st request m h
theorem sign_memo_steps (steps : List TaggedStep) (st : RouterState) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) :
    ((steps.foldl (routerStep U A (honestNonce A) published) st).memo.lookup request.message).isSome := by
  induction steps generalizing st with
  | nil => cases hmem
  | cons s rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact memo_isSome_steps U A published rest _ _ (memo_isSome_signed_self A published st request hc)
      · exact ih _ hmem
theorem covered_fold (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) (request : Security.Request)
    (out : Option Signature) (evs : List FirstHit.QueryEvent) (hmem : TaggedStep.sign request out evs ∈ steps)
    (hc : request.cache = published) (c : BitVec 32) (N : HashOutput)
    (hN : LargeResidual.signDigest A request.message = some (c, N)) :
    N ∈ (routerFold U A published steps verdict).exposures ∨ (routerFold U A published steps verdict).reused = true := by
  unfold routerFold
  have hinv0 : CoverOk RouterState.initial ∧ MemoOk A RouterState.initial :=
    ⟨fun m c N h => by simp [RouterState.initial] at h, fun m f h => by simp [RouterState.initial] at h⟩
  obtain ⟨h1, h2⟩ := invariants_steps U A published steps _ hinv0.1 hinv0.2
  obtain ⟨h3, h4⟩ := invariants_events U A verdict _ h1 h2
  have hs := sign_memo_steps U A published steps RouterState.initial request out evs hmem hc
  have hs' : ((verdict.foldl (routerEvent U) (steps.foldl (routerStep U A (honestNonce A) published)
      RouterState.initial)).memo.lookup request.message).isSome := by
    rw [(routerEvents_fields U verdict _).2.2.1]; exact hs
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hs'
  have hfe := h4 _ _ hf
  rw [hN] at hfe
  subst hfe
  exact h3 _ c N hf
theorem exposures_signedState_le (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).exposures.length ≤ st.exposures.length + 1 := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).1]
    unfold startState
    split_ifs
    · omega
    · unfold RouterState.signed
      split_ifs
      · dsimp only; omega
      · dsimp only
        rw [List.length_append]
        have : ((LargeResidual.signDigest A request.message).map Prod.snd).toList.length ≤ 1 := by
          cases LargeResidual.signDigest A request.message <;> simp
        omega
  · rw [hnpub hc]; omega
theorem exposures_steps_le (steps : List TaggedStep) (st : RouterState) :
    (steps.foldl (routerStep U A (honestNonce A) published) st).exposures.length ≤
      st.exposures.length + signCount steps := by
  induction steps generalizing st with
  | nil => simp [signCount]
  | cons s rest ih =>
      rw [List.foldl_cons]
      refine (ih _).trans ?_
      cases s with
      | world e =>
          change (routerEvent U st e).exposures.length + signCount rest ≤ st.exposures.length + signCount rest
          rw [(routerEvent_fields U st e).1]
      | sign request out evs =>
          have := exposures_signedState_le A published st request
          change (signedState A (honestNonce A) published st request).exposures.length + signCount rest ≤
            st.exposures.length + (signCount rest + 1)
          omega
theorem exposures_fold_le (steps : List TaggedStep) (verdict : List FirstHit.QueryEvent) :
    (routerFold U A published steps verdict).exposures.length ≤ signCount steps := by
  unfold routerFold
  rw [(routerEvents_fields U verdict _).1]
  have := exposures_steps_le U A published steps RouterState.initial
  simpa [RouterState.initial] using this
theorem trials_steps (steps : List TaggedStep) (st : RouterState) (X : HashInput)
    (hX : X ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials) :
    X ∈ st.trials ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧ request.cache = published ∧
      X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message) := by
  induction steps generalizing st with
  | nil => exact Or.inl hX
  | cons s rest ih =>
      rw [List.foldl_cons] at hX
      rcases ih _ hX with h | ⟨r, o, e, hm, hc, hr⟩
      · cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials at h
            rw [(routerEvent_fields U st e).2.2.2] at h
            exact Or.inl h
        | sign request out evs =>
            change X ∈ (signedState A (honestNonce A) published st request).trials at h
            obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
            by_cases hc : request.cache = published
            · rw [(hpub hc).2.2.2] at h
              unfold startState at h
              split_ifs at h
              · exact Or.inl h
              · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1, List.mem_append] at h
                rcases h with h | h
                · exact Or.inl h
                · exact Or.inr ⟨request, out, evs, List.mem_cons_self, hc, h⟩
            · rw [hnpub hc] at h; exact Or.inl h
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hc, hr⟩
theorem seen_event_mono' (st : RouterState) (e : FirstHit.QueryEvent) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (routerEvent U st e).seen := by
  rcases e with ⟨b, (n | X) | c, y⟩
  · exact h
  · change Y ∈ (st.next U X y).seen
    unfold RouterState.next
    split_ifs <;> exact List.mem_cons_of_mem _ h
  · exact h
theorem seen_event_self (st : RouterState) (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) :
    X ∈ (routerEvent U st ⟨b, .inl (.inr X), y⟩).seen := by
  change X ∈ (st.next U X y).seen
  unfold RouterState.next
  split_ifs <;> exact List.mem_cons_self
theorem seen_events_mono' (events : List FirstHit.QueryEvent) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih => exact ih _ (seen_event_mono' U st e Y h)
theorem seen_signed (st : RouterState) (request : Security.Request) :
    (signedState A (honestNonce A) published st request).seen = st.seen ∧
      (signedState A (honestNonce A) published st request).births = st.births := by
  refine ⟨(signedState_seen A (honestNonce A) published st request).1, ?_⟩
  rw [signedState_eq]
  split_ifs
  · rw [(finishState_fields _ _ _).2.2.2.1, (startState_fields _ _ _ _).2.2.2]
  · rfl
theorem seen_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.seen) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).seen := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e => exact seen_event_mono' U st e Y h
      | sign request out evs =>
          change Y ∈ (signedState A (honestNonce A) published st request).seen
          rw [(seen_signed A published st request).1]; exact h
def BirthInv (X : HashInput) (N : HashOutput) (st : RouterState) : Prop := X ∈ st.seen → (X, N) ∈ st.births
theorem birthInv_event (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (st : RouterState) (e : FirstHit.QueryEvent) (hans : ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (htr : X ∉ st.trials) (h : BirthInv X N st) : BirthInv X N (routerEvent U st e) := by
  rcases e with ⟨b, (n | Y) | c, y⟩
  · exact h
  · change X ∈ (st.next U Y y).seen → (X, N) ∈ (st.next U Y y).births
    intro hs
    unfold RouterState.next at hs ⊢
    by_cases hY : Y = X
    · subst hY
      have hy : y = N := hans b y rfl
      subst hy
      by_cases hf : st.Fresh Y
      · rw [if_pos ⟨hXU, hXd, hf⟩]
        exact List.mem_cons_self
      · have hfr : ¬(Y ∈ U ∧ IsDigestRow Y ∧ st.Fresh Y) := fun h' => hf h'.2.2
        rw [if_neg hfr]
        have hseen : Y ∈ st.seen := by
          by_contra hn
          exact hf ⟨hn, htr⟩
        exact h hseen
    · have hs' : X ∈ st.seen := by
        split_ifs at hs <;>
        · rcases List.mem_cons.mp hs with h1 | h1
          · exact absurd h1.symm hY
          · exact h1
      split_ifs
      · exact List.mem_cons_of_mem _ (h hs')
      · exact h hs'
  · exact h
theorem birthInv_events (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (events : List FirstHit.QueryEvent) (hans : ∀ e ∈ events, ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ st.trials) (h : BirthInv X N st) :
    BirthInv X N (events.foldl (routerEvent U) st) := by
  induction events generalizing st with
  | nil => exact h
  | cons e rest ih =>
      rw [List.foldl_cons]
      apply ih (fun e' he' => hans e' (List.mem_cons_of_mem _ he'))
      · rw [(routerEvent_fields U st e).2.2.2]; exact htr
      · exact birthInv_event U X N hXU hXd st e (hans e List.mem_cons_self) htr h
theorem trials_sign_mono (st : RouterState) (request : Security.Request) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (signedState A (honestNonce A) published st request).trials := by
  obtain ⟨hpub, hnpub⟩ := signedState_bank A published (honestNonce A) st request
  by_cases hc : request.cache = published
  · rw [(hpub hc).2.2.2]
    unfold startState
    split_ifs
    · exact h
    · rw [(RouterState.signed_fields _ _ _ _).2.2.2.2.1]; exact List.mem_append_left _ h
  · rw [hnpub hc]; exact h
theorem trials_steps_mono (steps : List TaggedStep) (st : RouterState) (Y : HashInput) (h : Y ∈ st.trials) :
    Y ∈ (steps.foldl (routerStep U A (honestNonce A) published) st).trials := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons]
      apply ih
      cases s with
      | world e =>
          change Y ∈ (routerEvent U st e).trials
          rw [(routerEvent_fields U st e).2.2.2]; exact h
      | sign request out evs => exact trials_sign_mono A published st request Y h
theorem birthInv_steps (X : HashInput) (N : HashOutput) (hXU : X ∈ U) (hXd : IsDigestRow X)
    (steps : List TaggedStep)
    (hans : ∀ s ∈ steps, ∀ e, s = .world e → ∀ b y, e = ⟨b, .inl (.inr X), y⟩ → y = N)
    (st : RouterState) (htr : X ∉ (steps.foldl (routerStep U A (honestNonce A) published) st).trials)
    (h : BirthInv X N st) :
    BirthInv X N (steps.foldl (routerStep U A (honestNonce A) published) st) := by
  induction steps generalizing st with
  | nil => exact h
  | cons s rest ih =>
      rw [List.foldl_cons] at htr ⊢
      have hrest := fun s' hs' => hans s' (List.mem_cons_of_mem _ hs')
      apply ih hrest _ htr
      have hst : X ∉ st.trials := fun hm => htr (trials_steps_mono U A published rest _ X (by
        cases s with
        | world e =>
            change X ∈ (routerEvent U st e).trials
            rw [(routerEvent_fields U st e).2.2.2]; exact hm
        | sign request out evs => exact trials_sign_mono A published st request X hm))
      cases s with
      | world e => exact birthInv_event U X N hXU hXd st e (hans _ List.mem_cons_self e rfl) hst h
      | sign request out evs =>
          change X ∈ (signedState A (honestNonce A) published st request).seen →
            (X, N) ∈ (signedState A (honestNonce A) published st request).births
          rw [(seen_signed A published st request).1, (seen_signed A published st request).2]
          exact h
end Fold
end SigGolfCandidate.T3.Security.LargeCoupling
end

section


namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeContactCert : DecidableEq T3.Cache := Classical.decEq _
theorem treeChild_inl {lay : Layer} {tree : Fin (2 ^ 31)} {level c : Nat} {x : Coord}
    (h : treeChild lay tree level c = some x) : ∃ n, x = .inl n := by
  unfold treeChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem ftsChild_inl {index : Fin (2 ^ 31)} {coord : Fin 7} {level c : Nat} {x : Coord}
    (h : ftsChild index coord level c = some x) : ∃ n, x = .inl n := by
  unfold ftsChild at h
  split_ifs at h
  · exact ⟨_, (Option.some.inj h).symm⟩
  · obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_, rfl⟩
theorem not_inr_keygenDisclosed (s : CanonGraph.SecretIndex) : (.inr s : Coord) ∉ keygenDisclosed := by
  unfold keygenDisclosed
  intro h
  simp only [List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨_, _, _, _, hc⟩ := h
  obtain ⟨n, hn⟩ := treeChild_inl hc
  cases hn
theorem secret_mem_signItems (digitsOf : Wots.LeafAddr → List Nat) (N : HashOutput) (p : CanonGraph.FtsLeafPos)
    (h : (.inr (.inr p) : Coord) ∈ signItemsWith digitsOf N) : BPair.ofLeafPos p ∈ BPair.openedPositions N := by
  unfold signItemsWith at h
  rcases List.mem_append.mp h with h | h
  · unfold ftsItems at h
    rw [List.mem_flatMap] at h
    obtain ⟨coord, hcoord, h⟩ := h
    rw [List.mem_range] at hcoord
    rcases List.mem_append.mp h with h | h
    · unfold ftsOpened at h
      rw [List.mem_filterMap] at h
      obtain ⟨leaf, hleaf, hl⟩ := h
      rw [List.mem_map] at hleaf
      obtain ⟨s, hs, rfl⟩ := hleaf
      split_ifs at hl with h2048
      have hp := Sum.inr.inj (Sum.inr.inj (Option.some.inj hl))
      subst hp
      unfold BPair.openedPositions
      rw [List.mem_flatMap]
      refine ⟨⟨coord, hcoord⟩, List.mem_finRange _, ?_⟩
      rw [List.mem_map]
      refine ⟨s, hs, ?_⟩
      unfold BPair.ofLeafPos BPair.leafIndex BPair.outputIndex
      simp only [Prod.mk.injEq]
      refine ⟨rfl, ?_, ?_⟩
      · exact Fin.ext (Nat.mod_eq_of_lt hcoord).symm
      · exact Fin.ext (Nat.mod_eq_of_lt h2048)
    · exfalso
      unfold ftsProof at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := ftsChild_inl hc
        cases hn
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := ftsChild_inl hc
        cases hn
  · exfalso
    unfold layerItems at h
    rw [List.mem_flatMap] at h
    obtain ⟨lay, -, h⟩ := h
    rcases List.mem_append.mp h with h | h
    · unfold layerChains at h
      split_ifs at h
      · rw [List.mem_map] at h
        obtain ⟨i, -, hi⟩ := h
        unfold chainItem at hi
        split_ifs at hi <;> cases hi
      · cases h
    · unfold layerPath at h
      split_ifs at h
      · obtain ⟨_, _, hc⟩ := List.mem_filterMap.mp h
        obtain ⟨n, hn⟩ := treeChild_inl hc
        cases hn
      · cases h
theorem disclosed_steps_mem (U : Finset HashInput) (A : Answers) (q : Nat) (published : T3.Cache)
    (steps : List TaggedStep) (mon : Monitor) (d : Coord)
    (hd : d ∈ (steps.foldl (Monitor.step U A q published) mon).disclosed) :
    d ∈ mon.disclosed ∨ ∃ request out evs, TaggedStep.sign request out evs ∈ steps ∧
      d ∈ signDisclosed A published request := by
  induction steps generalizing mon with
  | nil => exact Or.inl hd
  | cons s rest ih =>
      rw [List.foldl_cons] at hd
      rcases ih _ hd with h | ⟨r, o, e, hm, hr⟩
      · cases s with
        | world e =>
            change d ∈ (mon.event U A q e).disclosed at h
            rw [disclosed_event] at h
            exact Or.inl h
        | sign request out evs =>
            change d ∈ (mon.sign A published request).disclosed at h
            unfold Monitor.sign at h
            split_ifs at h
            · exact Or.inl h
            · rcases List.mem_append.mp h with h | h
              · exact Or.inl h
              · exact Or.inr ⟨request, out, evs, List.mem_cons_self, h⟩
      · exact Or.inr ⟨r, o, e, List.mem_cons_of_mem _ hm, hr⟩
theorem posOf_probeInput (f : BPair.FtsCoord) (s : Digest) :
    Extract.posOf (BPair.probeInput f s) = some (CanonGraph.Node.ftsLeaf (BPair.toLeafPos f)).toPos := by
  apply Extract.posOf_eq (CanonGraph.toPos_bounded _)
  rw [BPair.hdrBlock_probeInput]
  rfl
theorem slotValue_probeInput (f : BPair.FtsCoord) (s : Digest) : slotValue (BPair.probeInput f s) 2 = s := by
  rw [BPair.probeInput_eq]
  exact (slotValue_block4 0 _ s 0).2.1
theorem search_queried (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start k, start ≤ k → k < start + fuel →
      (∀ c', start ≤ c' → c' < k →
        digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) →
      (.inl (.inr (pad64 (digestInput rho m (BitVec.ofNat 32 k)))) : T3.Spec.Domain) ∈
        queried A (digestSearch rho m start fuel) := by
  intro fuel
  induction fuel with
  | zero => intro start k h1 h2; omega
  | succ fuel ih =>
      intro start k h1 h2 hrej
      rw [BPB.digestSearch_succ, queried_bind, BPB.queried_digest]
      by_cases hk : k = start
      · subst hk
        exact List.mem_append_left _ (List.mem_singleton_self _)
      · apply List.mem_append_right
        rw [if_neg (by rw [hrej start le_rfl (by omega)]; decide)]
        exact ih (start + 1) k (by omega) (by omega) (fun c' h1' h2' => hrej c' (by omega) h2')
theorem search_result (A : Answers) (rho : Digest) (m : Message) :
    ∀ fuel start,
      (∀ c N, evalWithAnswerFn A (digestSearch rho m start fuel) = some (c, N) →
        ∃ k, start ≤ k ∧ k < start + fuel ∧ c = BitVec.ofNat 32 k ∧ ∀ c', start ≤ c' → c' < k →
          digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) ∧
      (evalWithAnswerFn A (digestSearch rho m start fuel) = none → ∀ c', start ≤ c' → c' < start + fuel →
          digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 c'))) = false) := by
  intro fuel
  induction fuel with
  | zero =>
      intro start
      refine ⟨fun c N h => ?_, fun _ c' h1 h2 => by omega⟩
      simp [digestSearch] at h
  | succ fuel ih =>
      intro start
      rw [BPB.digestSearch_succ, evalWithAnswerFn_bind]
      by_cases hadm : digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = true
      · rw [if_pos hadm, evalWithAnswerFn_pure]
        refine ⟨fun c N h => ?_, fun h => by cases h⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨start, le_rfl, by omega, h.1.symm, fun c' h1 h2 => by omega⟩
      · rw [if_neg hadm]
        have hrej : digestAdmissible (evalWithAnswerFn A (digest rho m (BitVec.ofNat 32 start))) = false := by
          simpa using hadm
        obtain ⟨ih1, ih2⟩ := ih (start + 1)
        refine ⟨fun c N h => ?_, fun h c' h1 h2 => ?_⟩
        · obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih1 c N h
          refine ⟨k, by omega, by omega, hk3, fun c' h1 h2 => ?_⟩
          by_cases hc : c' = start
          · subst hc; exact hrej
          · exact hk4 c' (by omega) h2
        · by_cases hc : c' = start
          · subst hc; exact hrej
          · exact ih2 h c' (by omega) (by omega)
theorem trialRows_queried (A : Answers) (published : T3.Cache) (request : Security.Request)
    (hc : request.cache = published) (X : HashInput)
    (hX : X ∈ trialRows (honestNonce A request.message) request.message (LargeResidual.signDigest A request.message)) :
    (.inl (.inr X) : T3.Spec.Domain) ∈ queried A (FullGame.authenticatedSign published request) := by
  set rho := honestNonce A request.message with hrho
  have hsd : LargeResidual.signDigest A request.message =
      evalWithAnswerFn A (digestSearch rho request.message 0 attemptLimit) := rfl
  have hq : (.inl (.inr X) : T3.Spec.Domain) ∈ queried A (digestSearch rho request.message 0 attemptLimit) := by
    obtain ⟨r1, r2⟩ := search_result A rho request.message attemptLimit 0
    cases hfound : LargeResidual.signDigest A request.message with
    | none =>
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        exact search_queried A rho request.message attemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => r2 (hsd ▸ hfound) c' (Nat.zero_le _) (by omega))
    | some found =>
        obtain ⟨c, N⟩ := found
        rw [hfound] at hX
        unfold trialRows at hX
        rw [List.mem_map] at hX
        obtain ⟨k, hk, rfl⟩ := hX
        rw [List.mem_range] at hk
        dsimp only at hk
        obtain ⟨k0, -, hk0, hck, hrej⟩ := r1 c N (hsd ▸ hfound)
        have hlim : attemptLimit = 2 ^ 20 := rfl
        have hct : c.toNat = k0 := by
          rw [hck, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        exact search_queried A rho request.message attemptLimit 0 k (Nat.zero_le _) (by omega)
          (fun c' _ h2 => hrej c' (Nat.zero_le _) (by omega))
  unfold FullGame.authenticatedSign
  rw [queried_bind, BPB.queried_privateMac]
  apply List.mem_append_right
  rw [if_pos hc, signPayload_factor, queried_bind, BPB.queried_privateNonce]
  apply List.mem_append_right
  rw [queried_bind]
  exact List.mem_append_left _ hq
theorem seen_events_self (U : Finset HashInput) (events : List FirstHit.QueryEvent) (st : RouterState)
    (b : LazyPrivate.State) (X : HashInput) (y : HashOutput) (he : (⟨b, .inl (.inr X), y⟩ : FirstHit.QueryEvent) ∈ events) :
    X ∈ (events.foldl (routerEvent U) st).seen := by
  induction events generalizing st with
  | nil => cases he
  | cons e rest ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp he with rfl | he
      · exact seen_events_mono' U rest _ X (seen_event_self U st b X y)
      · exact ih _ he
end SigGolfCandidate.T3.Security.LargeCoupling
end
