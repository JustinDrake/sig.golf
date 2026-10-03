import SigGolfCandidate.T3M.Extract.FtsPart0

namespace SigGolfCandidate.T3M.FtsExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
theorem sameHeader_ftsLeafInputP (index coord leaf : Nat) (a b c a' b' c' : Digest) :
    Extract.SameHeader (ftsLeafInputP index coord leaf a b c) (ftsLeafInputP index coord leaf a' b' c') := by
  unfold Extract.SameHeader ftsLeafInputP
  rw [hdrBlock_block4, hdrBlock_block4]
theorem sameHeader_nodeInputP (tag lay tree heap : Nat) (a b c a' b' c' : Digest) :
    Extract.SameHeader (nodeInputP tag lay tree heap a b c) (nodeInputP tag lay tree heap a' b' c') := by
  unfold Extract.SameHeader nodeInputP
  rw [hdrBlock_block4, hdrBlock_block4]
def LeavesHonest (coord : Nat) (leaves : List Nat) (values : List Digest) (pads : Pads)
    (secret : Nat → Digest) (level node : Nat) : Prop :=
  ∀ g ∈ leaves, node * 2 ^ level ≤ g → g < (node + 1) * 2 ^ level →
    values.getD (leaves.idxOf g) 0 = secret g ∧
    pads.leaf ⟨(3 * coord + leaves.idxOf g) % 22, Nat.mod_lt _ (by decide)⟩ = 0 ∧
    pads.leaf ⟨(3 * coord + leaves.idxOf g + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0
theorem hasLeaf_false {leaves : List Nat} {level node : Nat} (h : hasLeaf leaves level node = false)
    {g : Nat} (hg : g ∈ leaves) (h0 : node * 2 ^ level ≤ g) (h1 : g < (node + 1) * 2 ^ level) : False := by
  unfold hasLeaf at h
  have := List.any_eq_false.mp h g hg
  simp only [decide_eq_true_eq] at this
  exact this ⟨h0, h1⟩
theorem allHonest_append {answers : Answers} {index coord : Nat} {secret : Nat → Digest}
    {qs qs' : List Spec.Domain} (h : AllHonest answers index coord secret qs)
    (h' : AllHonest answers index coord secret qs') : AllHonest answers index coord secret (qs ++ qs') := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact h q hq
  · exact h' q hq
theorem treeHit_mono {answers : Answers} {index coord : Nat} {secret : Nat → Digest}
    {qs qs' : List Spec.Domain} (h : TreeHit answers index coord secret qs) (hsub : ∀ q ∈ qs, q ∈ qs') :
    TreeHit answers index coord secret qs' := by
  obtain ⟨a, ha, rest⟩ := h
  exact ⟨a, hsub _ ha, rest⟩
theorem recoverChildP_extract (answers : Answers) (index coord : Nat) (leaves : List Nat) (values : List Digest)
    (proof : Fin 115 → Digest) (pads : Pads) (secret : Nat → Digest) :
    ∀ level node used (v : Digest) (next : Nat), level ≤ 11 → node < 2 ^ (11 - level) →
      evalWithAnswerFn answers (recoverChildP index coord leaves values proof pads level node used) =
        some (v, next) →
      v = honL answers index coord secret level node →
      (AllHonest answers index coord secret
          (queried answers (recoverChildP index coord leaves values proof pads level node used)) ∧
        LeavesHonest coord leaves values pads secret level node) ∨
      TreeHit answers index coord secret
        (queried answers (recoverChildP index coord leaves values proof pads level node used)) := by
  intro level
  induction level with
  | zero =>
      intro node used v next hl hn hrun hv
      by_cases hh : hasLeaf leaves 0 node = true
      · have hprog : recoverChildP index coord leaves values proof pads 0 node used =
            (shortHash (ftsLeafInputP index coord node
              (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
              (values.getD (leaves.idxOf node) 0)
              (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩)) >>=
              fun value => pure (some (value, used))) := by
          simp only [recoverChildP, hh, Bool.not_true, Bool.false_eq_true, if_false]; rfl
        rw [hprog] at hrun ⊢
        rw [queried_bind, queried_shortHash, pad64_ftsLeafInputP, queried_pure, List.append_nil]
        rw [evalWithAnswerFn_bind, eval_shortHash_out _ _ (pad64_ftsLeafInputP ..)] at hrun
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rw [honL] at hv
        by_cases heq : ftsLeafInputP index coord node
              (pads.leaf ⟨(3 * coord + leaves.idxOf node) % 22, Nat.mod_lt _ (by decide)⟩)
              (values.getD (leaves.idxOf node) 0)
              (pads.leaf ⟨(3 * coord + leaves.idxOf node + 1) % 22, Nat.mod_lt _ (by decide)⟩) =
            ftsLeafInputP index coord node 0 (secret node) 0
        · obtain ⟨hp0, -, hs, hp1⟩ := ftsLeafInputP_fields heq
          left
          refine ⟨?_, fun g _ h0 h1 => ?_⟩
          · intro q hq
            rw [List.mem_singleton] at hq
            exact ⟨0, node, Nat.zero_le _, hn, by rw [hq, heq]; rfl⟩
          · have : g = node := by simp at h0 h1; omega
            subst this
            exact ⟨hs, hp0, hp1⟩
        · right
          exact ⟨_, List.mem_singleton_self _, 0, node, Nat.zero_le _, hn, ⟨heq, hv⟩, sameHeader_ftsLeafInputP ..⟩
      · have hh : hasLeaf leaves 0 node = false := by simpa using hh
        left
        refine ⟨?_, fun g hg h0 h1 => (hasLeaf_false hh hg h0 h1).elim⟩
        simp only [recoverChildP, hh, Bool.not_false, if_true]
        split <;> simp [AllHonest]
  | succ level ih =>
      intro node used v next hl hn hrun hv
      by_cases hh : hasLeaf leaves (level + 1) node = true
      · have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
          rw [← pow_succ']; congr 1; omega
        rw [recoverChildP] at hrun ⊢
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
        rcases hr2 : evalWithAnswerFn answers (recoverChildP index coord leaves values proof pads level (2 * node + 1) n1)
          with _ | ⟨right, n2⟩
        · rw [hr2] at hrun; simp at hrun
        try rw [hr2] at hrun
        dsimp only at hrun ⊢
        rw [queried_bind, nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP, queried_pure,
          List.append_nil]
        rw [evalWithAnswerFn_bind, nodeHashP_eq_shortHash, eval_shortHash_out _ _ (pad64_nodeInputP ..)] at hrun
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rw [honL] at hv
        by_cases heq : nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node) left
              (foldPad pads leaves level node used n1) right =
            nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node) (honL answers index coord secret level (2 * node))
              0 (honL answers index coord secret level (2 * node + 1))
        · obtain ⟨hlft, -, -, hrgt⟩ := nodeInputP_fields heq
          have c1 := ih (2 * node) used left n1 (by omega) (by omega) hr1 hlft
          have c2 := ih (2 * node + 1) n1 right n2 (by omega) (by omega) hr2 hrgt
          rcases c1 with ⟨a1, l1⟩ | t1
          · rcases c2 with ⟨a2, l2⟩ | t2
            · left
              refine ⟨allHonest_append a1 (allHonest_append a2 ?_), ?_⟩
              · intro q hq
                rw [List.mem_singleton] at hq
                exact ⟨level + 1, node, hl, hn, by rw [hq, heq]; rfl⟩
              · intro g hg h0 h1
                have e0 : node * 2 ^ (level + 1) = 2 * node * 2 ^ level := by rw [pow_succ]; ring
                have e1 : (node + 1) * 2 ^ (level + 1) = (2 * node + 1 + 1) * 2 ^ level := by rw [pow_succ]; ring
                have e2 : (2 * node + 1) * 2 ^ level = 2 * node * 2 ^ level + 2 ^ level := by ring
                by_cases hlo : g < (2 * node + 1) * 2 ^ level
                · exact l1 g hg (by omega) hlo
                · exact l2 g hg (by omega) (by omega)
            · right
              exact treeHit_mono t2 fun q hq => List.mem_append_right _ (List.mem_append_left _ hq)
          · right
            exact treeHit_mono t1 fun q hq => List.mem_append_left _ hq
        · right
          exact ⟨_, List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self _)),
            level + 1, node, hl, hn, ⟨heq, hv⟩, sameHeader_nodeInputP ..⟩
      · have hh : hasLeaf leaves (level + 1) node = false := by simpa using hh
        left
        refine ⟨?_, fun g hg h0 h1 => (hasLeaf_false hh hg h0 h1).elim⟩
        rw [recoverChildP]
        simp only [hh, Bool.not_false, if_true]
        split <;> simp [AllHonest]
theorem outerStepP_some_lt (sig : Signature) (pads : Pads) (index coord bucket : Nat) (w : Digest) (u j : Nat)
    (h : u < 115) : outerStepP sig pads index coord bucket (some (w, u)) j =
      (nodeHashP 10 coord index (2 ^ (11 - (7 + j + 1)) + bucket / 2 ^ (j + 1))
        (if bucket / 2 ^ j % 2 = 0 then w else sig.proof ⟨u, h⟩) (pads.fold ⟨u, h⟩)
        (if bucket / 2 ^ j % 2 = 0 then sig.proof ⟨u, h⟩ else w) >>= fun parent => pure (some (parent, u + 1))) := by
  unfold outerStepP
  simp only [dif_pos h, show 4 - j - 1 = 11 - (7 + j + 1) by omega]
  split <;> rfl
theorem outer_extract (answers : Answers) (sig : Signature) (pads : Pads) (index coord bucket : Nat)
    (secret : Nat → Digest) (hb : bucket < 16) (v0 : Digest) (u0 : Nat) :
    ∀ n, n ≤ 4 → ∀ (v : Digest) (u : Nat),
      evalWithAnswerFn answers ((List.range n).foldlM (outerStepP sig pads index coord bucket) (some (v0, u0))) =
        some (v, u) →
      v = honL answers index coord secret (7 + n) (bucket / 2 ^ n) →
      (v0 = honL answers index coord secret 7 bucket ∧ AllHonest answers index coord secret
          (queried answers ((List.range n).foldlM (outerStepP sig pads index coord bucket) (some (v0, u0))))) ∨
      TreeHit answers index coord secret
        (queried answers ((List.range n).foldlM (outerStepP sig pads index coord bucket) (some (v0, u0)))) := by
  intro n
  induction n with
  | zero =>
      intro _ v u hrun hv
      simp only [List.range_zero, List.foldlM_nil, evalWithAnswerFn_pure, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      left
      refine ⟨by simpa using hv, ?_⟩
      simp [AllHonest]
  | succ n ih =>
      intro hn v u hrun hv
      rw [List.range_succ, List.foldlM_append] at hrun ⊢
      rw [queried_bind]
      rw [evalWithAnswerFn_bind] at hrun
      rcases hs : evalWithAnswerFn answers ((List.range n).foldlM (outerStepP sig pads index coord bucket)
          (some (v0, u0))) with _ | ⟨w, u'⟩
      · rw [hs] at hrun; simp [outerStepP] at hrun
      try rw [hs] at hrun
      simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hrun ⊢
      by_cases hu : u' < 115
      · rw [outerStepP_some_lt _ _ _ _ _ _ _ _ hu] at hrun ⊢
        rw [queried_bind, nodeHashP_eq_shortHash, queried_shortHash, pad64_nodeInputP, queried_pure,
          List.append_nil]
        rw [evalWithAnswerFn_bind, nodeHashP_eq_shortHash, eval_shortHash_out _ _ (pad64_nodeInputP ..)] at hrun
        simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rw [show 7 + (n + 1) = 7 + n + 1 by omega, honL] at hv
        have hdiv : bucket / 2 ^ (n + 1) = bucket / 2 ^ n / 2 := by rw [pow_succ, Nat.div_div_eq_div_mul]
        have hB : bucket / 2 ^ (n + 1) < 2 ^ (11 - (7 + n + 1)) := by
          have : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
          rcases this with rfl | rfl | rfl | rfl <;> simp <;> omega
        by_cases heq : nodeInputP 10 coord index (2 ^ (11 - (7 + n + 1)) + bucket / 2 ^ (n + 1))
              (if bucket / 2 ^ n % 2 = 0 then w else sig.proof ⟨u', hu⟩) (pads.fold ⟨u', hu⟩)
              (if bucket / 2 ^ n % 2 = 0 then sig.proof ⟨u', hu⟩ else w) =
            honInputL answers index coord secret (7 + n + 1) (bucket / 2 ^ (n + 1))
        · obtain ⟨hlft, -, -, hrgt⟩ := nodeInputP_fields heq
          have hw : w = honL answers index coord secret (7 + n) (bucket / 2 ^ n) := by
            rcases Nat.mod_two_eq_zero_or_one (bucket / 2 ^ n) with h0 | h0
            · simp only [h0, if_true] at hlft
              rw [hlft]; congr 1; omega
            · simp only [h0, if_false, show (1 : Nat) ≠ 0 by decide] at hrgt
              rw [hrgt]; congr 1; omega
          rcases ih (by omega) w u' hs hw with ⟨hv0, a⟩ | t
          · left
            refine ⟨hv0, allHonest_append a ?_⟩
            intro q hq
            rw [List.mem_singleton] at hq
            exact ⟨7 + n + 1, bucket / 2 ^ (n + 1), by omega, hB, by rw [hq, heq]⟩
          · right
            exact treeHit_mono t fun q hq => List.mem_append_left _ hq
        · right
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), 7 + n + 1, bucket / 2 ^ (n + 1),
            by omega, hB, ⟨heq, hv⟩, sameHeader_nodeInputP ..⟩
      · rw [show outerStepP sig pads index coord bucket (some (w, u')) n = pure none by
          unfold outerStepP; simp only [dif_neg hu]] at hrun
        simp at hrun
def coordValues (sig : Signature) (coord : Nat) : List Digest :=
  (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)
end SigGolfCandidate.T3M.FtsExtract
