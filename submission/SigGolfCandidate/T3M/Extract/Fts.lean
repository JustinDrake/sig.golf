import SigGolfCandidate.T3M.Witness.Queries
import SigGolfCandidate.T3M.Witness.Shaped
import SigGolfCandidate.T3M.Extract.Basic

/-! # Padded FTS / BPORS extraction (stream PEX-F)

Backward first-divergence extraction for the FTS part of the byte verifier. By `verifyP_normal`
(Witness/Skeleton) every accepting run of `verifyP` computes its FTS as `recoverFtsP sig pads index chosen`
(the stream decoded by `witDecP`/`padDecP`, exact program equality), so the extraction is stated for
`recoverChildP` / `recoverFtsP` with **arbitrary** signature fields and pads.

The honest reference is positional: `honL … level node` is the honest value of node `(level, node)` of the
coordinate tree `(index, coord)` (Core's `treeValue (buildFts index coord).1`, `honL_built`), and
`honInputL … level node` its honest input (zero pads, header heap `2^(11-level) + node`, or leaf `node` at level
0). Every hit is against the honest input **at the actual query's own header position**, so a reference parser
can recover it from the actual input alone.

If the run reaches the honest value, then either some issued query is a distinct-input `HashHit` against the
honest input at its position, or every issued query *is* an honest input (zero leaf/fold pads, honest siblings)
and every selected leaf carries its honest secret. -/
namespace SigGolfCandidate.T3M.FtsExtract
open OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open Correctness (Answers treeValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-! ## The honest coordinate tree -/

/-- The 128-bit output of a public query. -/
def out (answers : Answers) (input : HashInput) : Digest := (answers (.inl (.inr input))).extractLsb' 0 128

/-- Honest value of node `(level, node)` of the coordinate tree `(index, coord)` with leaf secrets `secret`. -/
def honL (answers : Answers) (index coord : Nat) (secret : Nat → Digest) : Nat → Nat → Digest
  | 0, node => out answers (ftsLeafInputP index coord node 0 (secret node) 0)
  | level + 1, node => out answers (nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
      (honL answers index coord secret level (2 * node)) 0 (honL answers index coord secret level (2 * node + 1)))

/-- Honest input of node `(level, node)`: Core's `ftsLeaf` / `nodeHash` query (zero pads). -/
def honInputL (answers : Answers) (index coord : Nat) (secret : Nat → Digest) : Nat → Nat → HashInput
  | 0, node => ftsLeafInputP index coord node 0 (secret node) 0
  | level + 1, node => nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
      (honL answers index coord secret level (2 * node)) 0 (honL answers index coord secret level (2 * node + 1))

theorem honL_eq (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (level node : Nat) :
    honL answers index coord secret level node = out answers (honInputL answers index coord secret level node) := by
  cases level <;> rfl

theorem eval_shortHash_out (answers : Answers) (input : HashInput) (h : pad64 input = input) :
    evalWithAnswerFn answers (shortHash input) = out answers input := by
  rw [eval_shortHash, h]; rfl

/-- **Bridge to Core**: the honest tree is the tree `buildFts` stores. -/
theorem honL_built (answers : Answers) (index coord : Nat) : ∀ level node, level ≤ 11 → node < 2 ^ (11 - level) →
    honL answers index coord (fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0) level node =
      treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level node := by
  have ht := Correctness.eval_buildFts_correct answers index coord
  intro level
  induction level with
  | zero =>
      intro node _ hn
      rw [ht.2.2.1 node (by simpa using hn), ftsLeaf_eq_shortHash, eval_shortHash_out _ _ (pad64_ftsLeafInputP ..)]
      rfl
  | succ level ih =>
      intro node hl hn
      have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
        rw [← pow_succ']; congr 1; omega
      rw [ht.2.2.2 level (by omega) node hn, nodeHash_eq_shortHash, eval_shortHash_out _ _ (pad64_nodeInputP ..),
        ← ih (2 * node) (by omega) (by omega), ← ih (2 * node + 1) (by omega) (by omega)]
      rfl


/-! ## One subtree: `recoverChildP` -/

/-- No hit on a query list: every query is the honest input at a position of the coordinate tree. -/
def AllHonest (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (qs : List Spec.Domain) : Prop :=
  ∀ q ∈ qs, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ q = .inl (.inr (honInputL answers index coord secret l n))

/-- A query of the list is a distinct-input hit on the honest input of a position of the coordinate tree. -/
def TreeHit (answers : Answers) (index coord : Nat) (secret : Nat → Digest) (qs : List Spec.Domain) : Prop :=
  ∃ actual, .inl (.inr actual) ∈ qs ∧
    ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ HashHit answers (honInputL answers index coord secret l n) actual ∧
      Extract.SameHeader actual (honInputL answers index coord secret l n)

theorem hdrBlock_append {a b : HashInput} (c : HashInput) (ha : a.length = 16) (hb : b.length = 16) :
    Extract.hdrBlock (a ++ b ++ c) = b := by
  unfold Extract.hdrBlock
  rw [List.append_assoc, List.drop_left' ha, List.take_left' hb]

theorem hdrBlock_block4 (a b c d : Digest) : Extract.hdrBlock (block4 a b c d) = bytesLE 16 b := by
  unfold block4
  rw [List.append_assoc (bytesLE 16 a ++ bytesLE 16 b), hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _)]

theorem sameHeader_ftsLeafInputP (index coord leaf : Nat) (a b c a' b' c' : Digest) :
    Extract.SameHeader (ftsLeafInputP index coord leaf a b c) (ftsLeafInputP index coord leaf a' b' c') := by
  unfold Extract.SameHeader ftsLeafInputP
  rw [hdrBlock_block4, hdrBlock_block4]

theorem sameHeader_nodeInputP (tag lay tree heap : Nat) (a b c a' b' c' : Digest) :
    Extract.SameHeader (nodeInputP tag lay tree heap a b c) (nodeInputP tag lay tree heap a' b' c') := by
  unfold Extract.SameHeader nodeInputP
  rw [hdrBlock_block4, hdrBlock_block4]

/-- The selected leaves below `(level, node)` carry their honest secrets with zero leaf pads (slot
`3 coord + idxOf g` hashes the leaf pads `s`, `s + 1`). -/
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

/-- **Subtree extraction**: a padded subtree run of Core's DFS reaching the honest node value either contains a
distinct-input hit at its own position or is honest: all its queries are honest inputs and its selected leaves
carry the honest secrets with zero pads. -/
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

/-! ## The four outer folds -/

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

/-! ## One coordinate -/

/-- The secrets list of coordinate `coord` in `recoverFtsP`. -/
def coordValues (sig : Signature) (coord : Nat) : List Digest :=
  (List.range 3).map (fun j => sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩)

/-- **Coordinate extraction**: one coordinate step of `recoverFtsP` appends its root; if that root is the honest
coordinate root, the step's queries are all honest and its selected leaves honest, or one of them is a hit. -/
theorem ftsStepP_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (secret : Nat → Digest) (R : List Digest) (u coord : Nat)
    (hb : (chosen.getD coord ⟨0, []⟩).bucket < 16) (R' : List Digest) (u' : Nat)
    (hrun : evalWithAnswerFn answers (ftsStepP sig pads index chosen (some (R, u)) coord) = some (R', u')) :
    ∃ root, R' = R ++ [root] ∧ (root = honL answers index coord secret 11 0 →
      (AllHonest answers index coord secret (queried answers (ftsStepP sig pads index chosen (some (R, u)) coord)) ∧
        LeavesHonest coord (selectedLeaves (chosen.getD coord ⟨0, []⟩)) (coordValues sig coord) pads secret 7
          (chosen.getD coord ⟨0, []⟩).bucket) ∨
      TreeHit answers index coord secret (queried answers (ftsStepP sig pads index chosen (some (R, u)) coord))) := by
  rw [ftsStepP_some] at hrun ⊢
  rw [evalWithAnswerFn_bind] at hrun
  rcases h1 : evalWithAnswerFn answers (recoverChildP index coord (selectedLeaves (chosen.getD coord ⟨0, []⟩))
      (coordValues sig coord) sig.proof pads 7 (chosen.getD coord ⟨0, []⟩).bucket u) with _ | ⟨value, next⟩
  · simp only [coordValues] at h1; rw [h1] at hrun; simp at hrun
  simp only [coordValues] at h1
  rw [h1] at hrun
  dsimp only at hrun
  rw [evalWithAnswerFn_bind] at hrun
  rcases h2 : evalWithAnswerFn answers ((List.range 4).foldlM
      (outerStepP sig pads index coord (chosen.getD coord ⟨0, []⟩).bucket) (some (value, next))) with _ | ⟨root, n2⟩
  · rw [h2] at hrun; simp at hrun
  rw [h2] at hrun
  simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  refine ⟨root, rfl, fun hroot => ?_⟩
  rw [queried_bind, h1]
  dsimp only
  rw [queried_bind, h2]
  dsimp only
  rw [queried_pure, List.append_nil]
  have hv : root = honL answers index coord secret (7 + 4) ((chosen.getD coord ⟨0, []⟩).bucket / 2 ^ 4) := by
    rw [Nat.div_eq_of_lt (by simpa using hb)]; exact hroot
  rcases outer_extract answers sig pads index coord _ secret hb value next 4 (le_refl _) root n2 h2 hv with
    ⟨hv0, a2⟩ | t2
  · rcases recoverChildP_extract answers index coord _ _ sig.proof pads secret 7 _ u value next (by decide)
        (by simpa using hb) h1 hv0 with ⟨a1, l1⟩ | t1
    · left
      exact ⟨allHonest_append a1 a2, l1⟩
    · right
      exact treeHit_mono t1 fun q hq => List.mem_append_left _ hq
  · right
    exact treeHit_mono t2 fun q hq => List.mem_append_right _ hq

/-! ## Seven coordinates -/

/-- The coordinate runs of the seven-coordinate fold: per-coordinate pointers `us`, each step appending the next
root, and the fold's queries exactly the steps' queries in order. -/
theorem ftsFold_runs (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat) (chosen : List Selection)
    (secret : Nat → Nat → Digest) : ∀ n (roots : List Digest) (used : Nat),
      (∀ c < n, (chosen.getD c ⟨0, []⟩).bucket < 16) →
      evalWithAnswerFn answers ((List.range n).foldlM (ftsStepP sig pads index chosen) (some ([], 0))) =
        some (roots, used) →
      roots.length = n ∧ ∃ us : Nat → Nat, us n = used ∧
        (∀ c < n, evalWithAnswerFn answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c) =
          some (roots.take (c + 1), us (c + 1))) ∧
        queried answers ((List.range n).foldlM (ftsStepP sig pads index chosen) (some ([], 0))) =
          (List.range n).flatMap (fun c =>
            queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) := by
  intro n
  induction n with
  | zero =>
      intro roots used _ hrun
      simp only [List.range_zero, List.foldlM_nil, evalWithAnswerFn_pure, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨rfl, fun _ => 0, rfl, fun c hc => by omega, by simp⟩
  | succ n ih =>
      intro roots used hb hrun
      rw [List.range_succ, List.foldlM_append] at hrun ⊢
      rw [queried_bind]
      rw [evalWithAnswerFn_bind] at hrun
      rcases hs : evalWithAnswerFn answers ((List.range n).foldlM (ftsStepP sig pads index chosen)
          (some ([], 0))) with _ | ⟨R, u⟩
      · rw [hs] at hrun; simp [ftsStepP] at hrun
      try rw [hs] at hrun
      simp only [List.foldlM_cons, List.foldlM_nil, bind_pure] at hrun ⊢
      obtain ⟨hlen, us, hus, hsteps, hq⟩ := ih R u (fun c hc => hb c (by omega)) hs
      obtain ⟨root, rfl, -⟩ := ftsStepP_extract answers sig pads index chosen (secret n) R u n (hb n (by omega))
        roots used hrun
      have htake : ∀ c, c ≤ n → (R ++ [root]).take c = R.take c := fun c hc =>
        List.take_append_of_le_length (by omega)
      refine ⟨by simp [hlen], fun c => if c = n + 1 then used else us c, by simp, fun c hc => ?_, ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc | rfl
        · dsimp only
          rw [htake c (by omega), htake (c + 1) (by omega), if_neg (by omega), if_neg (by omega)]
          exact hsteps c hc
        · dsimp only
          have e1 : R.take c = R := List.take_of_length_le (by omega)
          have e2 : (R ++ [root]).take (c + 1) = R ++ [root] := List.take_of_length_le (by simp; omega)
          rw [htake c le_rfl, if_neg (by omega), if_pos rfl, hus, e1, e2]
          exact hrun
      · dsimp only
        have e1 : R.take n = R := List.take_of_length_le (by omega)
        rw [hq, List.flatMap_append, List.flatMap_singleton, htake n le_rfl, if_neg (by omega), hus, e1]
        congr 1
        apply List.flatMap_congr
        intro c hc
        have hc := List.mem_range.mp hc
        rw [htake c (by omega), if_neg (by omega)]

/-! ## The forest public key and the whole FTS -/

theorem forestPk_eq_shortHash (index : Nat) (roots : List Digest) :
    forestPk index roots = shortHash (Extract.forestInput index roots) := rfl

theorem sameHeader_forest (index : Nat) (roots roots' : List Digest) :
    Extract.SameHeader (pad64 (Extract.forestInput index roots)) (pad64 (Extract.forestInput index roots')) := by
  unfold Extract.SameHeader Extract.forestInput Extract.listInput pad64
  rw [List.append_assoc _ _ (List.replicate _ 0), List.append_assoc _ _ (List.replicate _ 0),
    hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _),
    hdrBlock_append _ (bytesLE_length _ _) (bytesLE_length _ _)]

/-- The honest coordinate roots of index `index`. -/
def honRoots (answers : Answers) (index : Nat) (secret : Nat → Nat → Digest) : List Digest :=
  (List.range 7).map fun c => honL answers index c (secret c) 11 0

theorem flatMap_bytesLE_length (l : List Digest) : (l.flatMap (bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, bytesLE_length, ih, List.length_cons]; ring

theorem flatMap_bytesLE_injective : ∀ (l l' : List Digest), l.length = l'.length →
    l.flatMap (bytesLE 16) = l'.flatMap (bytesLE 16) → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, a' :: l', h, he => by
      simp only [List.flatMap_cons] at he
      obtain ⟨ha, hl⟩ := List.append_inj he (by simp only [bytesLE_length])
      rw [bytesLE_injective ha, flatMap_bytesLE_injective l l' (by simpa using h) hl]

theorem pad64_injective_of_length {x y : HashInput} (hl : x.length = y.length) (h : pad64 x = pad64 y) : x = y := by
  unfold pad64 at h
  rw [hl] at h
  exact (List.append_inj h hl).1

theorem forestInput_injective {index : Nat} {roots roots' : List Digest} (hl : roots.length = 7)
    (hl' : roots'.length = 7) (h : pad64 (Extract.forestInput index roots) = pad64 (Extract.forestInput index roots')) :
    roots = roots' := by
  have hlen : (Extract.forestInput index roots).length = (Extract.forestInput index roots').length := by
    simp only [Extract.forestInput, Extract.listInput, List.length_append, bytesLE_length, flatMap_bytesLE_length, List.length_drop, hl, hl']
  have h := pad64_injective_of_length hlen h
  unfold Extract.forestInput Extract.listInput at h
  obtain ⟨h12, h3⟩ := List.append_inj h (by simp only [List.length_append, bytesLE_length])
  obtain ⟨h1, -⟩ := List.append_inj h12 (by simp only [bytesLE_length])
  have hd := flatMap_bytesLE_injective _ _ (by simp only [List.length_drop, hl, hl']) h3
  have h0 := bytesLE_injective h1
  rcases roots with _ | ⟨a, t⟩
  · simp at hl
  rcases roots' with _ | ⟨a', t'⟩
  · simp at hl'
  simp only [List.getD_cons_zero] at h0
  simp only [List.drop_succ_cons, List.drop_zero] at hd
  rw [h0, hd]

/-- **FTS extraction** for Core's padded FTS `recoverFtsP` with arbitrary signature fields and pads (the
FTS of every accepting `verifyP` run, by `verifyP_normal`): if it returns the honest forest pk of `index`,
then either every query it issued is an honest input (the honest forest input or an honest node/leaf input of a
coordinate tree, at its own position) and every selected leaf carries its honest secret with zero leaf pads, or
some issued query is a distinct-input `HashHit` on the honest input at its position. -/
theorem recoverFtsP_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (secret : Nat → Nat → Digest) (v : Digest)
    (hb : ∀ c < 7, (chosen.getD c ⟨0, []⟩).bucket < 16)
    (hrun : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some v)
    (hroot : v = evalWithAnswerFn answers (forestPk index (honRoots answers index secret))) :
    ((∀ q ∈ queried answers (recoverFtsP sig pads index chosen),
        q = .inl (.inr (pad64 (Extract.forestInput index (honRoots answers index secret)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ q = .inl (.inr (honInputL answers index c (secret c) l n))) ∧
      ∀ c < 7, LeavesHonest c (selectedLeaves (chosen.getD c ⟨0, []⟩)) (coordValues sig c) pads (secret c) 7
        (chosen.getD c ⟨0, []⟩).bucket) ∨
    ∃ actual, .inl (.inr actual) ∈ queried answers (recoverFtsP sig pads index chosen) ∧
      ((HashHit answers (pad64 (Extract.forestInput index (honRoots answers index secret))) actual ∧
          Extract.SameHeader actual (pad64 (Extract.forestInput index (honRoots answers index secret)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧ HashHit answers (honInputL answers index c (secret c) l n) actual ∧
          Extract.SameHeader actual (honInputL answers index c (secret c) l n)) := by
  rw [recoverFtsP_eq] at hrun ⊢
  rw [queried_bind]
  rw [evalWithAnswerFn_bind] at hrun
  rcases hs : evalWithAnswerFn answers ((List.range 7).foldlM (ftsStepP sig pads index chosen) (some ([], 0)))
    with _ | ⟨roots, used⟩
  · rw [hs] at hrun; simp at hrun
  try rw [hs] at hrun
  dsimp only at hrun ⊢
  by_cases hz : (!(List.range (115 - used)).all (fun j =>
      decide (sig.proof ⟨(used + j) % 115, Nat.mod_lt _ (by decide)⟩ = 0))) = true
  · rw [if_pos hz] at hrun; simp at hrun
  rw [if_neg hz] at hrun ⊢
  rw [queried_bind, forestPk_eq_shortHash, queried_shortHash, queried_pure, List.append_nil]
  rw [evalWithAnswerFn_bind, forestPk_eq_shortHash, eval_shortHash] at hrun
  simp only [evalWithAnswerFn_pure, Option.some.injEq] at hrun
  rw [forestPk_eq_shortHash, eval_shortHash] at hroot
  obtain ⟨hlen, us, -, hsteps, hq⟩ := ftsFold_runs answers sig pads index chosen secret 7 roots used hb hs
  rw [hq]
  by_cases heq : pad64 (Extract.forestInput index roots) = pad64 (Extract.forestInput index (honRoots answers index secret))
  · have hR : roots = honRoots answers index secret :=
      forestInput_injective hlen (by simp [honRoots]) heq
    have hcoord : ∀ c < 7,
        (AllHonest answers index c (secret c)
            (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) ∧
          LeavesHonest c (selectedLeaves (chosen.getD c ⟨0, []⟩)) (coordValues sig c) pads (secret c) 7
            (chosen.getD c ⟨0, []⟩).bucket) ∨
        TreeHit answers index c (secret c)
          (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c)) := by
      intro c hc
      obtain ⟨root, hrt, himp⟩ := ftsStepP_extract answers sig pads index chosen (secret c) (roots.take c) (us c) c
        (hb c hc) _ _ (hsteps c hc)
      apply himp
      have h1 : (roots.take (c + 1)).getD c 0 = roots.getD c 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]; try simp
      have h2 : (roots.take c ++ [root]).getD c 0 = root := by
        rw [List.getD_append_right _ _ _ _ (by simp only [List.length_take]; omega)]
        simp [show c - min c roots.length = 0 by omega]
      rw [← h2, ← hrt, h1, hR]
      simp [honRoots, hc]
    by_cases hhit : ∃ c < 7, TreeHit answers index c (secret c)
        (queried answers (ftsStepP sig pads index chosen (some (roots.take c, us c)) c))
    · right
      obtain ⟨c, hc, actual, hmem, l, n, hl, hn, hh, hsh⟩ := hhit
      exact ⟨actual, List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hmem⟩),
        Or.inr ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
    · left
      have hall : ∀ c < 7, _ := fun c hc => (hcoord c hc).resolve_right fun ht => hhit ⟨c, hc, ht⟩
      refine ⟨fun q hq => ?_, fun c hc => (hall c hc).2⟩
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨c, hc, hmem⟩ := List.mem_flatMap.mp hq
        have hc := List.mem_range.mp hc
        exact Or.inr ⟨c, hc, (hall c hc).1 q hmem⟩
      · rw [List.mem_singleton] at hq
        exact Or.inl (by rw [hq, hR])
  · right
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), Or.inl ⟨⟨heq, hrun.trans hroot⟩, sameHeader_forest ..⟩⟩

/-! ## Machine-accepted selections and Core's built trees -/

/-- On a selection the machine accepts, the honest-leaves clause names the three opened secrets
`sig.secrets (3 coord + j)` and the leaf pads `P_{3 coord + j}`, `P_{3 coord + j + 1}`. -/
theorem leavesHonest_selOk (sig : Signature) (pads : Pads) (secret : Nat → Digest) (coord : Nat) (sel : Selection)
    (hs : SelOk sel) (h : LeavesHonest coord (selectedLeaves sel) (coordValues sig coord) pads secret 7 sel.bucket) :
    ∀ j < 3, sig.secrets ⟨(coord * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ = secret (selLeaf sel j) ∧
      pads.leaf ⟨(3 * coord + j) % 22, Nat.mod_lt _ (by decide)⟩ = 0 ∧
      pads.leaf ⟨(3 * coord + j + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0 := by
  intro j hj
  have hsel := hs.selected
  have h01 := hs.s01
  have h12 := hs.s12
  have h2 := hs.l2
  have hb := hs.b
  have e0 : selLeaf sel 0 = sel.bucket * 128 + sel.leaves.getD 0 0 := rfl
  have e1 : selLeaf sel 1 = sel.bucket * 128 + sel.leaves.getD 1 0 := rfl
  have e2 : selLeaf sel 2 = sel.bucket * 128 + sel.leaves.getD 2 0 := rfl
  generalize sel.leaves.getD 0 0 = x0 at h01 e0
  generalize sel.leaves.getD 1 0 = x1 at h01 h12 e1
  generalize sel.leaves.getD 2 0 = x2 at h12 h2 e2
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  have hidx : (selectedLeaves sel).idxOf (selLeaf sel j) = j := by
    rw [hsel, e0, e1, e2]
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2]
    · exact List.idxOf_cons_self
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
    · rw [List.idxOf_cons_ne _ (by omega), List.idxOf_cons_ne _ (by omega), List.idxOf_cons_self]
  have hmem : selLeaf sel j ∈ selectedLeaves sel := by
    rw [hsel]
    rcases hj3 with rfl | rfl | rfl <;> simp
  have hlo : sel.bucket * 2 ^ 7 ≤ selLeaf sel j := by
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega
  have hhi : selLeaf sel j < (sel.bucket + 1) * 2 ^ 7 := by
    rcases hj3 with rfl | rfl | rfl <;> simp only [e0, e1, e2] <;> omega
  obtain ⟨hv, hp0, hp1⟩ := h _ hmem hlo hhi
  simp only [hidx] at hv hp0 hp1
  refine ⟨?_, hp0, hp1⟩
  rw [← hv]
  simp [coordValues, hj]

/-- The honest inputs of the built tree are Core's `buildFts` queries: the zero-pad leaf of the stored secret,
and `nodeHash`'s input on the stored children. -/
theorem honInputL_built (answers : Answers) (index coord : Nat) (level node : Nat) (hl : level < 11)
    (hn : node < 2 ^ (11 - (level + 1))) :
    honInputL answers index coord (fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0)
        (level + 1) node =
      nodeInputP 10 coord index (2 ^ (11 - (level + 1)) + node)
        (treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level (2 * node)) 0
        (treeValue (evalWithAnswerFn answers (buildFts index coord)).1 level (2 * node + 1)) := by
  have h2 : 2 ^ (11 - level) = 2 * 2 ^ (11 - (level + 1)) := by
    rw [← pow_succ']; congr 1; omega
  simp only [honInputL]
  rw [honL_built answers index coord level (2 * node) (by omega) (by omega),
    honL_built answers index coord level (2 * node + 1) (by omega) (by omega)]

/-- The honest secrets of the forest of `index` (Core's `buildFts` secrets). -/
def builtSecret (answers : Answers) (index : Nat) : Nat → Nat → Digest :=
  fun c g => (evalWithAnswerFn answers (buildFts index c)).2.getD g 0

theorem honRoots_built (answers : Answers) (index : Nat) :
    honRoots answers index (builtSecret answers index) =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0 := by
  unfold honRoots
  apply List.map_congr_left
  intro c _
  exact honL_built answers index c 11 0 le_rfl (by decide)

/-- **FTS extraction against Core's forest** (the form for the security owner): a padded FTS run on
machine-accepted selections returning the forest pk Core stores for `index` either issued only honest inputs
(Core's `buildFts` / `forestPk` queries at their own positions) and opened each selected leaf's honest secret
with zero leaf pads, or issued a distinct-input `HashHit` on the honest input at its own position. -/
theorem recoverFtsP_built_extract (answers : Answers) (sig : Signature) (pads : Pads) (index : Nat)
    (chosen : List Selection) (v : Digest) (hc : ChosenOk chosen)
    (hrun : evalWithAnswerFn answers (recoverFtsP sig pads index chosen) = some v)
    (hroot : v = evalWithAnswerFn answers
      (forestPk index ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0))) :
    ((∀ q ∈ queried answers (recoverFtsP sig pads index chosen),
        q = .inl (.inr (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧
          q = .inl (.inr (honInputL answers index c (builtSecret answers index c) l n))) ∧
      ∀ c < 7, ∀ j < 3,
        sig.secrets ⟨(c * 3 + j) % 21, Nat.mod_lt _ (by decide)⟩ =
          builtSecret answers index c (selLeaf (chosen.getD c ⟨0, []⟩) j) ∧
        pads.leaf ⟨(3 * c + j) % 22, Nat.mod_lt _ (by decide)⟩ = 0 ∧
        pads.leaf ⟨(3 * c + j + 1) % 22, Nat.mod_lt _ (by decide)⟩ = 0) ∨
    ∃ actual, .inl (.inr actual) ∈ queried answers (recoverFtsP sig pads index chosen) ∧
      ((HashHit answers (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0))) actual ∧
        Extract.SameHeader actual (pad64 (Extract.forestInput index
          ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)))) ∨
        ∃ c < 7, ∃ l n, l ≤ 11 ∧ n < 2 ^ (11 - l) ∧
          HashHit answers (honInputL answers index c (builtSecret answers index c) l n) actual ∧
          Extract.SameHeader actual (honInputL answers index c (builtSecret answers index c) l n)) := by
  have h := recoverFtsP_extract answers sig pads index chosen (builtSecret answers index) v
    (fun c hc' => (hc c hc').b) hrun (by rw [honRoots_built]; exact hroot)
  rw [honRoots_built] at h
  rcases h with ⟨hq, hl⟩ | hhit
  · exact Or.inl ⟨hq, fun c hc' => leavesHonest_selOk sig pads (builtSecret answers index c) c _ (hc c hc') (hl c hc')⟩
  · exact Or.inr hhit

/-! ## PEX-L's interface (`FtsExtractSpecN`, shared `Extract.Basic` vocabulary) -/

theorem honestInput_forest (answers : Answers) (index : Nat) :
    Extract.honestInput answers (.forest index) = pad64 (Extract.forestInput index
      ((List.range 7).map fun c => treeValue (evalWithAnswerFn answers (buildFts index c)).1 11 0)) := rfl

theorem honestInput_ftsLeaf (answers : Answers) (index coord leaf : Nat) :
    Extract.honestInput answers (.ftsLeaf index coord leaf) =
      honInputL answers index coord (builtSecret answers index coord) 0 leaf := by
  simp only [Extract.honestInput, pad64_ftsLeafInputP]; rfl

theorem honestInput_ftsNode (answers : Answers) (index coord level node : Nat) (hl : level < 11)
    (hn : node < 2 ^ (11 - (level + 1))) :
    Extract.honestInput answers (.ftsNode index coord level node) =
      honInputL answers index coord (builtSecret answers index coord) (level + 1) node := by
  rw [show builtSecret answers index coord = fun g => (evalWithAnswerFn answers (buildFts index coord)).2.getD g 0 from rfl,
    honInputL_built answers index coord level node hl hn]
  simp only [Extract.honestInput, pad64_nodeInputP, Nat.sub_sub]; rfl

/-- The honest input at a tree position is a `Pos` reference input (`ftsLeaf` at level 0, `ftsNode` above). -/
theorem honInputL_pos (answers : Answers) (index coord l n : Nat) (hl : l ≤ 11) (hn : n < 2 ^ (11 - l)) :
    (n < 2048 ∧ honInputL answers index coord (builtSecret answers index coord) l n =
        Extract.honestInput answers (.ftsLeaf index coord n) ∧ l = 0) ∨
      ∃ level, l = level + 1 ∧ level < 11 ∧ n < 2 ^ (11 - (level + 1)) ∧
        honInputL answers index coord (builtSecret answers index coord) l n =
          Extract.honestInput answers (.ftsNode index coord level n) := by
  cases l with
  | zero => exact Or.inl ⟨by simpa using hn, (honestInput_ftsLeaf ..).symm, rfl⟩
  | succ level => exact Or.inr ⟨level, rfl, by omega, hn, (honestInput_ftsNode answers index coord level n (by omega) hn).symm⟩

/-- PEX-F's honest-shaped FTS part of a shaped witness: every query of the FTS is an honest reference input of the
forest of its index (the forest pk, an FTS leaf or an FTS node), and the 21 opened secrets are the honest secrets of
the selected leaves, with zero leaf pads on both sides. -/
def FtsShaped (answers : Answers) (N : HashOutput) (w : WBytes) : Prop :=
  (∀ q ∈ queried answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)),
      q = .inl (.inr (Extract.honestInput answers (.forest (N.toNat % 2 ^ 31)))) ∨
      ∃ c < 7, (∃ leaf < 2048, q = .inl (.inr (Extract.honestInput answers (.ftsLeaf (N.toNat % 2 ^ 31) c leaf)))) ∨
        ∃ level < 11, ∃ node < 2 ^ (11 - (level + 1)),
          q = .inl (.inr (Extract.honestInput answers (.ftsNode (N.toNat % 2 ^ 31) c level node)))) ∧
  ∀ c < 7, ∀ j < 3,
    wsecret w (3 * c + j) = Extract.ftsSecret answers (N.toNat % 2 ^ 31) c (selLeaf ((selections N).getD c ⟨0, []⟩) j) ∧
    wleafPad w (3 * c + j) = 0 ∧ wleafPad w (3 * c + j + 1) = 0

/-- **PEX-F's obligation** (`FtsExtractSpecN FtsShaped` of PEX-L's `Extract/VerifyP.lean`, unfolded): on a
shaped stream, the padded FTS `recoverFtsP` on the decoded signature and pads reaching the honest forest pk gives
a header-preserving hit among its actual queries or the honest-shaped FTS part. -/
theorem ftsExtractSpecN_holds (answers : Answers) (N : HashOutput) (w : WBytes) (hS : Shaped N w)
    (hrun : evalWithAnswerFn answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (Extract.honestForest answers (N.toNat % 2 ^ 31))) :
    Extract.HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))) ∨
      FtsShaped answers N w := by
  have h := recoverFtsP_built_extract answers (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31)
    (selections N) _ (chosenOk_of N hS.1) hrun rfl
  rcases h with ⟨hq, hl⟩ | ⟨actual, hmem, ⟨hh, hsh⟩ | ⟨c, hc, l, n, hl, hn, hh, hsh⟩⟩
  · right
    refine ⟨fun q hq' => ?_, fun c hc j hj => ?_⟩
    · rcases hq q hq' with hf | ⟨c, hc, l, n, hl, hn, rfl⟩
      · exact Or.inl (by rw [hf, honestInput_forest])
      · refine Or.inr ⟨c, hc, ?_⟩
        rcases honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
        · exact Or.inl ⟨n, hn', by rw [he]⟩
        · exact Or.inr ⟨level, hlev, n, hn', by rw [he]⟩
    · obtain ⟨hs, hp0, hp1⟩ := hl c hc j hj
      have m21 : (c * 3 + j) % 21 = 3 * c + j := by rw [Nat.mod_eq_of_lt (by omega)]; ring
      have m22 : (3 * c + j) % 22 = 3 * c + j := Nat.mod_eq_of_lt (by omega)
      have m22' : (3 * c + j + 1) % 22 = 3 * c + j + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [witDecP, padDecP, m21, m22, m22'] at hs hp0 hp1
      exact ⟨hs, hp0, hp1⟩
  · left
    have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
    exact ⟨.forest _, actual, hidx, hmem, by rw [honestInput_forest]; exact hh, by rw [honestInput_forest]; exact hsh⟩
  · left
    have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
    rcases honInputL_pos answers _ c l n hl hn with ⟨hn', he, -⟩ | ⟨level, -, hlev, hn', he⟩
    · exact ⟨.ftsLeaf _ c n, actual, ⟨by omega, hidx, by omega⟩, hmem, by rw [← he]; exact hh,
        by rw [← he]; exact hsh⟩
    · exact ⟨.ftsNode _ c level n, actual, ⟨by omega, hidx, hlev, by simpa only [Nat.sub_sub] using hn'⟩, hmem,
        by rw [← he]; exact hh, by rw [← he]; exact hsh⟩

end SigGolfCandidate.T3M.FtsExtract
