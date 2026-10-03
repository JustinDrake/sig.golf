import SigGolfCandidate.T3M.Extract.Layers
import SigGolfCandidate.T3M.Witness.Skeleton

/-! # Top-level padded structural extraction of `verifyP` (stream PEX-L)

`verifyP_extract`: under an answers table, an accepting byte verification against the honest public key
(`honestRoot answers 0 0`, which is `keygen`'s public key: `keygen_pk`) gives the digest query and, for its
index `N % 2^31`:
* a header-preserving `HitIn` among `verifyP`'s actual queries, or
* a WOTS/encoding divergence (`Diverge`) at a layer below `Good` layers, or
* all four layers `Good` and the FTS part `FtsShaped` (PEX-F's predicate, through `FtsExtractSpec`). -/
namespace SigGolfCandidate.T3M.Extract
open OracleComp OracleSpec SigGolfCandidate.T3 SecurityInputs SecurityExtraction
open Correctness (Answers treeValue builtTree)
open SphincsSecurity (bytesLE)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

/-- **PEX-F's obligation**: the seven-coordinate stream loop reaching the honest FTS roots (with the pointer cap
passed) gives a hit among its own actual queries, or an honest-shaped FTS part `FtsShaped`. -/
def FtsExtractSpec (FtsShaped : Answers → WBytes → Nat → List Selection → Prop) : Prop :=
  ∀ (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection) (ptr : Nat),
    selectionsOk chosen = true → ptr ≤ streamEnd →
    evalWithAnswerFn answers (ftsRoots w index chosen) = some (ftsRootsHonest answers index, ptr) →
    HitIn answers (queried answers (ftsRoots w index chosen)) ∨ FtsShaped answers w index chosen

theorem queried_map {α β : Type} (answers : Answers) (f : α → β) (p : M α) :
    queried answers (f <$> p) = queried answers p := by
  rw [map_eq_bind_pure_comp, queried_bind]
  simp

/-- The stream loop returns seven roots. -/
theorem ftsRoots_length (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (ptr : Nat) (h : evalWithAnswerFn answers (ftsRoots w index chosen) = some (roots, ptr)) :
    roots.length = 7 := by
  unfold ftsRoots at h
  revert roots ptr
  refine Correctness.eval_foldlM_range_inv (Inv := fun i (state : Option (List Digest × Nat)) =>
    ∀ roots ptr, state = some (roots, ptr) → roots.length = i) answers 7 _ _ ?_ ?_
  · intro roots ptr h
    cases h
    rfl
  · intro i _ state hstate
    rcases state with _ | ⟨roots, ptr⟩
    · intro roots ptr h
      simp at h
    · intro roots' ptr' h
      simp only [evalWithAnswerFn_bind] at h
      generalize evalWithAnswerFn answers (ftsCoordP w index i (chosen.getD i ⟨0, []⟩) ptr) = r at h
      rcases r with _ | ⟨root, ptr''⟩
      · simp at h
      · simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hstate roots ptr rfl]

theorem ftsP_queried_roots (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection) :
    ∀ q ∈ queried answers (ftsRoots w index chosen), q ∈ queried answers (ftsP w index chosen) := by
  intro q hq
  rw [ftsP_eq, queried_bind]
  exact List.mem_append_left _ hq

theorem ftsP_queried_forest (answers : Answers) (w : WBytes) (index : Nat) (chosen : List Selection)
    (roots : List Digest) (ptr : Nat) (h : evalWithAnswerFn answers (ftsRoots w index chosen) = some (roots, ptr))
    (hcap : ¬ streamEnd < ptr) :
    ∀ q ∈ queried answers (forestPk index roots), q ∈ queried answers (ftsP w index chosen) := by
  intro q hq
  rw [ftsP_eq, queried_bind, h]
  simp only
  rw [if_neg hcap, queried_bind]
  exact List.mem_append_right _ (List.mem_append_left _ hq)

/-- `keygen`'s public key is the honest root of the top tree. -/
theorem keygen_pk (answers : Answers) : (evalWithAnswerFn answers keygen).1 = honestRoot answers 0 0 := by
  unfold keygen keygenPayload
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [Correctness.eval_buildTree_levels answers 0 0 0 [] (Cost.validDigits_nil 0)]
  rfl

/-- **The walk through `verifyP`**: the digest query, the selection check, and the hit / divergence / all-`Good`
trichotomy, the last case leaving the FTS part `ftsP` evaluated to the honest forest pk. -/
theorem verifyP_walk_extract (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧
          evalWithAnswerFn answers (ftsP w (N.toNat % 2 ^ 31) (selections N)) =
            some (honestForest answers (N.toNat % 2 ^ 31)) ∧
          ∀ q ∈ queried answers (ftsP w (N.toNat % 2 ^ 31) (selections N)),
            q ∈ queried answers (verifyP m pk w))) := by
  classical
  rw [verifyP_eq_tail] at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  -- the digest
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · have h0 : digestP m w = pure none := by unfold digestP; rw [if_pos hdc]
    rw [h0] at hv; simp at hv
  have hD : digestP m w = some <$> digest (wrho w) m (wdc w) := by unfold digestP; rw [if_neg hdc]
  rw [hD] at hv ⊢
  rw [queried_map]
  simp only [evalWithAnswerFn_map] at hv ⊢
  generalize hN : evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N at hv ⊢
  try simp only at hv ⊢
  refine ⟨N, by omega, rfl, ?_, ?_⟩
  · apply List.mem_append_left
    unfold digest publicHash
    rw [show (liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) : M HashOutput) =
      liftM (Spec.query (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))))) >>= pure from (bind_pure _).symm,
      queried_query_bind]
    exact List.mem_cons_self
  -- the tail
  unfold verifyTailP at hv ⊢
  simp only at hv ⊢
  by_cases hsel : selectionsOk (selections N) = true
  swap
  · rw [if_pos (by simpa using hsel)] at hv; simp at hv
  rw [if_neg (by simpa using hsel)] at hv ⊢
  by_cases hg : digestGate N = true
  swap
  · rw [if_pos (by simpa using hg)] at hv
    simp at hv
  rw [if_neg (by simpa using hg)] at hv ⊢
  refine ⟨hsel, ?_⟩
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 31 := Nat.mod_lt _ (by decide)
  generalize N.toNat % 2 ^ 31 = index at hidx hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hR : evalWithAnswerFn answers (ftsP w index (selections N)) = rr at hv ⊢
  rcases rr with _ | root
  · simp at hv
  simp only at hv ⊢
  rw [evalWithAnswerFn_bind] at hv
  rw [queried_bind]
  generalize hL : evalWithAnswerFn answers (layersP w index 4 (root, 0, 0)) = ll at hv ⊢
  rcases ll with _ | root'
  · simp at hv
  simp only [evalWithAnswerFn_pure, beq_iff_eq] at hv
  subst hv
  -- the hypertree walk
  have htop : (walkTarget answers index 0).1 = root' := by
    rw [hpk]; simp only [walkTarget, route_top_tree index hidx]
  rcases layersP_walk answers w index hidx 4 le_rfl (root, 0, 0) (by rw [hL, htop]) with
    hhit | ⟨lay, _, hdiv, hgood⟩ | ⟨hgood, hroot⟩
  · exact Or.inl (hhit.mono fun q hq => by simp only [List.mem_append]; tauto)
  · exact Or.inr (Or.inl ⟨lay, hdiv.mono fun q hq => by simp only [List.mem_append]; tauto, hgood⟩)
  have hroot' : root = honestForest answers index := by
    have h4 : ((root, 0, 0) : LayerMessage) = walkTarget answers index 4 := by simpa using hroot
    simp [walkTarget, honestMsg] at h4
    exact h4
  exact Or.inr (Or.inr ⟨fun l => hgood l l.isLt, by rw [hroot'],
    fun q hq => by simp only [List.mem_append]; tauto⟩)

/-- **Top-level padded structural extraction**, conditional on an FTS-part extraction stated on the stream loop
`ftsRoots` (`FtsExtractSpec`). -/
theorem verifyP_extract {FtsShaped : Answers → WBytes → Nat → List Selection → Prop}
    (hF : FtsExtractSpec FtsShaped) (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      selectionsOk (selections N) = true ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧
          FtsShaped answers w (N.toNat % 2 ^ 31) (selections N))) := by
  classical
  obtain ⟨N, hdc, hN, hdq, hsel, hcase⟩ := verifyP_walk_extract answers m pk w hpk hv
  refine ⟨N, hdc, hN, hdq, hsel, ?_⟩
  rcases hcase with hhit | hdiv | ⟨hgood, hR, hqV⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  have hidx : N.toNat % 2 ^ 31 < 2 ^ 40 := lt_trans (Nat.mod_lt _ (by decide)) (by norm_num)
  generalize N.toNat % 2 ^ 31 = index at hgood hR hqV hidx ⊢
  have hR' := hR
  rw [ftsP_eq, evalWithAnswerFn_bind] at hR'
  generalize hS : evalWithAnswerFn answers (ftsRoots w index (selections N)) = ss at hR'
  rcases ss with _ | ⟨roots, ptr⟩
  · simp at hR'
  simp only at hR'
  by_cases hcap : streamEnd < ptr
  · rw [if_pos hcap] at hR'; simp at hR'
  rw [if_neg hcap, evalWithAnswerFn_bind] at hR'
  simp only [evalWithAnswerFn_pure, Option.some.injEq] at hR'
  have hqR := ftsP_queried_roots answers w index (selections N)
  have hqF := ftsP_queried_forest answers w index (selections N) roots ptr hS hcap
  rcases forestPk_honest_extract answers index hidx roots
      (ftsRoots_length answers w index (selections N) roots ptr hS) hR' with hroots | hhit
  · subst hroots
    rcases hF answers w index (selections N) ptr hsel (by omega) hS with hhit | hshape
    · exact Or.inl (hhit.mono fun q hq => hqV q (hqR q hq))
    · exact Or.inr (Or.inr ⟨hgood, hshape⟩)
  · exact Or.inl (hhit.mono fun q hq => hqV q (hqF q hq))

/-! ## The normal-form route (PEX-F's `recoverFtsP` extraction) -/

/-- **PEX-F's obligation, normal-form route**: on a shaped stream the FTS part of `verifyP` is Core's
`recoverFtsP` on the decoded signature and pads (`ftsP_shaped`); reaching the honest forest pk gives a hit among
its actual queries or an honest-shaped FTS part `FtsShaped answers N w`. -/
def FtsExtractSpecN (FtsShaped : Answers → HashOutput → WBytes → Prop) : Prop :=
  ∀ (answers : Answers) (N : HashOutput) (w : WBytes), Shaped N w →
    evalWithAnswerFn answers (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N)) =
      some (honestForest answers (N.toNat % 2 ^ 31)) →
    HitIn answers (queried answers
        (recoverFtsP (witDecP N w).signature (padDecP N w) (N.toNat % 2 ^ 31) (selections N))) ∨
      FtsShaped answers N w

/-- `rejectTail` evaluates to `false` under every answers table. -/
theorem eval_rejectTail (answers : Answers) (w : WBytes) (N : HashOutput) :
    evalWithAnswerFn answers (rejectTail w N) = false := by
  unfold rejectTail
  split
  · rfl
  · split
    · rfl
    · rw [evalWithAnswerFn_map]

/-- An accepting run has the honest stream shape for its digest answer. -/
theorem shaped_of_verifyP (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    Shaped (evalWithAnswerFn answers (digest (wrho w) m (wdc w))) w := by
  classical
  rw [verifyP_normal] at hv
  by_cases hdc : (wdc w).toNat ≥ attemptLimit
  · rw [if_pos hdc] at hv; simp at hv
  rw [if_neg hdc, evalWithAnswerFn_bind] at hv
  by_contra hS
  rw [if_neg hS, eval_rejectTail] at hv
  exact Bool.false_ne_true hv

/-- **Top-level padded structural extraction, normal-form route** (conditional on `FtsExtractSpecN`). -/
theorem verifyP_extract_normal {FtsShaped : Answers → HashOutput → WBytes → Prop}
    (hF : FtsExtractSpecN FtsShaped) (answers : Answers) (m : Message) (pk : Digest) (w : WBytes)
    (hpk : pk = honestRoot answers 0 0)
    (hv : evalWithAnswerFn answers (verifyP m pk w) = true) :
    ∃ N : HashOutput, (wdc w).toNat < attemptLimit ∧
      evalWithAnswerFn answers (digest (wrho w) m (wdc w)) = N ∧
      (.inl (.inr (pad64 (digestInput (wrho w) m (wdc w)))) : Spec.Domain) ∈ queried answers (verifyP m pk w) ∧
      Shaped N w ∧
      (HitIn answers (queried answers (verifyP m pk w)) ∨
       (∃ lay : Layer, Diverge answers w (N.toNat % 2 ^ 31) lay (queried answers (verifyP m pk w)) ∧
          ∀ l : Layer, l.val < lay.val → Good answers w (N.toNat % 2 ^ 31) l) ∨
       ((∀ l : Layer, Good answers w (N.toNat % 2 ^ 31) l) ∧ FtsShaped answers N w)) := by
  classical
  have hS := shaped_of_verifyP answers m pk w hv
  obtain ⟨N, hdc, hN, hdq, _, hcase⟩ := verifyP_walk_extract answers m pk w hpk hv
  rw [hN] at hS
  refine ⟨N, hdc, hN, hdq, hS, ?_⟩
  rcases hcase with hhit | hdiv | ⟨hgood, hR, hqV⟩
  · exact Or.inl hhit
  · exact Or.inr (Or.inl hdiv)
  rw [ftsP_shaped N w hS] at hR hqV
  rcases hF answers N w hS hR with hhit | hshape
  · exact Or.inl (hhit.mono hqV)
  · exact Or.inr (Or.inr ⟨hgood, hshape⟩)

end SigGolfCandidate.T3M.Extract
