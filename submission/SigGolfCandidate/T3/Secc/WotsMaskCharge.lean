import SigGolfCandidate.T3.Secc.WotsMask

/-!
# F1 (charges): the honest query counts are unchanged by the mask

R3 (stream F2) consumes the honest charges `(SourceReplay.queried T keygen).length` and
`(SourceReplay.queried T (FullGame.authenticatedSign published request)).length` as ticks. This module proves
that both are unchanged by `maskAt T a`:

* `queried_length_maskAt_keygen` (every `a`), `queried_length_maskAt_signPayload`,
  `queried_length_maskAt_coreSign`, `queried_length_maskAt_sign` (source-sized `a`).

Route: chain folds and leaf builders issue a table-independent number of queries (`queried_length_chain`,
`queried_length_buildLeaf`, `queried_length_treeRows`, `queried_length_topPath`: explicit counts); every other honest
sub-program issues the same query *list* under the mask (`Mask.Respects`, which also tracks `SourceReplay.queried`);
the searches have the same control flow because their rows are untouched (`eval_maskAt_*`).
-/

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree leafSeed leafEnd leafValue)
open SphincsSecurity (bytesLE bytesLE_length bytesLE_injective)
open Mask
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Mask

/-! ## Query counts of programs (per table) -/

theorem queried_length_bind (T : Answers) {α β : Type} (p : M α) (f : α → M β) :
    (SourceReplay.queried T (p >>= f)).length =
      (SourceReplay.queried T p).length + (SourceReplay.queried T (f (evalWithAnswerFn T p))).length := by
  rw [SourceReplay.queried_bind, List.length_append]

theorem queried_length_pure (T : Answers) {α : Type} (x : α) :
    (SourceReplay.queried T (pure x : M α)).length = 0 := rfl

theorem queried_length_shortHash (T : Answers) (input : HashInput) :
    (SourceReplay.queried T (shortHash input)).length = 1 := rfl

theorem queried_length_privatePair (T : Answers) (tag lay tree position index : Nat) :
    (SourceReplay.queried T (privatePair tag lay tree position index)).length = 1 := rfl

theorem queried_length_foldlM (T : Answers) {β γ : Type} (l : List β) (f : γ → β → M γ) (c : β → Nat)
    (hf : ∀ x ∈ l, ∀ s, (SourceReplay.queried T (f s x)).length = c x) :
    ∀ init, (SourceReplay.queried T (l.foldlM f init)).length = (l.map c).sum := by
  induction l with
  | nil => intro init; rfl
  | cons x xs ih =>
      intro init
      rw [List.foldlM_cons, queried_length_bind, hf x List.mem_cons_self,
        ih (fun y hy s => hf y (List.mem_cons_of_mem x hy) s), List.map_cons, List.sum_cons]

theorem queried_length_mapM (T : Answers) {α β : Type} (l : List α) (f : α → M β) (c : α → Nat)
    (hf : ∀ x ∈ l, (SourceReplay.queried T (f x)).length = c x) :
    (SourceReplay.queried T (l.mapM f)).length = (l.map c).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.mapM_cons, queried_length_bind, queried_length_bind, queried_length_pure,
        hf x List.mem_cons_self, ih (fun y hy => hf y (List.mem_cons_of_mem x hy)), List.map_cons, List.sum_cons,
        Nat.add_zero]

theorem sum_map_one {β : Type} (l : List β) : (l.map fun _ => 1).sum = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

theorem queried_length_chain (T : Answers) (lay : Layer) (tree leaf i start count : Nat) (v : Digest) :
    (SourceReplay.queried T (chain lay tree leaf i start count v)).length = count := by
  unfold chain
  rw [queried_length_foldlM T _ _ (fun _ => 1) (fun _ _ _ => queried_length_shortHash _ _), sum_map_one,
    List.length_range']

/-! ## Leaf builders: table-independent counts -/

/-- Queries of one chain of `buildLeaf`. -/
def halfCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) (i : Nat) : Nat :=
  if chainCount lay ≤ i then 0
  else digits.getD i 0 + (if signatureOnly then 0 else maxDigit lay i - digits.getD i 0)

/-- Queries of `buildLeaf lay _ _ digits signatureOnly`. -/
def leafCount (lay : Layer) (digits : List Nat) (signatureOnly : Bool) : Nat :=
  ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
      1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum +
    (if signatureOnly then 0 else 1)

theorem queried_length_leafHalf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) (pair : Nat) (seeds : Digest × Digest) (rows : List Digest × List Digest) (half : Nat) :
    (SourceReplay.queried T (Correctness.leafHalf lay tree leaf digits signatureOnly pair seeds rows half)).length =
      halfCount lay digits signatureOnly (2 * pair + half) := by
  unfold Correctness.leafHalf halfCount
  by_cases hi : chainCount lay ≤ 2 * pair + half
  · simp only [hi, ↓reduceIte]
    rfl
  · simp only [hi, ↓reduceIte]
    rw [queried_length_bind, queried_length_chain]
    cases signatureOnly
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [queried_length_bind, queried_length_chain, queried_length_pure, Nat.add_zero]
    · simp only [↓reduceIte]
      rw [queried_length_pure]

theorem queried_length_leafRows (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (Correctness.leafRows lay tree leaf digits signatureOnly)).length =
      ((List.range ((chainCount lay + 1) / 2)).map fun pair =>
        1 + ((List.range 2).map fun half => halfCount lay digits signatureOnly (2 * pair + half)).sum).sum := by
  unfold Correctness.leafRows
  refine queried_length_foldlM T _ _ _ (fun pair _ rows => ?_) _
  rw [queried_length_bind, queried_length_privatePair,
    queried_length_foldlM T _ _ _ (fun half _ s => queried_length_leafHalf T lay tree leaf digits signatureOnly
      pair _ s half)]

theorem queried_length_buildLeaf (T : Answers) (lay : Layer) (tree leaf : Nat) (digits : List Nat)
    (signatureOnly : Bool) :
    (SourceReplay.queried T (buildLeaf lay tree leaf digits signatureOnly)).length =
      leafCount lay digits signatureOnly := by
  rw [Correctness.buildLeaf_eq, queried_length_bind, queried_length_leafRows]
  unfold leafCount
  cases signatureOnly
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [queried_length_bind, queried_length_pure]
    rfl
  · simp only [↓reduceIte]
    rfl

/-- Queries of the leaf loop of `buildTree`. -/
def treeRowsCount (lay : Layer) (selected : Nat) (digits : List Nat) : Nat :=
  ((List.range (2 ^ height lay)).map fun leaf => leafCount lay (if leaf = selected then digits else []) false).sum

theorem queried_length_treeRows (T : Answers) (lay : Layer) (tree selected : Nat) (digits : List Nat) :
    (SourceReplay.queried T (Correctness.treeRows lay tree selected digits)).length =
      treeRowsCount lay selected digits := by
  unfold Correctness.treeRows
  refine queried_length_foldlM T _ _ _ (fun leaf _ rows => ?_) _
  rw [queried_length_bind, queried_length_buildLeaf]
  rfl

/-- Queries of `topPath`: one paired-mask query for each of twelve cached siblings. -/
def topPathCount : Nat := ((List.range 12).map fun _ => 1).sum

theorem queried_length_topPath (T : Answers) (cache : Cache) (leaf : Nat) :
    (SourceReplay.queried T (topPath cache leaf)).length = topPathCount := by
  unfold topPath topPathCount
  exact queried_length_mapM T _ _ (fun _ => 1) (fun level _ => by
    unfold mask pairedMask
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])

theorem queried_length_signTop (T : Answers) (cache : Cache) (leaf : Nat) (digits : List Nat) :
    (SourceReplay.queried T (signTop cache leaf digits)).length = leafCount 0 digits true + topPathCount := by
  unfold signTop
  simp only [queried_length_bind, queried_length_buildLeaf, queried_length_topPath, queried_length_pure,
    Nat.add_zero]

/-! ## Under the mask -/

variable (answers : Answers) (a : ChainAddr)

theorem count_bind_of {T T' : Answers} {α β : Type} {p : M α} {f : α → M β}
    (hp : evalWithAnswerFn T' p = evalWithAnswerFn T p)
    (hcp : (SourceReplay.queried T' p).length = (SourceReplay.queried T p).length)
    (hf : (SourceReplay.queried T' (f (evalWithAnswerFn T p))).length =
      (SourceReplay.queried T (f (evalWithAnswerFn T p))).length) :
    (SourceReplay.queried T' (p >>= f)).length = (SourceReplay.queried T (p >>= f)).length := by
  rw [queried_length_bind, queried_length_bind, hp, hcp, hf]

theorem count_maskAt_of_respects {α : Type} {program : M α} (h : Respects (Untouched a) program) :
    (SourceReplay.queried (maskAt answers a) program).length = (SourceReplay.queried answers program).length := by
  rw [queried_maskAt_of_respects answers a h]

/-- The tree builder issues as many queries under the mask (any word; the leaf roots are unchanged). -/
theorem count_buildTree_maskAt (lay : Layer) (tree selected : Nat) (digits : List Nat)
    (hvalid : Cost.ValidDigits lay digits) :
    (SourceReplay.queried (maskAt answers a) (buildTree lay tree selected digits)).length =
      (SourceReplay.queried answers (buildTree lay tree selected digits)).length := by
  rw [Correctness.buildTree_eq, queried_length_bind (maskAt answers a), queried_length_bind answers,
    queried_length_treeRows, queried_length_treeRows, Correctness.eval_treeRows _ lay tree selected digits hvalid,
    Correctness.eval_treeRows _ lay tree selected digits hvalid]
  have hr : Correctness.leafRoot (maskAt answers a) lay tree = Correctness.leafRoot answers lay tree :=
    funext (leafRoot_maskAt answers a lay tree)
  rw [hr]
  dsimp only
  rw [queried_length_bind, queried_length_bind, queried_length_pure, queried_length_pure,
    count_maskAt_of_respects answers a (respects_buildLevels a 3 _ _ _ _ (by decide))]

/-- Paired-mask queries for the twelve cached levels. -/
def maskCount : Nat := ((List.range' 0 12).map fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum).sum

theorem queried_length_maskedLevel (T : Answers) (nodes : List Digest) (level : Nat) :
    (SourceReplay.queried T (maskedLevel nodes level)).length =
      ((List.range (2 ^ (11-level))).map fun _ => 1).sum := by
  unfold maskedLevel pairedMask
  rw [queried_length_bind, queried_length_pure, Nat.add_zero]
  exact queried_length_mapM T _ _ (fun _ => 1) (fun pair _ => by
    simp only [queried_length_bind, queried_length_privatePair, queried_length_pure])

theorem queried_length_cachePayload (T : Answers) (builder : M (List (List Digest) × List Digest)) :
    (SourceReplay.queried T (Correctness.cachePayloadProgram builder)).length =
      (SourceReplay.queried T builder).length + maskCount := by
  unfold Correctness.cachePayloadProgram
  rw [queried_length_bind]
  generalize evalWithAnswerFn T builder = x
  rcases x with ⟨levels, values⟩
  dsimp only
  rw [queried_length_bind, queried_length_pure, Nat.add_zero,
    queried_length_mapM _ _ _ (fun level => ((List.range (2 ^ (11 - level))).map fun _ => 1).sum)
      (fun level _ => queried_length_maskedLevel _ _ _)]
  rfl

theorem count_keygenPayload_maskAt :
    (SourceReplay.queried (maskAt answers a) keygenPayload).length =
      (SourceReplay.queried answers keygenPayload).length := by
  rw [Correctness.keygenPayload_eq, queried_length_cachePayload, queried_length_cachePayload,
    count_buildTree_maskAt answers a 0 0 0 [] (Cost.validDigits_nil 0)]

end Mask

/-- **Honest key generation's charge is unchanged by the mask** (every address). -/
theorem queried_length_maskAt_keygen (answers : Answers) (a : ChainAddr) :
    (SourceReplay.queried (maskAt answers a) keygen).length = (SourceReplay.queried answers keygen).length := by
  unfold keygen
  refine count_bind_of (eval_keygenPayload_maskAt answers a) (count_keygenPayload_maskAt answers a) ?_
  generalize evalWithAnswerFn answers keygenPayload = payload
  rcases payload with ⟨publicKey, region⟩
  exact count_maskAt_of_respects answers a (Respects.bind (respects_privateMac a region) fun _ => Respects.pure' _)

namespace Mask
variable (answers : Answers) (a : ChainAddr)

/-- The layer signer issues as many queries under the mask (honest messages, source-sized `a`). -/
theorem count_signLayers_maskAt (htree : a.key.tree < 2 ^ 40) (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache)
    (index : Nat) (hindex : index < 2 ^ 31) :
    ∀ n, n ≤ 4 → ∀ msg, (∀ m, n = m + 1 → msg = leafMsg answers (routeLeaf index (Fin.ofNat 4 m))) →
      (SourceReplay.queried (maskAt answers a) (signLayers cache index n msg)).length =
        (SourceReplay.queried answers (signLayers cache index n msg)).length := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
      intro hn msg hmsg
      simp only [signLayers]
      refine count_bind_of (eval_maskAt_of_respects answers a (respects_counterSearch a _ _ _ _ _ _))
        (count_maskAt_of_respects answers a (respects_counterSearch a _ _ _ _ _ _)) ?_
      cases hs : evalWithAnswerFn answers (counterSearch (Fin.ofNat 4 n) (route index (Fin.ofNat 4 n)).2
        (route index (Fin.ofNat 4 n)).1 msg 0 counterLimit) with
      | none => rfl
      | some found =>
          obtain ⟨counter, digits⟩ := found
          have hd := (Correctness.counterSearch_some answers _ _ _ msg counterLimit 0 counter digits
            (by decide) hs).2.2
          have hvalid := Cost.validDigits_decode hd
          have hsearch : referenceSearch answers (routeLeaf index (Fin.ofNat 4 n)) = some (counter, digits) := by
            unfold referenceSearch
            rw [← hmsg n rfl]
            exact hs
          dsimp only
          split_ifs with hn0
          · rw [queried_length_bind, queried_length_bind, queried_length_signTop, queried_length_signTop]
            rfl
          · refine count_bind_of (eval_buildTree_maskAt answers a _ _ _ digits hvalid (route_leaf_bound index _)
                (fun hal _ => routeLeaf_alias a hindex hsearch htree hleaf hal))
              (count_buildTree_maskAt answers a _ _ _ digits hvalid) ?_
            rw [Correctness.eval_buildTree_result answers _ _ _ digits hvalid (route_leaf_bound index _)]
            dsimp only
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            have hmsg' : ∀ m', m + 1 = m' + 1 → (((builtTree answers (Fin.ofNat 4 (m + 1))
                (route index (Fin.ofNat 4 (m + 1))).2).getD (height (Fin.ofNat 4 (m + 1)) - 1) []).getD 0 0, 0, ((builtTree answers (Fin.ofNat 4 (m + 1))
                (route index (Fin.ofNat 4 (m + 1))).2).getD (height (Fin.ofNat 4 (m + 1)) - 1) []).getD 1 0) =
                leafMsg answers (routeLeaf index (Fin.ofNat 4 m')) := fun m' hm' => by
              obtain rfl : m = m' := by omega
              exact signedMsg_succ answers index m (by omega)
            refine count_bind_of (eval_signLayers_maskAt answers a htree hleaf cache index hindex (m + 1) (by omega)
              _ hmsg') (ih (by omega) _ hmsg') ?_
            cases evalWithAnswerFn answers (signLayers cache index (m + 1) _) <;> rfl

end Mask

/-- **The payload signer's charge is unchanged by the mask** (any cache and message; source-sized `a`). -/
theorem queried_length_maskAt_signPayload (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (signPayload cache message)).length =
      (SourceReplay.queried answers (signPayload cache message)).length := by
  rw [Correctness.signPayload_eq]
  refine count_bind_of (eval_maskAt_of_respects answers a (respects_privateNonce a message))
    (count_maskAt_of_respects answers a (respects_privateNonce a message)) ?_
  generalize evalWithAnswerFn answers (privateNonce message) = rho
  refine count_bind_of (eval_maskAt_of_respects answers a (respects_digestSearch a _ _ _ _))
    (count_maskAt_of_respects answers a (respects_digestSearch a _ _ _ _)) ?_
  generalize evalWithAnswerFn answers (digestSearch rho message 0 attemptLimit) = found
  rcases found with _ | ⟨counter, output⟩
  · rfl
  · dsimp only
    refine count_bind_of (eval_maskAt_of_respects answers a (respects_signForest a _ _))
      (count_maskAt_of_respects answers a (respects_signForest a _ _)) ?_
    rw [Correctness.eval_signForest]
    dsimp only
    refine count_bind_of (eval_maskAt_of_respects answers a (respects_forestPk a _ _))
      (count_maskAt_of_respects answers a (respects_forestPk a _ _)) ?_
    have hmsg : ∀ m, 4 = m + 1 → ((evalWithAnswerFn answers (forestPk (output.toNat % 2 ^ 31)
        (Correctness.forestRoots answers (output.toNat % 2 ^ 31) 7)), 0, 0) : Digest × BitVec 96 × Digest) =
        leafMsg answers (routeLeaf (output.toNat % 2 ^ 31) (Fin.ofNat 4 m)) := fun m hm => by
      obtain rfl : m = 3 := by omega
      exact signedMsg_top answers _
    refine count_bind_of (eval_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide)) 4
      le_rfl _ hmsg) (count_signLayers_maskAt answers a htree hleaf cache _ (Nat.mod_lt _ (by decide)) 4
      le_rfl _ hmsg) ?_
    generalize evalWithAnswerFn answers (signLayers cache (output.toNat % 2 ^ 31) 4 _) = pieces
    rcases pieces with _ | pieces <;> rfl

/-- **Core's signer's charge is unchanged by the mask.** -/
theorem queried_length_maskAt_coreSign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (cache : Cache) (message : Message) :
    (SourceReplay.queried (maskAt answers a) (T3.sign cache message)).length =
      (SourceReplay.queried answers (T3.sign cache message)).length := by
  unfold T3.sign
  refine count_bind_of (eval_maskAt_of_respects answers a (respects_privateMac a _))
    (count_maskAt_of_respects answers a (respects_privateMac a _)) ?_
  split
  · rfl
  · exact queried_length_maskAt_signPayload answers a htree hleaf cache message

/-- **The logged signer's charge is unchanged by the mask** (`FullGame.authenticatedSign`, any published cache and
request; source-sized `a`). -/
theorem queried_length_maskAt_sign (answers : Answers) (a : ChainAddr) (htree : a.key.tree < 2 ^ 40)
    (hleaf : a.key.leaf < 2 ^ 32) (published : T3.Cache) (request : Request) :
    (SourceReplay.queried (maskAt answers a) (FullGame.authenticatedSign published request)).length =
      (SourceReplay.queried answers (FullGame.authenticatedSign published request)).length := by
  unfold FullGame.authenticatedSign
  refine count_bind_of (eval_maskAt_of_respects answers a (respects_privateMac a _))
    (count_maskAt_of_respects answers a (respects_privateMac a _)) ?_
  split
  · exact queried_length_maskAt_signPayload answers a htree hleaf _ _
  · rfl

end SigGolfCandidate.T3.Security.Wots
