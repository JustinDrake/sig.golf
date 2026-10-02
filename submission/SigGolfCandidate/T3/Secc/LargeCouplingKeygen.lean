import SigGolfCandidate.T3.Secc.LargeCouplingInteraction

/-!
# LR-34 (coupling, key generation): the router's public key and published cache are the honest ones

The router discloses `keygenDisclosed` (the top-tree values of levels `0 … 12` of the layer-0 tree) and rebuilds the
public key and the published cache from them and the presampled masks and MAC. For a coherent table:

* `routerPk_eq`: the disclosed root value is `(evalWithAnswerFn T keygen).1`;
* `routerPublished_eq`: the rebuilt cache is `(evalWithAnswerFn T keygen).2`;
* `rel_initial`: the empty monitor and router states are related to the world state after the key disclosures.
-/

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers treeValue builtTree)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] buildFts buildTree keygen
noncomputable local instance instDecidableEqCache_largeCouplingKeygen : DecidableEq T3.Cache := Classical.decEq _

/-- The values the router uses after disclosing the key coordinates. -/
noncomputable def keyValues (vals : Coord → Digest) : Coord → Digest :=
  lookupVal (keygenDisclosed.map fun c => (c, vals c))

theorem treeChild_top_some (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level)) :
    ∃ c, treeChild 0 0 level node = some c := by
  by_cases hz : level=0
  · subst level
    have hn' : node < 4096 := by simpa using hn
    simp only [treeChild,ite_true,dif_pos hn']
    exact ⟨_,rfl⟩
  unfold treeChild treeNodeAt
  rw [if_neg hz]
  have h1 : level - 1 < height 0 := by simp [height]; omega
  have h2 : node < 2 ^ (height 0 - (level - 1) - 1) := by
    have : height 0 - (level - 1) - 1 = 12 - level := by simp [height]; omega
    rw [this]; exact hn
  rw [dif_pos ⟨h1, h2⟩]
  exact ⟨_, rfl⟩

theorem treeChild_mem_keygen (level node : Nat) (hl : 0 ≤ level) (hl' : level ≤ 12) (hn : node < 2 ^ (12 - level))
    (c : Coord) (hc : treeChild 0 0 level node = some c) : c ∈ keygenDisclosed := by
  unfold keygenDisclosed
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_filterMap, List.mem_range]
  exact ⟨level, ⟨by omega, by omega⟩, node, hn, hc⟩

theorem cacheRegion_congr (f g : Nat → Nat → Digest)
    (h : ∀ level node, 0 ≤ level → level < 12 → node < 2 ^ (12 - level) → f level node = g level node) :
    Correctness.cacheRegion f = Correctness.cacheRegion g := by
  have hw : Correctness.cacheWordList f = Correctness.cacheWordList g := by
    unfold Correctness.cacheWordList
    apply List.flatMap_congr
    intro level hlevel
    rw [List.mem_range'_1] at hlevel
    apply List.map_congr_left
    intro node hnode
    exact h level node (by omega) (by omega) (List.mem_range.mp hnode)
  unfold Correctness.cacheRegion
  rw [hw]

section Keygen
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}

theorem Coherent.topValue_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) (hl : 0 ≤ level) (hl' : level < 12)
    (hn : node < 2 ^ (12 - level)) : topValue (keyValues vals) level node = treeValue (builtTree T 0 0) level node := by
  obtain ⟨c, hc⟩ := treeChild_top_some level node (by omega) (by omega) hn
  have hmem := treeChild_mem_keygen level node hl (by omega) hn c hc
  have hb := builtTree_eq hcoh.agrees 0 ⟨0, by decide⟩ level node (by simp [height]; omega)
    (by simpa [height] using hn)
  change _ = treeValue (builtTree T 0 (⟨0, by decide⟩ : Fin (2 ^ 31)).val) level node
  rw [hb, treeLabel_eq (secretsOf T), ← honestValue_eq hcoh.agrees, hcoh.honestValue]
  have hc' : treeChild 0 ⟨0, by decide⟩ level node = some c := hc
  unfold LargeResidual.topValue
  rw [hc, hc']
  simp only [Option.map_some, Option.getD_some]
  exact lookupVal_map vals keygenDisclosed c hmem

theorem Coherent.private_header (hcoh : Coherent U T vals nv τ a)
    (tag level node : Nat) (h0 : tag%256 ≠ 0) (h8 : tag%256 ≠ 8) :
    T (.inr (.inl (header tag 0 0 level node))) = a.priv (.inl (header tag 0 0 level node)) := by
  apply hcoh.priv
  · intro i hi
    obtain ⟨s, hs⟩ := hi
    have hp := congrArg Prod.fst hs
    cases s with
    | inl x =>
        change Sum.inl (header 0 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h0) (Sum.inl.inj hp)
    | inr f =>
        change Sum.inl (header 8 _ _ _ _) = (Sum.inl (header tag 0 0 level node) : Coordinate) at hp
        exact QuerySpace.header_ne_of_tag (Ne.symm h8) (Sum.inl.inj hp)
  · intro m h
    cases h

theorem Coherent.mask_eq (hcoh : Coherent U T vals nv τ a) (level node : Nat) :
    maskOf a level node = evalWithAnswerFn T (T3.mask level node) := by
  have hp := hcoh.private_header 13 level (node/2) (by decide) (by decide)
  unfold maskOf T3.mask pairedMask privatePair privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [← hp]
  rfl

theorem Coherent.mac_eq (hcoh : Coherent U T vals nv τ a) (region : Region) :
    macOf a region = evalWithAnswerFn T (T3.privateMac region) := by
  have hk : (fun i : Fin 2 => a.priv (.inl (header 14 0 0 0 i.val))) =
      (fun i : Fin 2 => if i=0 then T (.inr (.inl (header 14 0 0 0 0)))
        else T (.inr (.inl (header 14 0 0 0 1)))) := by
    funext i
    fin_cases i <;> simp [hcoh.private_header 14 0 0 (by decide) (by decide),
      hcoh.private_header 14 0 1 (by decide) (by decide)]
  unfold macOf T3.privateMac T3.privateMacKey privateHash
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hk]
  rfl

/-- The router's published cache region is the honest one. -/
theorem Coherent.region (hcoh : Coherent U T vals nv τ a) :
    Correctness.cacheRegion (fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node) =
      Correctness.cacheRegion (Correctness.maskedTop T) := by
  apply cacheRegion_congr
  intro level node hl hl' hn
  rw [hcoh.topValue_eq level node hl hl' hn, hcoh.mask_eq]
  rfl

theorem rootNode_coord : treeChild 0 0 12 0 = some (.inl (.node (rootNode 0 0))) := by
  unfold treeChild treeNodeAt
  rw [if_neg (by decide), dif_pos (by simp [height])]
  rfl

/-- The router's public key is the honest one. -/
theorem Coherent.pk (hcoh : Coherent U T vals nv τ a) :
    keyValues vals (.inl (.node (rootNode 0 0))) = (evalWithAnswerFn T keygen).1 := by
  rw [Extract.keygen_pk, honestRoot_label hcoh.agrees 0 ⟨0, by decide⟩]
  have hmem := treeChild_mem_keygen 12 0 (by decide) le_rfl (by decide) _ rootNode_coord
  unfold keyValues
  rw [lookupVal_map vals keygenDisclosed _ hmem]
  exact (joinLabels_low (fun N => vals (.inl N)) a.high _).symm

/-- The router's published cache is the honest one. -/
theorem Coherent.published (hcoh : Coherent U T vals nv τ a) :
    (⟨macOf a (Correctness.cacheRegion fun level node =>
        topValue (keyValues vals) level node ^^^ maskOf a level node),
      Correctness.cacheRegion fun level node => topValue (keyValues vals) level node ^^^ maskOf a level node⟩ :
        T3.Cache) = (evalWithAnswerFn T keygen).2 := by
  obtain ⟨-, hreg, htag⟩ := Correctness.keygen_correct T
  rw [hcoh.region, hcoh.mac_eq]
  unfold Correctness.CacheTagCorrect at htag
  cases hk : (evalWithAnswerFn T keygen).2 with
  | mk tag region =>
      rw [hk] at hreg htag
      simp only at hreg htag
      subst hreg
      rw [htag]

end Keygen

end SigGolfCandidate.T3.Security.LargeCoupling
