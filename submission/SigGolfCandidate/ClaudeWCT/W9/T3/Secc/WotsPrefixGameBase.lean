import SigGolfCandidate.T3.Secc.WotsPrefixGameBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRef
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsReference
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.SeccLaw
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsEvents
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskCharge
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMask
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskChain
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskBase
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.WotsMaskRest

namespace ClaudeWCT.W9.T3.Security.Wots
open SigGolfCandidate SigGolfCandidate.T3.Security SigGolfCandidate.T3.Security.Wots
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Correctness (Answers leafSeed)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.constructorNameAsVariable false
attribute [local instance low] Classical.propDecidable
noncomputable local instance instFintypeCoordinate_wotsPrefixGameBase : Fintype Coordinate := coordinateFintype
open SigGolfCandidate.T3.Security.Wots.Mask ClaudeWCT.W9.T3.Security.Wots.Mask
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
end PrefixGame
abbrev RefTables (adversary : AdversaryP) := FullGame.FullTable × (referenceInputs adversary → HashOutput)
noncomputable instance instFintypeRefTables (adversary : AdversaryP) : Fintype (RefTables adversary) := by
  unfold RefTables FullGame.FullTable
  infer_instance
instance instNonemptyRefTables (adversary : AdversaryP) : Nonempty (RefTables adversary) := ⟨(fun _ => 0, fun _ => 0)⟩
noncomputable def restLaw (adversary : AdversaryP) : PMF (RefTables adversary) := PMF.uniformOfFintype _
noncomputable def restTable {adversary : AdversaryP} (R : RefTables adversary) : Answers :=
  eagerAnswers (referenceInputs adversary) R.1 R.2
@[irreducible] noncomputable def restDepth {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) : Nat :=
  depth (restTable R) a
theorem restDepth_eq {adversary : AdversaryP} (a : ChainAddr) (R : RefTables adversary) :
    restDepth a R = depth (restTable R) a := by
  unfold restDepth; rfl
namespace PrefixGame
open SigGolfCandidate.T3.Security.Wots.PrefixGame
variable {adversary : AdversaryP}
theorem chainRow_mem (a : ChainAddr) (step : Nat) (value : Digest) :
    chainRow a step value ∈ referenceInputs adversary := by
  unfold referenceInputs
  apply Finset.mem_union_left
  apply SeccLaw.mem_publicUniverse
  rw [chainRow_eq]
  have h : (chainInput a.key.lay a.key.tree a.key.leaf a.chain step value).length = 64 := by
    simp [chainInput, zero16, SphincsSecurity.bytesLE_length]
  rw [h]
  unfold SeccLaw.maxInputLength
  omega
theorem restTable_mem (R : RefTables adversary) (input : HashInput) (h : input ∈ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = R.2 ⟨input, h⟩ := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = R.2 ⟨input, h⟩
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_pos h]
  rfl
theorem restTable_nonmem (R : RefTables adversary) (input : HashInput) (h : input ∉ referenceInputs adversary) :
    restTable R (.inl (.inr input)) = (0 : HashOutput) := by
  show SphincsSecurity.Concrete.finiteHashAnswer ∅ (referenceInputs adversary) R.2 input = (0 : HashOutput)
  unfold SphincsSecurity.Concrete.finiteHashAnswer
  rw [dif_neg h]
  rfl
theorem restTable_private (R : RefTables adversary) (coordinate : Coordinate) :
    restTable R (.inr coordinate) = R.1 coordinate := rfl
theorem restTable_coin (R : RefTables adversary) (n : Nat) :
    restTable R (.inl (.inl n)) = (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) := rfl
noncomputable def ovPub (a : ChainAddr) (d : Nat) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) : referenceInputs adversary → HashOutput := fun x =>
  match rowOf a d x.val with
  | some p => ChainGraph.joinOutput (tables p.1 p.2) (high (pub x))
  | none => pub x
noncomputable def ov (a : ChainAddr) (d : Nat) (R : RefTables adversary) (x : Hidden d) : RefTables adversary :=
  (ovPriv a R.1 x.2, ovPub a d R.2 x.1)
noncomputable def rd (a : ChainAddr) (d : Nat) (R : RefTables adversary) : Hidden d :=
  (fun i v => low (R.2 ⟨chainRow a i v, chainRow_mem a i v⟩), seedHalf a (R.1 (.inl (seedTweak a))))
theorem ovPub_row (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (i : Fin d) (v : Digest) :
    ovPub a d pub tables ⟨chainRow a i v, chainRow_mem a i v⟩ =
      ChainGraph.joinOutput (tables i v) (high (pub ⟨chainRow a i v, chainRow_mem a i v⟩)) := by
  unfold ovPub
  rw [rowOf_chainRow a hd i v]
theorem ovPub_none (a : ChainAddr) {d : Nat} (pub : referenceInputs adversary → HashOutput)
    (tables : Fin d → Digest → Digest) (x : referenceInputs adversary) (h : rowOf a d x.val = none) :
    ovPub a d pub tables x = pub x := by
  unfold ovPub
  rw [h]
theorem rd_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    rd a d (ov a d R x) = x := by
  obtain ⟨tables, seed⟩ := x
  unfold rd ov
  simp only
  refine Prod.ext ?_ ?_
  · funext i v
    simp only
    rw [ovPub_row a hd, low, ChainGraph.joinOutput_low]
  · simp only [ovPriv, Function.update_self]
    exact seedHalf_setSeed a _ seed
theorem ov_ov_rd (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ov a d (ov a d R x) (rd a d R) = R := by
  obtain ⟨priv, pub⟩ := R
  obtain ⟨tables, seed⟩ := x
  unfold ov rd
  simp only
  refine Prod.ext ?_ ?_
  · simp only [ovPriv, Function.update_self, Function.update_idem, setSeed_setSeed, setSeed_seedHalf,
      Function.update_eq_self]
  · funext y
    unfold ovPub
    cases hp : rowOf a d y.val with
    | none => simp only [hp]
    | some p =>
        simp only [hp]
        have hy : y = ⟨chainRow a p.1 p.2, chainRow_mem a p.1 p.2⟩ := Subtype.ext (rowOf_some hp)
        subst hy
        simp only [high, low, ChainGraph.joinOutput_high, ChainGraph.joinOutput_parts]
theorem restTable_ov_untouched (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (query : T3.Spec.Domain) (hq : Untouched a query) : restTable (ov a d R x) query = restTable R query := by
  rcases query with (n | input) | (tweak | other)
  · rfl
  · by_cases h : input ∈ referenceInputs adversary
    · rw [restTable_mem _ _ h, restTable_mem _ _ h]
      unfold ov
      simp only
      rw [ovPub_none]
      cases hp : rowOf a d input with
      | none => rfl
      | some p => exact absurd (rowOf_some hp) (hq p.1 p.2 (by have := p.1.isLt; omega))
    · rw [restTable_nonmem _ _ h, restTable_nonmem _ _ h]
  · rw [restTable_private, restTable_private]
    unfold ov ovPriv
    simp only
    rw [Function.update_of_ne]
    intro he
    exact hq (Sum.inl.inj he)
  · rw [restTable_private, restTable_private]
    unfold ov ovPriv
    simp only
    rw [Function.update_of_ne]
    intro he
    cases he
theorem restTable_ov_prefix (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d)
    (i : Fin d) (v : Digest) :
    restTable (ov a d R x) (.inl (.inr (chainRow a i v))) =
      ChainGraph.joinOutput (x.1 i v) (high (restTable R (.inl (.inr (chainRow a i v))))) := by
  rw [restTable_mem _ _ (chainRow_mem a i v), restTable_mem _ _ (chainRow_mem a i v)]
  exact ovPub_row a hd R.2 x.1 i v
theorem restTable_ov_nonprefix (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (input : HashInput) (h : rowOf a d input = none) :
    restTable (ov a d R x) (.inl (.inr input)) = restTable R (.inl (.inr input)) := by
  by_cases hm : input ∈ referenceInputs adversary
  · rw [restTable_mem _ _ hm, restTable_mem _ _ hm]
    exact ovPub_none a R.2 x.1 _ h
  · rw [restTable_nonmem _ _ hm, restTable_nonmem _ _ hm]
theorem restTable_ov_seed (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    restTable (ov a d R x) (.inr (.inl (seedTweak a))) = setSeed a (restTable R (.inr (.inl (seedTweak a)))) x.2 := by
  rw [restTable_private, restTable_private]
  unfold ov ovPriv
  simp only [Function.update_self]
theorem restTable_ov_private (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d)
    (coordinate : Coordinate) (hc : coordinate ≠ .inl (seedTweak a)) :
    restTable (ov a d R x) (.inr coordinate) = restTable R (.inr coordinate) := by
  rw [restTable_private, restTable_private]
  unfold ov ovPriv
  simp only
  rw [Function.update_of_ne hc]
theorem depth_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) (b : ChainAddr)
    (hb : b = a) : depth (restTable (ov a d R x)) b = depth (restTable R) b := by
  subst hb
  exact depth_congr b _ _ (restTable_ov_untouched b hd R x)
theorem restDepth_le (a : ChainAddr) (R : RefTables adversary) : restDepth a R ≤ 7 := by
  rw [restDepth_eq]; exact Mask.depth_le_seven _ a
theorem restDepth_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    restDepth a (ov a (restDepth a R) R x) = restDepth a R := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  calc restDepth a (ov a (restDepth a R) R x) = depth (restTable (ov a (restDepth a R) R x)) a := restDepth_eq _ _
    _ = depth (restTable R) a := depth_ov a hd R x a rfl
    _ = restDepth a R := (restDepth_eq a R).symm
theorem leafSeed_ov (a : ChainAddr) {d : Nat} (R : RefTables adversary) (x : Hidden d) :
    leafSeed (restTable (ov a d R x)) a.key.lay a.key.tree a.key.leaf a.chain = x.2 := by
  rw [leafSeed_eq]
  have hs : header 0 a.key.lay.val a.key.tree (a.chain / 2) a.key.leaf = seedTweak a := rfl
  rw [hs, restTable_ov_seed]
  have := seedHalf_setSeed a (restTable R (.inr (.inl (seedTweak a)))) x.2
  unfold seedHalf at this
  exact this
theorem eval_chain_ov (a : ChainAddr) {d : Nat} (hd : d ≤ 256) (R : RefTables adversary) (x : Hidden d) :
    ∀ (n s : Nat) (hn : s + n ≤ d) (v : Digest),
      evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s n v) =
        SphincsSecurity.Concrete.PartialChainEndpoint.evaluate
          (fun (i : Fin n) => x.1 ⟨s + i.val, by omega⟩) v := by
  intro n
  induction n with
  | zero =>
      intro s hn v
      simp [chain, SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
  | succ n ih =>
      intro s hn v
      have hsplit : evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s (n + 1) v) =
          evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain (s + 1) n
            (evalWithAnswerFn (restTable (ov a d R x)) (chain a.key.lay a.key.tree a.key.leaf a.chain s 1 v))) := by
        rw [show n + 1 = 1 + n by omega]
        exact Correctness.eval_chain_add _ _ _ _ _ _ _ _ _
      rw [hsplit, eval_chain_one]
      have hrow : chainInput a.key.lay a.key.tree a.key.leaf a.chain s v = chainRow a (⟨s, by omega⟩ : Fin d) v := rfl
      rw [hrow, restTable_ov_prefix a hd R x, ChainGraph.joinOutput_low, ih (s + 1) (by omega)]
      simp only [SphincsSecurity.Concrete.PartialChainEndpoint.evaluate]
      congr 1
      · funext i w
        unfold Fin.tail
        exact congrArg (fun j : Fin d => x.1 j w) (Fin.ext (by simp only [Fin.val_succ]; omega))
theorem frontierValue_ov (a : ChainAddr) (R : RefTables adversary) (x : Hidden (restDepth a R)) :
    frontierValue (restTable (ov a (restDepth a R) R x)) a =
      SphincsSecurity.Concrete.PartialChainEndpoint.evaluate x.1 x.2 := by
  have hd : restDepth a R ≤ 256 := by have := restDepth_le a R; omega
  have hdepth : depth (restTable (ov a (restDepth a R) R x)) a = restDepth a R :=
    (restDepth_eq a (ov a (restDepth a R) R x)).symm.trans (restDepth_ov a R x)
  unfold frontierValue honestChainValue
  rw [hdepth, leafSeed_ov]
  rw [eval_chain_ov a hd R x (restDepth a R) 0 (by omega)]
  congr 1
  funext i
  exact congrArg x.1 (Fin.ext (by simp only [Nat.zero_add]))
end PrefixGame
end ClaudeWCT.W9.T3.Security.Wots
