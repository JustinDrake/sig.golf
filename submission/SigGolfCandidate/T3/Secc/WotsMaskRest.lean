import SigGolfCandidate.T3.Secc.WotsMaskChain

/-!
# F1 (rest): the reference data of `a` is a function of the rest

BP-A §5.3 (stream C's per-address mixture): `depth T a` must be a function of the "rest" of `a`, i.e. of the table
outside `a`'s canonical rows and `a`'s seed coordinate. `depth_congr`: two tables agreeing on `Mask.Untouched a`
(every query except `chainRow a step value`, `step < 256`, and the seed coordinate `seedTweak a`) give `a` the same
depth (and the same honest message and reference search). The child tree of `a`'s leaf lives one layer below, so
none of its chains is an alias of `a`.
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
variable (a : ChainAddr)

theorem lay_eq_of_header {lay : Layer} {t t' tree pos leaf tree' pos' leaf' : Nat}
    (h : header t lay.val tree pos leaf = header t' a.key.lay.val tree' pos' leaf') : lay = a.key.lay := by
  have hl := (header_fields h).2.1
  apply Fin.ext
  rw [Nat.mod_eq_of_lt (lt_trans lay.isLt (by decide)),
    Nat.mod_eq_of_lt (lt_trans a.key.lay.isLt (by decide))] at hl
  exact hl

/-- Chain queries at another layer are untouched. -/
theorem untouched_chainInput_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i s : Nat) (v : Digest) :
    Untouched a (.inl (.inr (pad64 (chainInput lay tree leaf i s v)))) := by
  intro step value _ heq
  rw [pad64_chainInput, chainRow_eq, chainInput_eq_zero, chainInput_eq_zero] at heq
  exact hl (lay_eq_of_header a (chainInputP_fields heq).2.1)

theorem respects_chain_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i start count : Nat) (v : Digest) :
    Respects (Untouched a) (chain lay tree leaf i start count v) := by
  unfold chain
  exact Respects.foldlM _ _ (fun step _ value => Respects.shortHash _ (untouched_chainInput_of_lay a hl _ _ _ _ _))
    _

variable {T T' : Answers} (hT : ∀ q, Untouched a q → T q = T' q)
include hT

theorem leafSeed_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    leafSeed T lay tree leaf i = leafSeed T' lay tree leaf i := by
  rw [leafSeed_eq, leafSeed_eq, hT (.inr (.inl _)) (fun h => hl (lay_eq_of_header a (h.trans rfl)))]

theorem leafEnd_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf i : Nat) :
    leafEnd T lay tree leaf i = leafEnd T' lay tree leaf i := by
  unfold leafEnd
  rw [leafSeed_congr_of_lay a hT hl]
  exact (respects_chain_of_lay a hl _ _ _ _ _ _).eval_eq hT

theorem leafRoot_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree leaf : Nat) :
    Correctness.leafRoot T lay tree leaf = Correctness.leafRoot T' lay tree leaf := by
  unfold Correctness.leafRoot
  rw [List.map_congr_left (fun i _ => leafEnd_congr_of_lay a hT hl tree leaf i)]
  exact (respects_leafHash a _ _ _ _).eval_eq hT

theorem builtTree_congr_of_lay {lay : Layer} (hl : lay ≠ a.key.lay) (tree : Nat) :
    builtTree T lay tree = builtTree T' lay tree := by
  unfold builtTree
  have hr : Correctness.leafRoot T lay tree = Correctness.leafRoot T' lay tree :=
    funext (leafRoot_congr_of_lay a hT hl tree)
  rw [hr]
  exact (respects_buildLevels a 3 _ _ _ _ (by decide)).eval_eq hT

theorem honestForest_congr (index : Nat) : Extract.honestForest T index = Extract.honestForest T' index := by
  rw [honestForest_eq, honestForest_eq]
  have hl : ((List.range 7).map fun c => treeValue (evalWithAnswerFn T (buildFts index c)).1 11 0) =
      (List.range 7).map fun c => treeValue (evalWithAnswerFn T' (buildFts index c)).1 11 0 :=
    List.map_congr_left fun c _ => congrArg (fun x : List (List Digest) × List Digest => treeValue x.1 11 0)
      ((respects_buildFts a index c).eval_eq hT)
  rw [hl]
  exact (respects_forestPk a _ _).eval_eq hT

/-- The honest message of `a`'s leaf is a function of the rest of `a`. -/
theorem leafMsg_congr : leafMsg T a.key = leafMsg T' a.key := by
  unfold leafMsg
  split
  · rename_i h
    unfold Extract.honestRoot
    rw [builtTree_congr_of_lay a hT (fun he => by
      have := congrArg Fin.val he
      simp only at this
      omega)]
  · exact honestForest_congr a hT _

theorem referenceSearch_congr : referenceSearch T a.key = referenceSearch T' a.key := by
  unfold referenceSearch
  rw [leafMsg_congr a hT]
  exact (respects_counterSearch a _ _ _ _ _ _).eval_eq hT

end Mask

open Mask in
/-- **The depth of `a` is a function of the rest of `a`**: tables agreeing on every query except `a`'s canonical rows
(`step < 256`) and `a`'s seed coordinate give `a` the same reference word, hence the same depth. -/
theorem depth_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, Untouched a q → T q = T' q) :
    depth T a = depth T' a := by
  unfold depth referenceDigits
  rw [referenceSearch_congr a hT]

open Mask in
theorem referenceDigits_congr (a : ChainAddr) (T T' : Answers) (hT : ∀ q, Untouched a q → T q = T' q) :
    referenceDigits T a.key = referenceDigits T' a.key := by
  unfold referenceDigits
  rw [referenceSearch_congr a hT]

end SigGolfCandidate.T3.Security.Wots
