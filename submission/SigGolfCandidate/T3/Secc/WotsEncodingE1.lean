import SigGolfCandidate.T3.Secc.WotsEncodingMatch

namespace SigGolfCandidate.T3.Security.Wots
open OracleComp OracleSpec ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final
open SigGolfCandidate.T3M.SecurityInputs SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance low] Classical.propDecidable
attribute [local irreducible] referenceGame offlineGame
namespace Enc
section Assembly
variable (adversary : AdversaryP) (q : Nat)
theorem tsum_uniform_prod {α β : Type} {iP : Fintype (α × β)} [Nonempty (α × β)] (iA : Fintype α) (iB : Fintype β)
    [Nonempty α] [Nonempty β] (G : α × β → ENNReal) :
    ∑' R, @PMF.uniformOfFintype (α × β) iP _ R * G R =
      ∑' a, @PMF.uniformOfFintype α iA _ a * ∑' b, @PMF.uniformOfFintype β iB _ b * G (a, b) := by
  obtain rfl : iP = @instFintypeProd α β iA iB := Subsingleton.elim _ _
  rw [ENNReal.tsum_prod (f := fun a b => @PMF.uniformOfFintype (α × β) (@instFintypeProd α β iA iB) _ (a, b) *
    G (a, b))]
  refine tsum_congr fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun b => ?_
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv (by simp) (by simp), mul_assoc]
theorem restTable_pair (p : FullGame.FullTable) (x : referenceInputs adversary → HashOutput) :
    restTable ((p, x) : RefTables adversary) = eagerAnswers (referenceInputs adversary) p x := by
  rw [restTable]
theorem weighted_le {α : Type} (μ : α → ENNReal) (left right : α → ENNReal) (rate : ENNReal)
    (h : ∀ x, left x ≤ rate * right x) : ∑' x, μ x * left x ≤ rate * ∑' x, μ x * right x := by
  calc _ ≤ ∑' x, μ x * (rate * right x) := ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)
    _ = _ := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => mul_left_comm _ _ _
theorem reference_free_le (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) (f g : RefSample → ENNReal)
    (rate : ENNReal)
    (hfg : ∀ (privateTable : FullGame.FullTable) (pub : referenceInputs adversary → HashOutput),
      ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) → HashOutput)
          (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          f (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r) ≤
      rate * ∑' y, @PMF.uniformOfFintype (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub) →
          HashOutput) (iX _) _ y *
        ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) adversary q) :
            PMF SeedResult) r *
          g (mkSample (eagerAnswers (referenceInputs adversary) privateTable
            (ov (freeSet (eagerAnswers (referenceInputs adversary) privateTable pub)) pub y)) r)) :
    ∑' s, referenceExperiment adversary q s * f s ≤ rate * ∑' s, referenceExperiment adversary q s * g s := by
  rw [reference_eq_bind, tsum_bind_mul, tsum_bind_mul]
  simp only [tsum_map_mul]
  unfold restLaw
  have iF : Fintype FullGame.FullTable := by unfold FullGame.FullTable; exact Pi.instFintype
  have iU : Fintype (referenceInputs adversary → HashOutput) := Pi.instFintype
  rw [tsum_uniform_prod iF iU, tsum_uniform_prod iF iU]
  simp only [restTable_pair]
  refine weighted_le _ _ _ _ fun privateTable => ?_
  have hU := publicUniverse_sub adversary
  rw [@public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * f (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r)),
    @public_resample (referenceInputs adversary) iX iU hU privateTable
      (fun pub => ∑' r, (liftM (offlineRun (eagerAnswers (referenceInputs adversary) privateTable pub) adversary q) :
        PMF SeedResult) r * g (mkSample (eagerAnswers (referenceInputs adversary) privateTable pub) r))]
  refine weighted_le _ _ _ _ fun pub => ?_
  exact hfg privateTable pub
theorem reference_matchInd_le [∀ k : Set EncIndex, Fintype k] [∀ k : Set EncIndex, DecidableEq k]
    (iX : ∀ k : Set EncIndex, Fintype (k → HashOutput)) :
    ∑' s, referenceExperiment adversary q s * matchInd s ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) :=
  reference_free_le adversary q iX matchInd (fun s => (encodingCount s : ENNReal)) _
    (fun privateTable pub => free_match_le adversary q iX (referenceInputs adversary)
      (publicUniverse_sub adversary) privateTable pub)
end Assembly
end Enc
open Enc in
theorem reference_encodingMatch_le (adversary : AdversaryP) (q : Nat) :
    Pr[fun s => ∃ L, WotsExtract.SourceLeaf L ∧ EncodingMatchAt s.answers s.trace L |
        referenceExperiment adversary q] ≤
      (2 ^ 128 : ENNReal)⁻¹ * ∑' s, referenceExperiment adversary q s * (encodingCount s : ENNReal) := by
  let _ : ∀ k : Set EncIndex, Fintype k := fun k => Fintype.ofFinite k
  let _ : ∀ k : Set EncIndex, DecidableEq k := fun k => Classical.decEq k
  refine le_trans ?_ (reference_matchInd_le adversary q (fun k => Pi.instFintype))
  rw [probEvent_eq_tsum_ite]
  refine ENNReal.tsum_le_tsum fun s => ?_
  split_ifs with h
  · obtain ⟨L, hsrc, hm⟩ := h
    have hpos : ∃ L' : CanonGraph.LeafPos, EncodingMatchAt s.answers s.trace (leafOf L') := by
      refine ⟨⟨L.lay, ⟨L.tree, hsrc.1⟩, ⟨L.leaf, lt_of_lt_of_le hsrc.2 ?_⟩⟩, hm⟩
      calc 2 ^ height L.lay ≤ 2 ^ 12 := Nat.pow_le_pow_right (by decide) (Extract.height_le L.lay)
        _ = 4096 := by norm_num
    rw [matchInd, if_pos hpos, mul_one, PMF.probOutput_eq_apply]
  · exact zero_le
end SigGolfCandidate.T3.Security.Wots
