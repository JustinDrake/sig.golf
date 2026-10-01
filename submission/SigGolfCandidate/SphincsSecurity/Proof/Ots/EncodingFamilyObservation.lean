import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingConditionalObservation
import SigGolfCandidate.SphincsSecurity.Proof.Base.UniformTableProducts
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec UniformTableCompletion
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def encodingFamilyAllowed (selections : ReferenceFamily) (row : EncodingRow) : Finset HashOutput :=
  encodingSelectionAllowed row.1.lay (selections row.1) row.2

theorem encodingFamilyAllowed_nonempty (selections : ReferenceFamily) :
    ∀ row, (encodingFamilyAllowed selections row).Nonempty :=
  fun row => encodingSelectionAllowed_nonempty (selections row.1) row.2

theorem encoding_afterSelect_uniform {lay : Layer} (selection : ReferenceSelection) :
    FirstSuccessTable.afterSelect (decodeEncodingOutput lay) encodingAttemptLimit selection =
      uniformTable (encodingSelectionAllowed lay selection) (encodingSelectionAllowed_nonempty selection) := by
  apply PMF.ext
  intro table
  have h := congrArg (fun law : SPMF (Fin encodingAttemptLimit → HashOutput) => law table)
    (encoding_afterSelect_complete (lay := lay) selection)
  simpa only [complete_of_nonempty _ (encodingSelectionAllowed_nonempty selection), PMF.evalSPMF_eq, SPMF.liftM_apply] using h

theorem encoding_family_uniform (selections : ReferenceFamily) :
    (FirstSuccessFamily.afterSelect decodeEncodingFamily encodingAttemptLimit selections).map Function.uncurry =
        uniformTable (encodingFamilyAllowed selections) (encodingFamilyAllowed_nonempty selections) := by
  simp only [FirstSuccessFamily.afterSelect, decodeEncodingFamily, encoding_afterSelect_uniform, uniformTable_eq_product,
    encodingFamilyAllowed]
  exact FinitePmfProduct.uncurry (fun (position : EncodingPosition) (coordinate : Fin encodingAttemptLimit) =>
    PMF.uniformOfFinset (encodingSelectionAllowed position.lay (selections position) coordinate)
      (encodingSelectionAllowed_nonempty (selections position) coordinate))

end SphincsSecurity.Concrete
