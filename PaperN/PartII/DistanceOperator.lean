import PaperN.PartII.DistanceOperatorStatements

namespace PaperN.PartII
universe u

theorem distanceOperator_spec (h : DistanceKernelSpectralInput.{u}) :
    DistanceOperatorStatement.{u} := by
  intro X _ _ _ _ _ μ _ _
  refine ⟨(h X μ).1, (h X μ).2, ?_, ?_⟩
  · intro f
    exact ⟨rfl, distanceValue_integral μ f, distanceContinuous_norm_le μ f,
      distanceValue_sub_bound μ f⟩
  · exact eigenfunction_continuousRepresentative μ
end PaperN.PartII
