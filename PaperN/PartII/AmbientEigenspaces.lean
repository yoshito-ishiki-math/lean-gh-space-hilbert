import PaperN.PartII.AmbientStatements
import PaperN.PartII.AmbientEquivalence

namespace PaperN.PartII
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambientEigenspaces_spec (he : Isometry e) : AmbientEigenspacesStatement e μ where
  integrable := AmbientKernel.distanceIntegrand_integrable e μ
  representative := AmbientKernel.distanceValue_integral_of_ae e μ
  compact := AmbientKernel.ambientOperator_compact e μ
  factorization := AmbientKernel.restriction_extension e μ he
  stabilization := fun a ha n hn ↦ ⟨AmbientKernel.ambient_power_kernel e μ he a ha n hn,
    AmbientKernel.distance_power_kernel μ a n hn⟩
  generalized := fun a ha ↦ ⟨AmbientKernel.ambient_maxGenEigenspace e μ he a ha,
    AmbientKernel.distance_maxGenEigenspace μ a⟩
  restriction_equivalence := fun a ha ↦ ⟨AmbientKernel.restrictionGeneralizedEquiv e μ he a ha,
    AmbientKernel.restrictionGeneralizedEquiv_apply e μ he a ha,
    AmbientKernel.restrictionGeneralizedEquiv_symm_apply e μ he a ha⟩
  spectrum_eq := AmbientKernel.ambient_nonzero_spectrum_eq e μ he
  spectrum_interval := fun _ ha ↦ AmbientKernel.ambient_spectrum_interval e μ he ha
end PaperN.PartII
