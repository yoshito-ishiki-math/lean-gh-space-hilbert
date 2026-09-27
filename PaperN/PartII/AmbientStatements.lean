import PaperN.PartII.AmbientKernel
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u v
/-- Review surface for the ambient-eigenspaces proposition, for any probability. -/
structure AmbientEigenspacesStatement
    {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {Z : Type v} [MetricSpace Z] [CompactSpace Z]
    (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] : Prop where
  integrable : ∀ f : Lp ℂ 2 μ, ∀ z, Integrable (fun y ↦ (dist z (e y) : ℂ) * f y) μ
  representative : ∀ (f : Lp ℂ 2 μ) (g : X → ℂ), g =ᵐ[μ] f → ∀ z,
    AmbientKernel.distanceToContinuous e μ f z = ∫ y, (dist z (e y) : ℂ) * g y ∂μ
  compact : IsCompactOperator (AmbientKernel.ambientOperator e μ)
  factorization : (AmbientKernel.restriction e μ).comp (AmbientKernel.distanceToContinuous e μ) =
    ComplexKernel.distanceOperator μ
  stabilization : ∀ a : ℂ, a ≠ 0 → ∀ n : ℕ, 0 < n →
    LinearMap.ker (((AmbientKernel.ambientOperator e μ).toLinearMap - a • 1)^n) =
      LinearMap.ker ((AmbientKernel.ambientOperator e μ).toLinearMap - a • 1) ∧
    LinearMap.ker (((ComplexKernel.distanceOperator μ).toLinearMap - a • 1)^n) =
      LinearMap.ker ((ComplexKernel.distanceOperator μ).toLinearMap - a • 1)
  generalized : ∀ a : ℂ, a ≠ 0 →
    Module.End.maxGenEigenspace (AmbientKernel.ambientOperator e μ).toLinearMap a =
      Module.End.eigenspace (AmbientKernel.ambientOperator e μ).toLinearMap a ∧
    Module.End.maxGenEigenspace (ComplexKernel.distanceOperator μ).toLinearMap a =
      Module.End.eigenspace (ComplexKernel.distanceOperator μ).toLinearMap a
  restriction_equivalence : ∀ a : ℂ, a ≠ 0 → ∃ E :
    Module.End.maxGenEigenspace (AmbientKernel.ambientOperator e μ).toLinearMap a ≃ₗ[ℂ]
      Module.End.maxGenEigenspace (ComplexKernel.distanceOperator μ).toLinearMap a,
    (∀ x, (E x : Lp ℂ 2 μ) = AmbientKernel.restriction e μ x) ∧
    (∀ y, (E.symm y : C(Z, ℂ)) = a⁻¹ • AmbientKernel.distanceToContinuous e μ y)
  spectrum_eq : spectrum ℂ (AmbientKernel.ambientOperator e μ) \ {0} =
    spectrum ℂ (ComplexKernel.distanceOperator μ) \ {0}
  spectrum_interval : ∀ a ∈ spectrum ℂ (AmbientKernel.ambientOperator e μ),
    a.im = 0 ∧ -diam (univ : Set Z) ≤ a.re ∧ a.re ≤ diam (univ : Set Z)
end PaperN.PartII
