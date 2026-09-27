import PaperN.PartII.ContourComparison

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

def ProjectionRestrictionStatement (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) : Prop :=
  let P := cutoffContourOperator (ambientOperator e μ) (Metric.diam (Set.univ : Set X)) η
  (∀ f : C(Z, ℝ), ∀ z : Z, (P (continuousRealEmbed f) z).im = 0) ∧
  (∃ R : LinearMap.range P.toLinearMap ≃ₗ[ℂ] continuousComplexCutoff μ η,
    ∀ f, (R f : C(X, ℂ)) = (f : C(Z, ℂ)).comp e) ∧
  (∀ f : C(Z, ℂ), (P f).comp e = continuousCutoffProjection μ hf η hη (restriction e μ f)) ∧
  (∀ g : C(X, ℂ), g ∈ continuousComplexCutoff μ η ↔
    ∃ u ∈ spectralCutoff μ η, ∃ v ∈ spectralCutoff μ η,
      g = continuousRealEmbed u + Complex.I • continuousRealEmbed v)


theorem projectionRestriction_spec (hf : CompactEigenvalueFinitenessInput.{u})

    (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    ProjectionRestrictionStatement e μ hf η hη := by
  unfold ProjectionRestrictionStatement
  rw [ambient_cutoffContour_eq_circle e μ  he η hη hp hn]
  exact circularProjectionRestriction_explicit e μ hf  he η hη hp hn

end PaperN.PartII.AmbientKernel
