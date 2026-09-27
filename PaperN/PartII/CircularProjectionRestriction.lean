import PaperN.PartII.ContinuousCutoffEquivalence

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

/-- All conclusions of projection restriction for the explicit two-circle contour.
Contour independence is not included in this statement. -/
def CircularProjectionRestrictionStatement (hf : CompactEigenvalueFinitenessInput.{u})
    (η B : ℝ) (hη : 0 < η) : Prop :=
  let P := cutoffCircleOperator (ambientOperator e μ) η B
  (∀ f : C(Z, ℝ), ∀ z : Z, (P (continuousRealEmbed f) z).im = 0) ∧
  (∃ R : LinearMap.range P.toLinearMap ≃ₗ[ℂ] continuousComplexCutoff μ η,
    ∀ f, (R f : C(X, ℂ)) = (f : C(Z, ℂ)).comp e) ∧
  (∀ f : C(Z, ℂ), (P f).comp e = continuousCutoffProjection μ hf η hη (restriction e μ f)) ∧
  (∀ g : C(X, ℂ), g ∈ continuousComplexCutoff μ η ↔
    ∃ u ∈ spectralCutoff μ η, ∃ v ∈ spectralCutoff μ η,
      g = continuousRealEmbed u + Complex.I • continuousRealEmbed v)

theorem circularProjectionRestriction_spec (hf : CompactEigenvalueFinitenessInput.{u})
     (he : Isometry e)
    (η B : ℝ) (hη : 0 < η) (hB : η < B) (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    CircularProjectionRestrictionStatement e μ hf η B hη := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ambient_cutoffCircle_real_pointwise e μ hf  he η B hη hB hd hp hn
  · exact ⟨restrictionContinuousCircleRangeEquiv e μ  he η B hη hB hd hp hn,
      restrictionContinuousCircleRangeEquiv_apply e μ  he η B hη hB hd hp hn⟩
  · exact restriction_cutoffCircle_continuous e μ hf he η B hη hB hd hp hn
  · exact mem_continuousComplexCutoff_iff μ hη

/-- The outer radius is chosen from the carrier diameter, leaving no extra bound assumption. -/
theorem circularProjectionRestriction_explicit (hf : CompactEigenvalueFinitenessInput.{u})
     (he : Isometry e)
    (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    CircularProjectionRestrictionStatement e μ hf η (Metric.diam (Set.univ : Set X) + η + 1) hη := by
  apply circularProjectionRestriction_spec e μ hf  he η _ hη _ _ hp hn
  · linarith [Metric.diam_nonneg (s := Set.univ (α := X))]
  · linarith

end PaperN.PartII.AmbientKernel
