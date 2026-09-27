import PaperN.PartII.RealComplexProjection
import PaperN.PartII.CircleIntertwining

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

/-- Restriction of the ambient integral is the complex extension of the real L² projection. -/
theorem restriction_cutoffCircle_real_imag (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : C(Z, ℂ)) :
    restriction e μ (cutoffCircleOperator (ambientOperator e μ) η B f) =
      realEmbed μ (realCutoffProjection μ hf η hη (realPart μ (restriction e μ f))) +
      Complex.I • realEmbed μ
        (realCutoffProjection μ hf η hη (imagPart μ (restriction e μ f))) := by
  have h := restriction_cutoffCircle e μ he η B hη hB hd hp hn
  rw [← distance_cutoffCircle_eq_starProjection μ η B hη hB hd hp hn] at h
  have hh := DFunLike.congr_fun h f
  change restriction e μ (cutoffCircleOperator (ambientOperator e μ) η B f) =
    cutoffCircleOperator (ComplexKernel.distanceOperator μ) η B (restriction e μ f) at hh
  rw [hh]
  exact distance_cutoffCircle_real_imag μ hf η B hη hB hd hp hn _

end PaperN.PartII.AmbientKernel
