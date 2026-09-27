import PaperN.PartII.CircularProjectionRestriction
import PaperN.PartII.CutoffContour
import PaperN.PartII.AmbientContourComparisonProof

namespace PaperN.PartII
universe u

/-- Cited Cauchy contour independence, specialized to two positively oriented
contours selecting the same real spectral interval. No inhabitant is asserted. -/
def RectangleCircleResolventInput : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E), (∀ z ∈ spectrum ℂ U, z.im = 0) →
    ∀ l r h : ℝ, l < r → 0 < h →
    (l : ℂ) ∈ resolventSet ℂ U → (r : ℂ) ∈ resolventSet ℂ U →
    rectangleResolvent U l r h = circleResolvent U (((l+r)/2 : ℝ) : ℂ) ((r-l)/2)

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cutoffContour_eq_circle (hC : RectangleCircleResolventInput.{u})
    (U : E →L[ℂ] E) (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (hb : ∀ z ∈ spectrum ℂ U, ‖z‖ ≤ D)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    cutoffContourOperator U D η = cutoffCircleOperator U η (cutoffOuter D η) := by
  obtain ⟨ho, hno⟩ := cutoffOuter_resolvent U D η hD hη hb
  have hgt := (cutoffOuter_gt D η hD hη).2
  unfold cutoffContourOperator cutoffCircleOperator twoCircleResolvent
  rw [hC E U hr η (cutoffOuter D η) 1 hgt (by norm_num) hp ho,
    hC E U hr (-cutoffOuter D η) (-η) 1 (by linarith) (by norm_num) (by simpa using hno) hn]

namespace AmbientKernel
open MeasureTheory
universe v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambient_spectrum_bound_source (he : Isometry e) {z : ℂ}
    (hz : z ∈ spectrum ℂ (ambientOperator e μ)) :
    z.im = 0 ∧ ‖z‖ ≤ Metric.diam (Set.univ : Set X) := by
  by_cases hzero : z = 0
  · simp [hzero, Metric.diam_nonneg]
  · have hh : z ∈ spectrum ℂ (ambientOperator e μ) \ {0} := ⟨hz, hzero⟩
    rw [ambient_nonzero_spectrum_eq e μ he] at hh
    exact ComplexKernel.distanceOperator_spectrum_bound μ hh.1

theorem ambient_cutoffContour_eq_circle (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    cutoffContourOperator (ambientOperator e μ) (Metric.diam (Set.univ : Set X)) η =
      cutoffCircleOperator (ambientOperator e μ) η (cutoffOuter (Metric.diam (Set.univ : Set X)) η) := by
  exact ambient_cutoffContour_eq_circle_proved e μ he η hη hp hn

end AmbientKernel
end PaperN.PartII
