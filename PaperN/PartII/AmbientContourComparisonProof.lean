import PaperN.PartII.RectangleSpectralProjection
import PaperN.PartII.SegmentSquareFactorization
import PaperN.PartII.CircleSquareFactorization
import PaperN.PartII.SymmetricFactorSquareRange

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X,Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambient_rectangle_eq_circle_proved (he : Isometry e)
    (l r h : ℝ) (hlr : l < r) (hh : 0 < h) (hzero : (0 : ℝ) ∉ uIcc l r)
    (hl : (l : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hr : (r : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    rectangleResolvent (ambientOperator e μ) l r h =
      circleResolvent (ambientOperator e μ) (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) := by
  have ht : ∀ z ∈ spectrum ℂ (ComplexKernel.distanceOperator μ), z.im = 0 :=
    fun z hz ↦ (ComplexKernel.distanceOperator_spectrum_bound μ hz).1
  have hu : ∀ z ∈ spectrum ℂ (ambientOperator e μ), z.im = 0 := by
    intro z hz
    by_cases hz0 : z = 0
    · simp [hz0]
    · have hz' : z ∈ spectrum ℂ (ambientOperator e μ) \ {0} := ⟨hz,hz0⟩
      rw [ambient_nonzero_spectrum_eq e μ he] at hz'
      exact ht z hz'.1
  have hl0 : l ≠ 0 := fun h ↦ hzero (h ▸ left_mem_uIcc)
  have hr0 : r ≠ 0 := fun h ↦ hzero (h ▸ right_mem_uIcc)
  have hl' := (nonzero_resolventSet_iff e μ he (l : ℂ) (by exact_mod_cast hl0)).mpr hl
  have hr' := (nonzero_resolventSet_iff e μ he (r : ℂ) (by exact_mod_cast hr0)).mpr hr
  have hrect := rectangleResolvent_intertwine (ambientOperator e μ) (ComplexKernel.distanceOperator μ)
    (restriction e μ) (restriction_intertwine e μ he) hu ht l r h hh ⟨hl',hl⟩ ⟨hr',hr⟩
  have hcircle := circleResolvent_intertwine (ambientOperator e μ) (ComplexKernel.distanceOperator μ)
    (restriction e μ) (restriction_intertwine e μ he) (((l+r)/2 : ℝ) : ℂ) ((r-l)/2)
    (by linarith) (circle_real_interval_resolvent _ hu l r hl' hr')
    (circle_real_interval_resolvent _ ht l r hl hr)
  have heq := rectangleResolvent_eq_circle_of_compact_symmetric (ComplexKernel.distanceOperator μ)
    (distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (ComplexKernel.distanceOperator_symmetric μ) ht l r h hlr hh hl hr
  rw [heq] at hrect
  have hdisk : (0 : ℂ) ∉ closedBall (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) := by
    intro hz
    rw [mem_closedBall, dist_zero_left, Complex.norm_real, Real.norm_eq_abs] at hz
    have hb := abs_le.mp hz
    apply hzero
    rw [uIcc_of_le hlr.le]
    constructor <;> linarith
  have hsqR := rectangleResolvent_range_le_square_range (ambientOperator e μ) hu l r h hh hl' hr' hzero
  have hsqC := circleResolvent_range_le_square_range (ambientOperator e μ) _ _
    (by linarith : 0 ≤ (r-l)/2) hdisk (circle_real_interval_resolvent _ hu l r hl' hr')
  apply ContinuousLinearMap.ext
  intro f
  apply sub_eq_zero.mp
  apply restriction_zero_on_ambient_square_range e μ he
  · exact (LinearMap.range _).sub_mem (hsqR ⟨f,rfl⟩) (hsqC ⟨f,rfl⟩)
  · rw [map_sub]
    apply sub_eq_zero.mpr
    exact congrArg (fun A : C(Z,ℂ) →L[ℂ] Lp ℂ 2 μ ↦ A f) (hrect.trans hcircle.symm)

theorem ambient_cutoffContour_eq_circle_of_bound (he : Isometry e) (D : ℝ)
    (hD : 0 ≤ D) (hbound : diam (univ : Set X) ≤ D) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    cutoffContourOperator (ambientOperator e μ) (D) η =
      cutoffCircleOperator (ambientOperator e μ) η (cutoffOuter (D) η) := by
  have hb : ∀ z ∈ spectrum ℂ (ComplexKernel.distanceOperator μ), ‖z‖ ≤ D :=
    fun z hz ↦ (ComplexKernel.distanceOperator_spectrum_bound μ hz).2.trans hbound
  obtain ⟨ho,hno⟩ := cutoffOuter_resolvent (ComplexKernel.distanceOperator μ)
    (D) η hD hη hb
  have hgt := (cutoffOuter_gt (D) η hD hη).2
  have hp0 : (0 : ℝ) ∉ uIcc η (cutoffOuter (D) η) := by
    rw [uIcc_of_le hgt.le]
    intro hz
    linarith [hz.1]
  have hn0 : (0 : ℝ) ∉ uIcc (-cutoffOuter (D) η) (-η) := by
    rw [uIcc_of_le (by linarith)]
    intro hz
    linarith [hz.2]
  unfold cutoffContourOperator cutoffCircleOperator twoCircleResolvent
  rw [ambient_rectangle_eq_circle_proved e μ he η _ 1 hgt (by norm_num) hp0 hp ho,
    ambient_rectangle_eq_circle_proved e μ he (-cutoffOuter (D) η)
      (-η) 1 (by linarith) (by norm_num) hn0 (by simpa using hno) hn]
theorem ambient_cutoffContour_eq_circle_proved (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    cutoffContourOperator (ambientOperator e μ) (diam (univ : Set X)) η =
      cutoffCircleOperator (ambientOperator e μ) η (cutoffOuter (diam (univ : Set X)) η) := by
  exact ambient_cutoffContour_eq_circle_of_bound e μ he _ diam_nonneg le_rfl η hη hp hn
end PaperN.PartII.AmbientKernel
