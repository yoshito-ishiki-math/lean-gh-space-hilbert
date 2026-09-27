import PaperN.PartI.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic

/-! The metric bump and normalized bump used in Part I.
The radius is a positive real number. Function support means closed topological support. -/
namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set Metric

variable {X : Type*} [MetricSpace X]


lemma metricBump_nonneg (x y : X) (r : ℝ) : 0 ≤ metricBump x r y := le_max_right _ _

lemma metricBump_le_one (x y : X) {r : ℝ} (hr : 0 < r) :
    metricBump x r y ≤ 1 := by
  apply max_le
  · have := div_nonneg (dist_nonneg (x := x) (y := y)) hr.le
    linarith
  · norm_num

lemma continuous_metricBump (x : X) (r : ℝ) : Continuous (metricBump x r) := by
  unfold metricBump
  fun_prop

lemma metricBump_eq_zero_of_le (x y : X) {r : ℝ} (hr : 0 < r)
    (h : r ≤ dist x y) : metricBump x r y = 0 := by
  apply max_eq_right
  have : (1 : ℝ) ≤ dist x y / r := (le_div_iff₀ hr).2 (by simpa using h)
  linarith

lemma metricBump_lipschitz (x x' y y' : X) {r : ℝ} (hr : 0 < r) :
    |metricBump x r y - metricBump x' r y'| ≤ (dist x x' + dist y y') / r := by
  calc
    _ ≤ |(1 - dist x y / r) - (1 - dist x' y' / r)| :=
      abs_max_sub_max_le_abs _ _ _
    _ = |dist x y - dist x' y'| / r := by
      rw [sub_sub_sub_cancel_left, ← sub_div, abs_div, abs_of_pos hr, abs_sub_comm]
    _ ≤ _ := div_le_div_of_nonneg_right (by
      have h1 := abs_dist_sub_le x x' y
      have h2 := abs_dist_sub_le y y' x'
      have h3 := abs_add_le (dist x y - dist x' y) (dist x' y - dist x' y')
      rw [dist_comm y x', dist_comm y' x'] at h2
      have heq : dist x y - dist x' y + (dist x' y - dist x' y') = dist x y - dist x' y' := by ring
      rw [heq] at h3
      linarith) hr.le

lemma metricBump_le_indicator (x : X) {r : ℝ} (hr : 0 < r) (y : X) :
    metricBump x r y ≤ (ball x r).indicator (fun _ : X ↦ (1 : ℝ)) y := by
  by_cases hy : y ∈ ball x r
  · simpa [hy] using metricBump_le_one x y hr
  · have h : r ≤ dist x y := by simpa [mem_ball, dist_comm] using hy
    simp [hy, metricBump_eq_zero_of_le x y hr h]

lemma indicator_half_le_metricBump (x : X) {r : ℝ} (hr : 0 < r) (y : X) :
    (ball x (r / 2)).indicator (fun _ : X ↦ (1 / 2 : ℝ)) y ≤ metricBump x r y := by
  by_cases hy : y ∈ ball x (r / 2)
  · rw [indicator_of_mem hy]
    have hd : dist x y < r / 2 := by simpa [mem_ball, dist_comm] using hy
    have hdiv : dist x y / r ≤ 1 / 2 := (div_le_iff₀ hr).2 (by linarith)
    exact (by linarith : (1 / 2 : ℝ) ≤ 1 - dist x y / r).trans (le_max_left _ _)
  · simpa [hy] using metricBump_nonneg x y r

variable [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma integrable_metricBump (μ : Measure X) [IsFiniteMeasure μ] (x : X) (r : ℝ) :
    Integrable (metricBump x r) μ := (continuous_metricBump x r).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Both estimates of lem:metric-bump, for any finite Borel measure. -/
theorem metricBump_integral_bounds (μ : Measure X) [IsFiniteMeasure μ]
    (x : X) {r : ℝ} (hr : 0 < r) :
    (1 / 2 : ℝ) * μ.real (ball x (r / 2)) ≤ ∫ y, metricBump x r y ∂μ ∧
    (∫ y, metricBump x r y ∂μ) ≤ μ.real (ball x r) := by
  constructor
  · have h := integral_mono
      ((integrable_const (1 / 2 : ℝ)).indicator measurableSet_ball)
      (integrable_metricBump μ x r) (indicator_half_le_metricBump x hr)
    rw [integral_indicator_const _ measurableSet_ball] at h
    simpa [smul_eq_mul, mul_comm] using h
  · have h := integral_mono (integrable_metricBump μ x r)
      ((integrable_const (1 : ℝ)).indicator measurableSet_ball)
      (metricBump_le_indicator x hr)
    rw [integral_indicator_const _ measurableSet_ball] at h
    simpa using h

lemma metricBump_integral_pos (μ : Measure X) [IsFiniteMeasure μ] [IsOpenPosMeasure μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < ∫ y, metricBump x r y ∂μ := by
  have hp : 0 < μ.real (ball x (r / 2)) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos μ x (by positivity))) (measure_ne_top _ _)
  exact (mul_pos (by norm_num) hp).trans_le (metricBump_integral_bounds μ x hr).1


/-- The complete conclusion of lem:normalized-metric-bump. -/
theorem normalizedMetricBump_properties (μ : Measure X) [IsFiniteMeasure μ]
    [IsOpenPosMeasure μ] (x : X) {r : ℝ} (hr : 0 < r) :
    (0 < ∫ z, metricBump x (r / 2) z ∂μ) ∧
    Continuous (normalizedMetricBump μ x r) ∧
    (∀ y, 0 ≤ normalizedMetricBump μ x r y) ∧
    (∫ y, normalizedMetricBump μ x r y ∂μ) = 1 ∧
    tsupport (normalizedMetricBump μ x r) ⊆ ball x r := by
  have hr2 : 0 < r / 2 := by positivity
  have hp := metricBump_integral_pos μ x hr2
  refine ⟨hp, (continuous_metricBump x (r / 2)).div_const _,
    fun y ↦ div_nonneg (metricBump_nonneg x y _) hp.le, ?_, ?_⟩
  · simp only [normalizedMetricBump, integral_div, div_self hp.ne']
  · apply subset_trans (b := closedBall x (r / 2))
    · apply closure_minimal _ isClosed_closedBall
      intro y hy
      by_contra h
      have hd : r / 2 ≤ dist x y := by
        have : ¬ dist y x ≤ r / 2 := h
        rw [dist_comm] at this
        exact (lt_of_not_ge this).le
      exact hy (by simp [normalizedMetricBump, metricBump_eq_zero_of_le x y hr2 hd])
    · exact closedBall_subset_ball (by linarith)

end PaperN.PartI
