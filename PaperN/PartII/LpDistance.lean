import PaperN.PartII.LpDistanceStatements
import PaperN.PartII.UniformBallMass
import PaperN.PartII.ProfileApproximation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

namespace PaperN.PartII
open MeasureTheory Metric Set
open scoped ENNReal
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

omit [Nonempty X] in
theorem distanceDifferenceLp_eq_sub (x y : X) :
    distanceDifferenceLp μ p x y = ContinuousMap.toLp p μ ℝ (distanceProfile x) -
      ContinuousMap.toLp p μ ℝ (distanceProfile y) := map_sub _ _ _

omit [Nonempty X] in
theorem distanceDifferenceLp_norm_le (x y : X) :
    ‖distanceDifferenceLp μ p x y‖ ≤ dist x y := by
  have h : ‖(ContinuousMap.toLp p μ ℝ : C(X, ℝ) →L[ℝ] Lp ℝ p μ)‖ ≤ 1 := by
    simpa [measureUnivNNReal] using (ContinuousMap.toLp_norm_le (E := ℝ) (𝕜 := ℝ) (p := p) μ)
  have hn := (ContinuousMap.toLp p μ ℝ).le_opNorm (distanceProfile x - distanceProfile y)
  change ‖ContinuousMap.toLp p μ ℝ (distanceProfile x - distanceProfile y)‖ ≤ _
  nlinarith [distanceProfile_sub_norm_le x y, norm_nonneg (distanceProfile x - distanceProfile y)]

omit [Nonempty X] in
/-- A constant supported on the ball gives the lower Lp norm estimate. -/
theorem distanceDifferenceLp_norm_lower (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (x y : X) (r : ℝ) (_hr : 0 < r) :
    max (dist x y - 2*r) 0 * μ.real (ball x r) ^ (1 / p.toReal) ≤
      ‖distanceDifferenceLp μ p x y‖ := by
  classical
  let c := max (dist x y - 2*r) 0
  have hc : 0 ≤ c := le_max_right _ _
  let g := indicatorConstLp p isOpen_ball.measurableSet (measure_ne_top μ (ball x r)) c
  have hnorm : ‖g‖ = c * μ.real (ball x r) ^ (1 / p.toReal) := by
    change ‖indicatorConstLp p isOpen_ball.measurableSet (measure_ne_top μ _) c‖ = _
    rw [norm_indicatorConstLp hp0 hp]
    rw [Real.norm_eq_abs,abs_of_nonneg hc]
  rw [← hnorm]
  apply Lp.norm_le_norm_of_ae_le
  have hgae : (fun z ↦ g z) =ᵐ[μ] (ball x r).indicator (fun _ ↦ c) := indicatorConstLp_coeFn
  filter_upwards [hgae,
    (distanceProfile x - distanceProfile y).coeFn_toLp (p := p) (𝕜 := ℝ) μ] with z hg hz
  change ‖g z‖ ≤ ‖(ContinuousMap.toLp p μ ℝ (distanceProfile x - distanceProfile y)) z‖
  rw [hz]
  change ‖g z‖ ≤ |dist x z - dist y z|
  change g z = _ at hg
  rw [hg]
  by_cases hzr : z ∈ ball x r
  · rw [indicator_of_mem hzr,Real.norm_eq_abs,abs_of_nonneg hc]
    apply max_le _ (abs_nonneg _)
    have hdist : dist x z < r := by simpa [dist_comm] using hzr
    have ht := dist_triangle x z y
    rw [dist_comm z y] at ht
    have hab := le_abs_self (dist y z - dist x z)
    rw [abs_sub_comm] at hab
    linarith
  · simp [indicator_of_notMem hzr,abs_nonneg]
/-- The complete quantitative error inequality; p is finite and at least one. -/
theorem distanceDifferenceLp_error (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (x y : X) (r : ℝ) (hr : 0 < r) :
    0 ≤ dist x y - ‖distanceDifferenceLp μ p x y‖ ∧
    dist x y - ‖distanceDifferenceLp μ p x y‖ ≤
      diam (univ : Set X) * (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p.toReal)) + 2*r := by
  let m : ℝ := ⨅ z : X, μ.real (ball z r)
  have hb : BddBelow (range (fun z : X ↦ μ.real (ball z r))) := by
    refine ⟨0,?_⟩
    rintro a ⟨z,rfl⟩
    exact measureReal_nonneg
  have hm0 : 0 ≤ m := le_ciInf (fun z ↦ measureReal_nonneg)
  have hmx : m ≤ μ.real (ball x r) := ciInf_le hb x
  have hm1 : m ≤ 1 := by
    have h := measureReal_mono (μ := μ) (subset_univ (ball x r)) (measure_ne_top _ _)
    rw [probReal_univ] at h
    exact hmx.trans h
  have he : 0 ≤ 1 / p.toReal := by positivity
  let b := m ^ (1 / p.toReal)
  have hb0 : 0 ≤ b := Real.rpow_nonneg hm0 _
  have hb1 : b ≤ 1 := Real.rpow_le_one hm0 hm1 he
  have hpower : b ≤ μ.real (ball x r) ^ (1 / p.toReal) := Real.rpow_le_rpow hm0 hmx he
  have hlower := distanceDifferenceLp_norm_lower μ p hp0 hp x y r hr
  have hmul := mul_le_mul_of_nonneg_left hpower (le_max_right (dist x y - 2*r) 0)
  have hmax := mul_le_mul_of_nonneg_left (le_max_left (dist x y - 2*r) 0) hb0
  have hd := dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)
  refine ⟨sub_nonneg.mpr (distanceDifferenceLp_norm_le μ p x y),?_⟩
  change dist x y - ‖distanceDifferenceLp μ p x y‖ ≤ diam (univ : Set X) * (1-b) + 2*r
  nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hd),
    mul_nonneg (le_of_lt hr) (sub_nonneg.mpr hb1)]
theorem lpDistance_spec : LpDistanceStatement.{u} := by
  intro X _ _ _ _ _ μ _ _ r hr
  refine ⟨uniform_ball_mass_pos μ r hr,?_⟩
  intro q hq
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  intro x y
  have h := distanceDifferenceLp_error μ (ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top x y r hr
  simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using h
end PaperN.PartII
