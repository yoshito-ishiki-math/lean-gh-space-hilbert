import PaperN.PartII.DistanceKernel
import PaperN.PartI.MetricBump

namespace PaperN.PartII
open MeasureTheory Metric Set PaperN.PartI
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X]

/-- The original metric is recovered exactly from uniform distances of profiles. -/
theorem distanceProfile_sub_norm (x y : X) : ‖distanceProfile x - distanceProfile y‖ = dist x y := by
  apply le_antisymm (distanceProfile_sub_norm_le x y)
  have h := (distanceProfile x - distanceProfile y).norm_coe_le_norm x
  simpa [distanceProfile, dist_comm] using h

theorem distanceProfile_isometry : Isometry (distanceProfile : X → C(X, ℝ)) :=
  Isometry.of_dist_eq fun x y ↦ by rw [dist_eq_norm, distanceProfile_sub_norm]

variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- A positive, normalized continuous bump approximates its center's distance profile. -/
theorem distance_bump_approximation (x : X) (r : ℝ) (hr : 0 ≤ r)
    (b : C(X, ℝ)) (hb : ∀ z, 0 ≤ b z) (hi : ∫ z, b z ∂μ = 1)
    (hs : ∀ z, b z ≠ 0 → dist x z ≤ r) :
    ‖distanceToContinuous μ (continuousToL2 μ b) - distanceProfile x‖ ≤ r := by
  have int (f : C(X, ℝ)) : Integrable f μ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (ContinuousMap.norm_le _ hr).mpr
  intro y
  have he : distanceValue μ (continuousToL2 μ b) y = ∫ z, dist y z * b z ∂μ :=
    distanceValue_integral_of_ae μ _ b (b.coeFn_toLp (p := 2) (𝕜 := ℝ) μ).symm y
  change |distanceValue μ (continuousToL2 μ b) y - dist x y| ≤ r
  rw [he]
  have hf : Integrable (fun z ↦ (dist y z - dist x y) * b z) μ :=
    int ⟨_, (continuous_const.dist continuous_id).sub continuous_const |>.mul b.continuous⟩
  have heq : (∫ z, dist y z * b z ∂μ) - dist x y =
      ∫ z, (dist y z - dist x y) * b z ∂μ := by
    simp only [sub_mul]
    have h₁ : Integrable (fun z : X ↦ dist y z * b z) μ :=
      int ⟨_, (continuous_const.dist continuous_id).mul b.continuous⟩
    rw [integral_sub h₁ ((int b).const_mul _), integral_const_mul, hi, mul_one]
  rw [heq]
  calc
    _ ≤ ∫ z, ‖(dist y z - dist x y) * b z‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ z, r * b z ∂μ := integral_mono hf.norm ((int b).const_mul r) (fun z ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hb z)]
      by_cases hz : b z = 0
      · simp [hz]
      · apply mul_le_mul_of_nonneg_right _ (hb z)
        have h := abs_dist_sub_le z x y
        rw [dist_comm z y, dist_comm z x] at h
        exact h.trans (hs z hz))
    _ = r := by rw [integral_const_mul, hi, mul_one]

/-- Concrete approximants using the normalized metric bumps already proved in Part I. -/
theorem exists_distance_range_approximation [μ.IsOpenPosMeasure] (x : X) (r : ℝ) (hr : 0 < r) :
    ∃ f : Lp ℝ 2 μ, ‖distanceToContinuous μ f - distanceProfile x‖ ≤ r := by
  obtain ⟨_,hc,hn,hi,hs⟩ := normalizedMetricBump_properties μ x hr
  let b : C(X, ℝ) := ⟨normalizedMetricBump μ x r,hc⟩
  refine ⟨continuousToL2 μ b, distance_bump_approximation μ x r hr.le b hn hi ?_⟩
  intro z hz
  have h := hs (subset_closure hz)
  exact (by simpa [mem_ball,dist_comm] using h : dist x z < r).le

/-- Every profile lies in the uniform closure of the actual operator's continuous range. -/
theorem distanceProfile_mem_closure_range [μ.IsOpenPosMeasure] (x : X) :
    distanceProfile x ∈ closure (range (distanceToContinuous μ)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨f,hf⟩ := exists_distance_range_approximation μ x (ε/2) (by positivity)
  refine ⟨distanceToContinuous μ f, mem_range_self f, ?_⟩
  rw [dist_comm, dist_eq_norm]
  linarith
end PaperN.PartII
