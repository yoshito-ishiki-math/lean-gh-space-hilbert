import PaperN.PartII.CircleRangeFactorization
import PaperN.PartII.CircleIntertwining

namespace PaperN.PartII
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Both closed cutoff disks avoid zero when the cutoff is positive. -/
theorem cutoffCircle_disks_avoid_zero (η B : ℝ) (hη : 0 < η) (hB : η < B) :
    (0 : ℂ) ∉ closedBall (((η+B)/2 : ℝ) : ℂ) ((B-η)/2) ∧
    (0 : ℂ) ∉ closedBall (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2) := by
  constructor
  · intro h
    rw [mem_closedBall, dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < (η+B)/2)] at h
    linarith
  · intro h
    rw [mem_closedBall, dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith : (-B + -η)/2 < 0)] at h
    linarith

/-- The actual two-circle cutoff range is contained in the original operator range. -/
theorem cutoffCircle_range_le_operator_range (U : E →L[ℂ] E) (η B : ℝ)
    (hη : 0 < η) (hB : η < B)
    (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    LinearMap.range (cutoffCircleOperator U η B).toLinearMap ≤ LinearMap.range U.toLinearMap := by
  obtain ⟨hz,hw⟩ := cutoffCircle_spheres_resolvent U η B (hη.trans hB) hb hp hn
  obtain ⟨hzero,hzero'⟩ := cutoffCircle_disks_avoid_zero η B hη hB
  have h₁ := circleResolvent_range_le U _ _ (by linarith : 0 ≤ (B-η)/2) hzero hz
  have h₂ := circleResolvent_range_le U _ _ (by linarith : 0 ≤ (-η - -B)/2) hzero' hw
  rintro y ⟨x,rfl⟩
  exact (LinearMap.range U.toLinearMap).add_mem (h₁ ⟨x,rfl⟩) (h₂ ⟨x,rfl⟩)

/-- Circle cutoffs excluding zero of compact operators are compact. -/
theorem circleResolvent_isCompactOperator (U : E →L[ℂ] E) (hU : IsCompactOperator U)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    IsCompactOperator (circleResolvent U c r) := by
  rw [circleResolvent_factor U c r hr hzero hz]
  exact hU.comp_clm (weightedCircleOperator U c r)

/-- The two-circle cutoff of a compact operator is compact. -/
theorem cutoffCircle_isCompactOperator (U : E →L[ℂ] E) (hU : IsCompactOperator U)
    (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    IsCompactOperator (cutoffCircleOperator U η B) := by
  obtain ⟨hz,hw⟩ := cutoffCircle_spheres_resolvent U η B (hη.trans hB) hb hp hn
  obtain ⟨hzero,hzero'⟩ := cutoffCircle_disks_avoid_zero η B hη hB
  exact (circleResolvent_isCompactOperator U hU _ _ (by linarith) hzero hz).add
    (circleResolvent_isCompactOperator U hU _ _ (by linarith) hzero' hw)
end PaperN.PartII

