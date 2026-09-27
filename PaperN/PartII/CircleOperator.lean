import PaperN.PartII.CircleScalar
import PaperN.PartII.ResolventEigenvector

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def circleResolvent (U : E →L[ℂ] E) (c : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ • circleIntegral (resolvent U) c r

theorem circleResolvent_integrable (U : E →L[ℂ] E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) : CircleIntegrable (resolvent U) c r := by
  apply ContinuousOn.circleIntegrable hr
  intro z hzs
  exact (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).continuousAt.continuousWithinAt

theorem circleResolvent_apply (U : E →L[ℂ] E) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) (v : E) :
    circleResolvent U c r v = (2 * Real.pi * Complex.I)⁻¹ •
      circleIntegral (fun z ↦ resolvent U z v) c r := by
  have hi := (circleIntegrable_iff r).mp (circleResolvent_integrable U c r hr hz)
  unfold circleResolvent circleIntegral
  rw [smul_apply, ContinuousLinearMap.intervalIntegral_apply hi]
  rfl

theorem circleResolvent_apply_eigenvector (U : E →L[ℂ] E) (a c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (ha : a ∉ sphere c r) (v : E) (hv : U v = a • v) :
    circleResolvent U c r v = scalarCircle a c r • v := by
  rw [circleResolvent_apply U c r hr hz]
  have he : circleIntegral (fun z ↦ resolvent U z v) c r =
      circleIntegral (fun z ↦ (z-a)⁻¹ • v) c r := by
    apply circleIntegral.integral_congr hr
    intro z hzs
    exact resolvent_apply_eigenvector U a z (hz z hzs) (ne_of_mem_of_not_mem hzs ha) v hv
  rw [he, circleIntegral.integral_smul_const]
  simp only [scalarCircle, smul_eq_mul, mul_smul]

theorem circleResolvent_fixes_inside (U : E →L[ℂ] E) (a c : ℂ) (r : ℝ)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) (ha : a ∈ ball c r)
    (v : E) (hv : U v = a • v) : circleResolvent U c r v = v := by
  have hr : 0 ≤ r := le_of_lt (lt_of_le_of_lt dist_nonneg ha)
  have hn : a ∉ sphere c r := by
    intro h; have hh := mem_sphere.mp h; exact (ne_of_lt ha) hh
  rw [circleResolvent_apply_eigenvector U a c r hr hz hn v hv, scalarCircle_inside a c r ha, one_smul]

theorem circleResolvent_kills_outside (U : E →L[ℂ] E) (a c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (ha : a ∉ closedBall c r) (v : E) (hv : U v = a • v) : circleResolvent U c r v = 0 := by
  rw [circleResolvent_apply_eigenvector U a c r hr hz
    (fun h ↦ ha (sphere_subset_closedBall h)) v hv, scalarCircle_outside a c r hr ha, zero_smul]
end PaperN.PartII
