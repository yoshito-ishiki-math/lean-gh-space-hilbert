import PaperN.PartII.WeightedResolvent

namespace PaperN.PartII
open Set Metric MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Continuous complex-linear maps commute with circle integration. -/
theorem map_circleIntegral (L : E →L[ℂ] F) (f : ℂ → E) (c : ℂ) (r : ℝ)
    (hf : CircleIntegrable f c r) :
    L (circleIntegral f c r) = circleIntegral (fun z ↦ L (f z)) c r := by
  unfold circleIntegral
  rw [← L.intervalIntegral_comp_comm ((circleIntegrable_iff r).mp hf)]
  congr 1
  funext t
  exact map_smul L _ _

/-- The weighted circle operator used to factor a contour avoiding zero. -/
noncomputable def weightedCircleOperator (U : E →L[ℂ] E) (c : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ • circleIntegral (fun z ↦ z⁻¹ • resolvent U z) c r

/-- A circle not enclosing zero has its resolvent integral factored through U. -/
theorem circleResolvent_factor (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    circleResolvent U c r = U.comp (weightedCircleOperator U c r) := by
  have hn : ∀ z ∈ sphere c r, z ≠ 0 := by
    intro z hzs he
    exact hzero (he ▸ sphere_subset_closedBall hzs)
  let W := fun z : ℂ ↦ z⁻¹ • resolvent U z
  let L := ContinuousLinearMap.compL ℂ E E E U
  have hw : CircleIntegrable W c r := weightedResolvent_circleIntegrable U c r hr
    (fun h ↦ hzero (sphere_subset_closedBall h)) hz
  have hg : CircleIntegrable (fun z : ℂ ↦ z⁻¹ • (1 : E →L[ℂ] E)) c r := by
    apply ContinuousOn.circleIntegrable hr
    intro z hzs
    exact ((continuousAt_id.inv₀ (hn z hzs)).smul continuousAt_const).continuousWithinAt
  have hl : CircleIntegrable (fun z ↦ L (W z)) c r := by
    apply ContinuousOn.circleIntegrable hr
    intro z hzs
    exact (L.continuous.continuousAt.comp
      ((continuousAt_id.inv₀ (hn z hzs)).smul
        (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).continuousAt)).continuousWithinAt
  have he : circleIntegral (resolvent U) c r =
      circleIntegral (fun z ↦ z⁻¹ • (1 : E →L[ℂ] E) + L (W z)) c r := by
    apply circleIntegral.integral_congr hr
    intro z hzs
    ext x
    exact resolvent_apply_eq_scalar_add U z (hz z hzs) (hn z hzs) x
  unfold circleResolvent weightedCircleOperator
  rw [he, circleIntegral.integral_add hg hl, smul_add,
    circleIntegral.integral_smul_const, ← map_circleIntegral L W c r hw]
  have hscalar : (2 * Real.pi * Complex.I)⁻¹ * circleIntegral (fun z : ℂ ↦ z⁻¹) c r = 0 := by
    simpa [scalarCircle] using scalarCircle_outside 0 c r hr hzero
  rw [smul_smul, hscalar, zero_smul, zero_add]
  exact (map_smul L _ _).symm

/-- The range of a circle cutoff avoiding zero lies in the original operator range. -/
theorem circleResolvent_range_le (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    LinearMap.range (circleResolvent U c r).toLinearMap ≤ LinearMap.range U.toLinearMap := by
  rw [circleResolvent_factor U c r hr hzero hz]
  rintro y ⟨x,rfl⟩
  exact ⟨weightedCircleOperator U c r x,rfl⟩
end PaperN.PartII

