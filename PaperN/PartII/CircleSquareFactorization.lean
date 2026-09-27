import PaperN.PartII.CutoffCircleRangeFactorization

namespace PaperN.PartII
open Set Metric MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def twiceWeightedCircleOperator (U : E →L[ℂ] E) (c : ℂ) (r : ℝ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ • circleIntegral (fun z ↦ (z⁻¹)^2 • resolvent U z) c r

theorem weightedCircleOperator_factor (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    weightedCircleOperator U c r = U.comp (twiceWeightedCircleOperator U c r) := by
  have hn : ∀ z ∈ closedBall c r, z ≠ 0 := by
    intro z hzs he
    exact hzero (he ▸ hzs)
  have hc : ContinuousOn (fun z : ℂ ↦ (z⁻¹)^2) (closedBall c r) :=
    (continuousOn_id.inv₀ hn).pow 2
  have hd : ∀ z ∈ ball c r \ (∅ : Set ℂ), DifferentiableAt ℂ (fun z : ℂ ↦ (z⁻¹)^2) z := by
    intro z hzs
    exact (differentiableAt_id.inv (hn z (ball_subset_closedBall hzs.1))).pow 2
  have hscalar := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    countable_empty hc hd
  let W := fun z : ℂ ↦ (z⁻¹)^2 • resolvent U z
  let L := ContinuousLinearMap.compL ℂ E E E U
  have hwc : ContinuousOn W (sphere c r) := by
    intro z hzs
    exact (((continuousAt_id.inv₀ (hn z (sphere_subset_closedBall hzs))).pow 2).smul
      (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).continuousAt).continuousWithinAt
  have hw : CircleIntegrable W c r := hwc.circleIntegrable hr
  have hg : CircleIntegrable (fun z : ℂ ↦ (z⁻¹)^2 • (1 : E →L[ℂ] E)) c r :=
    ((hc.mono sphere_subset_closedBall).smul continuousOn_const).circleIntegrable hr
  have hl : CircleIntegrable (fun z ↦ L (W z)) c r :=
    (L.continuous.comp_continuousOn hwc).circleIntegrable hr
  have he : circleIntegral (fun z : ℂ ↦ z⁻¹ • resolvent U z) c r =
      circleIntegral (fun z ↦ (z⁻¹)^2 • (1 : E →L[ℂ] E) + L (W z)) c r := by
    apply circleIntegral.integral_congr hr
    intro z hzs
    ext x
    have h := congrArg (fun y : E ↦ z⁻¹ • y)
      (resolvent_apply_eq_scalar_add U z (hz z hzs) (hn z (sphere_subset_closedBall hzs)) x)
    simpa [W, L, smul_add, map_smul, smul_smul, pow_two] using h
  unfold weightedCircleOperator twiceWeightedCircleOperator
  rw [he, circleIntegral.integral_add hg hl, smul_add,
    circleIntegral.integral_smul_const, hscalar, zero_smul, smul_zero, zero_add,
    ← map_circleIntegral L W c r hw]
  exact (map_smul L _ _).symm

theorem circleResolvent_square_factor (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    circleResolvent U c r = (U.comp U).comp (twiceWeightedCircleOperator U c r) := by
  rw [circleResolvent_factor U c r hr hzero hz,
    weightedCircleOperator_factor U c r hr hzero hz]
  rfl

theorem circleResolvent_range_le_square_range (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ closedBall c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    LinearMap.range (circleResolvent U c r).toLinearMap ≤
      LinearMap.range (U.comp U).toLinearMap := by
  rw [circleResolvent_square_factor U c r hr hzero hz]
  rintro y ⟨x,rfl⟩
  exact ⟨twiceWeightedCircleOperator U c r x,rfl⟩
theorem cutoffCircle_range_le_square_range (U : E →L[ℂ] E) (η B : ℝ)
    (hη : 0 < η) (hB : η < B)
    (hb : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    LinearMap.range (cutoffCircleOperator U η B).toLinearMap ≤ LinearMap.range (U.comp U).toLinearMap := by
  obtain ⟨hz,hw⟩ := cutoffCircle_spheres_resolvent U η B (hη.trans hB) hb hp hn
  obtain ⟨hzero,hzero'⟩ := cutoffCircle_disks_avoid_zero η B hη hB
  have h₁ := circleResolvent_range_le_square_range U _ _ (by linarith : 0 ≤ (B-η)/2) hzero hz
  have h₂ := circleResolvent_range_le_square_range U _ _ (by linarith : 0 ≤ (-η - -B)/2) hzero' hw
  rintro y ⟨x,rfl⟩
  exact (LinearMap.range (U.comp U).toLinearMap).add_mem (h₁ ⟨x,rfl⟩) (h₂ ⟨x,rfl⟩)

end PaperN.PartII
