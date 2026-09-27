import PaperN.PartII.CircleOperator

namespace PaperN.PartII
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The resolvent equation on vectors, with the original operator on the left. -/
theorem operator_apply_resolvent_eq (U : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ resolventSet ℂ U) (x : E) :
    U (resolvent U z x) = z • resolvent U z x - x := by
  have h := congrArg (fun T : E →L[ℂ] E ↦ T x)
    (Ring.mul_inverse_cancel (algebraMap ℂ (E →L[ℂ] E) z - U) hz)
  change (algebraMap ℂ (E →L[ℂ] E) z - U) (resolvent U z x) = x at h
  simp only [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self] at h
  exact eq_sub_of_add_eq (by simpa [add_comm] using (sub_eq_iff_eq_add.mp h).symm)

omit [CompleteSpace E] in
/-- Away from zero, the resolvent splits into a scalar term and an operator-range term. -/
theorem resolvent_apply_eq_scalar_add (U : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ resolventSet ℂ U) (hz0 : z ≠ 0) (x : E) :
    resolvent U z x = z⁻¹ • x + U (z⁻¹ • resolvent U z x) := by
  rw [map_smul, operator_apply_resolvent_eq U z hz x, smul_sub, smul_smul,
    inv_mul_cancel₀ hz0, one_smul]
  abel

/-- The weighted resolvent is integrable on a circle avoiding zero and the spectrum. -/
theorem weightedResolvent_circleIntegrable (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hzero : (0 : ℂ) ∉ sphere c r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    CircleIntegrable (fun z ↦ z⁻¹ • resolvent U z) c r := by
  apply ContinuousOn.circleIntegrable hr
  intro z hzs
  have hn : z ≠ 0 := fun he ↦ hzero (he ▸ hzs)
  exact ((continuousAt_id.inv₀ hn).smul
    (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).continuousAt).continuousWithinAt
end PaperN.PartII
