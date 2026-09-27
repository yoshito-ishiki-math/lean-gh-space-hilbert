import PaperN.PartII.WeightedResolvent
import PaperN.PartII.SegmentLogIntegral

namespace PaperN.PartII
open MeasureTheory Set

/-- Second-order resolvent expansion away from zero, on vectors. -/
theorem resolvent_apply_eq_second_order
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (U : E →L[ℂ] E) (z : ℂ) (hz : z ∈ resolventSet ℂ U) (hz0 : z ≠ 0) (x : E) :
    resolvent U z x = z⁻¹ • x + (z⁻¹)^2 • U x +
      (U.comp U) ((z⁻¹)^2 • resolvent U z x) := by
  have h := resolvent_apply_eq_scalar_add U z hz hz0 x
  calc
    resolvent U z x = z⁻¹ • x + U (z⁻¹ • resolvent U z x) := h
    _ = z⁻¹ • x + U (z⁻¹ • (z⁻¹ • x + U (z⁻¹ • resolvent U z x))) :=
      congrArg (fun y ↦ z⁻¹ • x + U (z⁻¹ • y)) h
    _ = _ := by simp [smul_add, map_add, map_smul, smul_smul, pow_two, add_assoc]

/-- The inverse-square scalar segment integral has an elementary primitive. -/
theorem segment_inverse_square_integral (p q : ℂ)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ≠ 0) :
    (∫ t in (0 : ℝ)..1, (q-p) * (segmentParameter p q t)⁻¹ ^ 2) = p⁻¹-q⁻¹ := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ -(segmentParameter p q t)⁻¹)
        ((q-p)*(segmentParameter p q t)⁻¹ ^ 2) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hf : HasDerivAt (fun z : ℂ ↦ p+z*(q-p)) (q-p) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const (q-p)).const_add p
    have hi := ((hf.inv (hz t ht')).neg).comp_ofReal
    convert hi using 1
    · dsimp [segmentParameter]
    · simp [segmentParameter, div_eq_mul_inv, inv_pow]
      <;> ring
  have hi : IntervalIntegrable (fun t : ℝ ↦ (q-p)*(segmentParameter p q t)⁻¹ ^ 2) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    have hp : ContinuousAt (segmentParameter p q) t := by unfold segmentParameter; fun_prop
    exact (continuousAt_const.mul ((hp.inv₀ (hz t ht)).pow 2)).continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa [segmentParameter, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using he

/-- Inverse-square integrals cancel around all four oriented edges. -/
theorem quadrilateral_inverse_square_integral (p q r s : ℂ)
    (hpq : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ≠ 0)
    (hqr : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter q r t ≠ 0)
    (hrs : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter r s t ≠ 0)
    (hsp : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter s p t ≠ 0) :
    (∫ t in (0 : ℝ)..1, (q-p)*(segmentParameter p q t)⁻¹ ^ 2) +
    (∫ t in (0 : ℝ)..1, (r-q)*(segmentParameter q r t)⁻¹ ^ 2) +
    (∫ t in (0 : ℝ)..1, (s-r)*(segmentParameter r s t)⁻¹ ^ 2) +
    (∫ t in (0 : ℝ)..1, (p-s)*(segmentParameter s p t)⁻¹ ^ 2) = 0 := by
  rw [segment_inverse_square_integral p q hpq, segment_inverse_square_integral q r hqr,
    segment_inverse_square_integral r s hrs, segment_inverse_square_integral s p hsp]
  ring
end PaperN.PartII
