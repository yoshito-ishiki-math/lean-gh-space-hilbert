import PaperN.PartII.CutoffContour

namespace PaperN.PartII
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem resolvent_apply_eigenvector (U : E →L[ℂ] E) (a z : ℂ)
    (hz : z ∈ resolventSet ℂ U) (hza : z ≠ a) (v : E) (hv : U v = a • v) :
    resolvent U z v = (z-a)⁻¹ • v := by
  have hi := Ring.inverse_mul_cancel (algebraMap ℂ (E →L[ℂ] E) z - U) hz
  have he : (algebraMap ℂ (E →L[ℂ] E) z - U) ((z-a)⁻¹ • v) = v := by
    simp only [Algebra.algebraMap_eq_smul_one, sub_apply,
      smul_apply, one_apply_eq_self, map_smul, hv]
    rw [← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hza), one_smul]
  calc
    resolvent U z v = resolvent U z ((algebraMap ℂ (E →L[ℂ] E) z - U) ((z-a)⁻¹ • v)) := by rw [he]
    _ = (z-a)⁻¹ • v := congrArg (fun A : E →L[ℂ] E ↦ A ((z-a)⁻¹ • v)) hi
theorem segmentResolvent_apply_eigenvector (U : E →L[ℂ] E) (a p q : ℂ)
    (hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, segmentParameter p q t ∈ resolventSet ℂ U)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, segmentParameter p q t ≠ a)
    (v : E) (hv : U v = a • v) :
    segmentResolvent U p q v =
      (∫ t in (0 : ℝ)..1, (q-p) * (segmentParameter p q t-a)⁻¹) • v := by
  rw [segmentResolvent, ContinuousLinearMap.intervalIntegral_apply
    (segmentResolvent_integrable U p q hz), ← intervalIntegral.integral_smul_const]
  apply intervalIntegral.integral_congr
  intro t ht
  have hh : t ∈ Set.Icc (0 : ℝ) 1 := by simpa using ht
  change (q-p) • resolvent U (segmentParameter p q t) v = _
  rw [resolvent_apply_eigenvector U a _ (hz t hh) (ha t hh) v hv, smul_smul]
end PaperN.PartII
