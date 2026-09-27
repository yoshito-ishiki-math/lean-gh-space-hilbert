import PaperN.PartII.SegmentLogIntegral
import PaperN.PartII.RectangleScalarOutside

namespace PaperN.PartII
open Set

theorem scalarRectangle_real_inside (a l r h : ℝ)
    (hl : l < a) (hr : a < r) (hh : 0 < h) :
    scalarRectangle (a : ℂ) l r h = 1 := by
  have H (x y b : ℝ) (hb : b ≠ 0) :
      scalarSegment (a : ℂ) ⟨x,b⟩ ⟨y,b⟩ =
        Complex.log ((⟨y,b⟩ : ℂ)-a) - Complex.log ((⟨x,b⟩ : ℂ)-a) := by
    have he := scalarSegment_eq_rotated_log (a : ℂ) ⟨x,b⟩ ⟨y,b⟩ 1 one_ne_zero (by
      intro t ht
      apply Complex.mem_slitPlane_iff.mpr
      right
      simpa [segmentParameter, Complex.mul_im] using hb)
    simpa using he
  have h₁ := H l r (-h) (neg_ne_zero.mpr (ne_of_gt hh))
  have h₃ := H r l h (ne_of_gt hh)
  have h₂ := scalarSegment_eq_rotated_log (a : ℂ) ⟨r,-h⟩ ⟨r,h⟩ 1 one_ne_zero (by
    intro t ht
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa [segmentParameter, Complex.mul_re] using sub_pos.mpr hr)
  have h₄ := scalarSegment_eq_rotated_log (a : ℂ) ⟨l,h⟩ ⟨l,-h⟩ (-1) (by norm_num) (by
    intro t ht
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp [segmentParameter, Complex.mul_re]
    linarith)
  simp only [one_mul, neg_one_mul] at h₂ h₄
  have hb : Complex.log (-((⟨l,-h⟩ : ℂ)-a)) =
      Complex.log ((⟨l,-h⟩ : ℂ)-a) + (Real.pi : ℂ) * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using neg_lt_zero.mpr hh)]
    push_cast
    ring
  have ht : Complex.log (-((⟨l,h⟩ : ℂ)-a)) =
      Complex.log ((⟨l,h⟩ : ℂ)-a) - (Real.pi : ℂ) * Complex.I := by
    rw [Complex.log, Complex.log, norm_neg,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by simpa using hh)]
    push_cast
    ring
  unfold scalarRectangle scalarQuadrilateral
  rw [h₁,h₂,h₃,h₄,hb,ht]
  have hn : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp
  <;> ring

/-- The rectangle operator fixes eigenvectors with real eigenvalue strictly inside. -/
theorem rectangleResolvent_apply_inside
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hs : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (a l r h : ℝ) (hl : l < a) (hr : a < r) (hh : 0 < h)
    (hlr : (l : ℂ) ∈ resolventSet ℂ U) (hrr : (r : ℂ) ∈ resolventSet ℂ U)
    (v : E) (hv : U v = (a : ℂ) • v) : rectangleResolvent U l r h v = v := by
  by_cases hzero : v = 0
  · simp [hzero]
  have heig : Module.End.HasEigenvalue U.toLinearMap (a : ℂ) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have haspec : (a : ℂ) ∈ spectrum ℂ U := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact heig.mem_spectrum
  rw [rectangleResolvent_apply_eigenvector U (a : ℂ) l r h
    (rectangleEigenCondition_of_mem_spectrum U hs (a : ℂ) haspec l r h hh hlr hrr) v hv,
    scalarRectangle_real_inside a l r h hl hr hh, one_smul]
end PaperN.PartII
