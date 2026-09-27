import PaperN.PartII.ContourEigenvector
import PaperN.PartII.RectangleCauchyBridge

namespace PaperN.PartII
open MeasureTheory Set

/-- The scalar rectangle integral vanishes when its pole is outside the closed rectangle. -/
theorem scalarRectangle_outside (a : ℂ) (l r h : ℝ)
    (ha : a ∉ uIcc l r ×ℂ uIcc (-h) h) : scalarRectangle a l r h = 0 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ ↦ (z-a)⁻¹)
      (uIcc l r ×ℂ uIcc (-h) h) := by
    intro z hz
    exact ((differentiableAt_id.sub_const a).inv
      (fun he ↦ ha (sub_eq_zero.mp he ▸ hz))).differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (fun z : ℂ ↦ (z-a)⁻¹) (⟨l,-h⟩ : ℂ) (⟨r,h⟩ : ℂ) hd
  have H (x y t : ℝ) := horizontal_segment_integral (fun z : ℂ ↦ (z-a)⁻¹) x y t
  have V (x b t : ℝ) := vertical_segment_integral (fun z : ℂ ↦ (z-a)⁻¹) x b t
  simp only [smul_eq_mul] at H V hc
  unfold scalarRectangle scalarQuadrilateral scalarSegment
  rw [H, V, H, V, intervalIntegral.integral_symm l r,
    intervalIntegral.integral_symm (-h) h, mul_neg]
  have he : (∫ x in l..r, ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I-a)⁻¹) +
      Complex.I * (∫ y in (-h)..h, ((r : ℂ) + (y : ℂ) * Complex.I-a)⁻¹) +
      -(∫ x in l..r, ((x : ℂ) + (h : ℂ) * Complex.I-a)⁻¹) +
      -(Complex.I * (∫ y in (-h)..h, ((l : ℂ) + (y : ℂ) * Complex.I-a)⁻¹)) = 0 := by
    convert hc using 1 <;> ring
  rw [he, mul_zero]

/-- A real pole outside the horizontal interval contributes zero. -/
theorem scalarRectangle_real_outside (a l r h : ℝ) (ha : a ∉ uIcc l r) :
    scalarRectangle (a : ℂ) l r h = 0 := by
  apply scalarRectangle_outside
  intro hz
  exact ha hz.1

/-- The actual rectangle operator kills an eigenvector whose eigenvalue lies
outside its closed rectangle, under the existing edge conditions. -/
theorem rectangleResolvent_kills_outside_eigenvector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (a : ℂ) (l r h : ℝ)
    (hc : RectangleEigenCondition U a l r h)
    (ha : a ∉ uIcc l r ×ℂ uIcc (-h) h)
    (v : E) (hv : U v = a • v) : rectangleResolvent U l r h v = 0 := by
  rw [rectangleResolvent_apply_eigenvector U a l r h hc v hv,
    scalarRectangle_outside a l r h ha, zero_smul]

/-- Spectral membership supplies the pole-avoidance part of the edge conditions. -/
theorem rectangleEigenCondition_of_mem_spectrum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hr : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (a : ℂ) (ha : a ∈ spectrum ℂ U) (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    RectangleEigenCondition U a l r h := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := rectangle_edges_resolvent U hr l r h hh hl hr'
  have H (p q : ℂ) (hz : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ∈ resolventSet ℂ U) :
      EigenEdgeCondition U a p q := by
    intro t ht
    exact ⟨hz t ht, fun he ↦ ha (he ▸ hz t ht)⟩
  exact ⟨H _ _ h₁,H _ _ h₂,H _ _ h₃,H _ _ h₄⟩

/-- Outside eigenvectors vanish under the standard real-spectrum contour hypotheses. -/
theorem rectangleResolvent_apply_outside
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : E →L[ℂ] E) (hr : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (a : ℂ) (ha : a ∉ uIcc l r ×ℂ uIcc (-h) h)
    (v : E) (hv : U v = a • v) : rectangleResolvent U l r h v = 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  have heig : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have haspec : a ∈ spectrum ℂ U := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact heig.mem_spectrum
  exact rectangleResolvent_kills_outside_eigenvector U a l r h
    (rectangleEigenCondition_of_mem_spectrum U hr a haspec l r h hh hl hr') ha v hv
end PaperN.PartII
