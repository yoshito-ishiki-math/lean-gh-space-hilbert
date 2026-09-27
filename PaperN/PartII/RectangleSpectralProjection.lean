import PaperN.PartII.RectangleScalarInside
import PaperN.PartII.TwoCircleProjection

namespace PaperN.PartII
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem rectangleResolvent_apply_eigenvector_ite (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ) (hlr : l < r) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (a : ℂ) (v : E) (hv : U v = a • v) :
    rectangleResolvent U l r h v = if l < a.re ∧ a.re < r then v else 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  have heig : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have haspec : a ∈ spectrum ℂ U := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact heig.mem_spectrum
  have he : a = (a.re : ℂ) := Complex.ext rfl (by simpa using hr a haspec)
  have hal : a.re ≠ l := by
    intro ha
    have he' : a = (l : ℂ) := he.trans (congrArg (fun x : ℝ ↦ (x : ℂ)) ha)
    exact haspec (he'.symm ▸ hl)
  have har : a.re ≠ r := by
    intro ha
    have he' : a = (r : ℂ) := he.trans (congrArg (fun x : ℝ ↦ (x : ℂ)) ha)
    exact haspec (he'.symm ▸ hr')
  by_cases ha : l < a.re ∧ a.re < r
  · rw [if_pos ha]
    exact rectangleResolvent_apply_inside U hr a.re l r h ha.1 ha.2 hh hl hr' v (by simpa [← he] using hv)
  · rw [if_neg ha]
    apply rectangleResolvent_apply_outside U hr l r h hh hl hr' a _ v hv
    intro hz
    have hb : a.re ∈ Icc l r := by simpa [uIcc_of_le hlr.le] using hz.1
    exact ha ⟨lt_of_le_of_ne hb.1 hal.symm, lt_of_le_of_ne hb.2 har⟩

/-- The rectangle integral of a compact symmetric Hilbert operator is its
orthogonal projection onto the closed sum of the selected eigenspaces. -/
theorem rectangleResolvent_eq_starProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ) (hlr : l < r) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = (closedEigenSpan U {a | l < a.re ∧ a.re < r}).starProjection := by
  apply selector_eq_starProjection U _ _ hc hs
  · intro a ha v hv
    rw [rectangleResolvent_apply_eigenvector_ite U hr l r h hlr hh hl hr' a v hv,
      if_pos (show l < a.re ∧ a.re < r from ha)]
  · intro a ha v hv
    rw [rectangleResolvent_apply_eigenvector_ite U hr l r h hlr hh hl hr' a v hv,
      if_neg (show ¬ (l < a.re ∧ a.re < r) from ha)]

theorem circleResolvent_realInterval_apply_eigenvector (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r : ℝ) (hlr : l < r)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (a : ℂ) (v : E) (hv : U v = a • v) :
    circleResolvent U (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) v =
      if l < a.re ∧ a.re < r then v else 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  have heig : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have haspec : a ∈ spectrum ℂ U := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact heig.mem_spectrum
  have he : a = (a.re : ℂ) := Complex.ext rfl (by simpa using hr a haspec)
  have hal : a.re ≠ l := by
    intro ha
    have he' : a = (l : ℂ) := he.trans (congrArg (fun x : ℝ ↦ (x : ℂ)) ha)
    exact haspec (he'.symm ▸ hl)
  have har : a.re ≠ r := by
    intro ha
    have he' : a = (r : ℂ) := he.trans (congrArg (fun x : ℝ ↦ (x : ℂ)) ha)
    exact haspec (he'.symm ▸ hr')
  have hz := circle_real_interval_resolvent U hr l r hl hr'
  rw [circleResolvent_apply_eigenvector U a _ _ (by linarith) hz
    (fun ha ↦ haspec (hz a ha)) v hv]
  by_cases ha : l < a.re ∧ a.re < r
  · rw [if_pos ha, he, scalarCircle_real_interval_inside a.re l r ha.1 ha.2, one_smul]
  · have hout : a.re < l ∨ r < a.re := by
      rcases lt_or_gt_of_ne hal with hleft | hleft
      · exact Or.inl hleft
      · exact Or.inr (lt_of_le_of_ne (le_of_not_gt (fun h ↦ ha ⟨hleft,h⟩)) har.symm)
    rw [if_neg ha, he, scalarCircle_real_interval_outside a.re l r hlr.le hout, zero_smul]

/-- Rectangle-circle comparison for compact symmetric Hilbert operators. -/
theorem rectangleResolvent_eq_circle_of_compact_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ) (hlr : l < r) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = circleResolvent U (((l+r)/2 : ℝ) : ℂ) ((r-l)/2) := by
  rw [rectangleResolvent_eq_starProjection U hc hs hr l r h hlr hh hl hr']
  symm
  apply selector_eq_starProjection U _ _ hc hs
  · intro a ha v hv
    rw [circleResolvent_realInterval_apply_eigenvector U hr l r hlr hl hr' a v hv,
      if_pos (show l < a.re ∧ a.re < r from ha)]
  · intro a ha v hv
    rw [circleResolvent_realInterval_apply_eigenvector U hr l r hlr hl hr' a v hv,
      if_neg (show ¬ (l < a.re ∧ a.re < r) from ha)]
end PaperN.PartII
