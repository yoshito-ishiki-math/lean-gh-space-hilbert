import PaperN.PartII.RectangleCauchyBridge

namespace PaperN.PartII
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A positively oriented box integral, allowing nonsymmetric vertical bounds. -/
noncomputable def boxResolvent (U : E →L[ℂ] E) (l r b t : ℝ) : E →L[ℂ] E :=
  quadrilateralResolvent U ⟨l,b⟩ ⟨r,b⟩ ⟨r,t⟩ ⟨l,t⟩

omit [CompleteSpace E] in
theorem boxResolvent_eq_boundary (U : E →L[ℂ] E) (l r b t : ℝ) :
    boxResolvent U l r b t = (2 * Real.pi * Complex.I)⁻¹ •
      ((∫ x in l..r, resolvent U ((x : ℂ) + (b : ℂ) * Complex.I)) -
       (∫ x in l..r, resolvent U ((x : ℂ) + (t : ℂ) * Complex.I)) +
       Complex.I • (∫ y in b..t, resolvent U ((r : ℂ) + (y : ℂ) * Complex.I)) -
       Complex.I • (∫ y in b..t, resolvent U ((l : ℂ) + (y : ℂ) * Complex.I))) := by
  unfold boxResolvent quadrilateralResolvent segmentResolvent
  rw [horizontal_segment_integral, vertical_segment_integral,
    horizontal_segment_integral, vertical_segment_integral]
  rw [intervalIntegral.integral_symm l r, intervalIntegral.integral_symm b t, smul_neg]
  congr 1
  abel

theorem boxResolvent_eq_zero_of_closed_box (U : E →L[ℂ] E) (l r b t : ℝ)
    (hz : ∀ z ∈ uIcc l r ×ℂ uIcc b t, z ∈ resolventSet ℂ U) :
    boxResolvent U l r b t = 0 := by
  have hd : DifferentiableOn ℂ (resolvent U) (uIcc l r ×ℂ uIcc b t) := by
    intro z hzs
    exact (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).differentiableAt.differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (resolvent U) (⟨l,b⟩ : ℂ) (⟨r,t⟩ : ℂ) hd
  rw [boxResolvent_eq_boundary]
  change _ = 0 at hc
  rw [hc, smul_zero]

/-- Boxes strictly above or below a real spectrum contribute zero. -/
theorem boxResolvent_eq_zero_of_im_interval (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r b t : ℝ)
    (hbt : (0 : ℝ) ∉ uIcc b t) : boxResolvent U l r b t = 0 := by
  apply boxResolvent_eq_zero_of_closed_box
  intro z hz
  apply mem_resolvent_of_im_ne_zero U hr
  intro he
  exact hbt (he ▸ hz.2)

/-- Moving a horizontal cut partitions the box integral, provided the two
vertical sides are integrable on both subintervals. -/
theorem boxResolvent_split_vertical (U : E →L[ℂ] E) (l r b m t : ℝ)
    (hlb : IntervalIntegrable (fun y : ℝ ↦ resolvent U ((l : ℂ) + (y : ℂ) * Complex.I)) volume b m)
    (hlt : IntervalIntegrable (fun y : ℝ ↦ resolvent U ((l : ℂ) + (y : ℂ) * Complex.I)) volume m t)
    (hrb : IntervalIntegrable (fun y : ℝ ↦ resolvent U ((r : ℂ) + (y : ℂ) * Complex.I)) volume b m)
    (hrt : IntervalIntegrable (fun y : ℝ ↦ resolvent U ((r : ℂ) + (y : ℂ) * Complex.I)) volume m t) :
    boxResolvent U l r b t = boxResolvent U l r b m + boxResolvent U l r m t := by
  simp only [boxResolvent_eq_boundary]
  rw [← intervalIntegral.integral_add_adjacent_intervals hlb hlt,
    ← intervalIntegral.integral_add_adjacent_intervals hrb hrt]
  simp only [smul_add, smul_sub]
  abel

theorem vertical_resolvent_intervalIntegrable (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (x b t : ℝ)
    (hx : (x : ℂ) ∈ resolventSet ℂ U) :
    IntervalIntegrable (fun y : ℝ ↦ resolvent U ((x : ℂ) + (y : ℂ) * Complex.I)) volume b t := by
  apply ContinuousOn.intervalIntegrable
  intro y _
  have hz : (x : ℂ) + (y : ℂ) * Complex.I ∈ resolventSet ℂ U := by
    apply mem_resolvent_of_re U hr
    simpa using hx
  exact ((spectrum.hasDerivAt_resolvent_const_left hz).continuousAt.comp (f := fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I)
    (by fun_prop : ContinuousAt (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) y)).continuousWithinAt

/-- For real spectrum, the rectangle integral is independent of positive height. -/
theorem rectangleResolvent_height_independent (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h k : ℝ)
    (hh : 0 < h) (hk : 0 < k)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = rectangleResolvent U l r k := by
  have H (b m t : ℝ) := boxResolvent_split_vertical U l r b m t
    (vertical_resolvent_intervalIntegrable U hr l b m hl)
    (vertical_resolvent_intervalIntegrable U hr l m t hl)
    (vertical_resolvent_intervalIntegrable U hr r b m hr')
    (vertical_resolvent_intervalIntegrable U hr r m t hr')
  have hz₁ : boxResolvent U l r (-h) (-k) = 0 := by
    apply boxResolvent_eq_zero_of_im_interval U hr
    intro hz
    rcases mem_uIcc.mp hz with hz | hz <;> linarith [hz.2]
  have hz₂ : boxResolvent U l r k h = 0 := by
    apply boxResolvent_eq_zero_of_im_interval U hr
    intro hz
    rcases mem_uIcc.mp hz with hz | hz <;> linarith [hz.1]
  change boxResolvent U l r (-h) h = boxResolvent U l r (-k) k
  rw [H (-h) (-k) h, H (-k) k h, hz₁, hz₂, zero_add, add_zero]
end PaperN.PartII
