import PaperN.PartII.BoxResolvent

namespace PaperN.PartII
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Resolvents along horizontal lines off a real spectrum are integrable. -/
theorem horizontal_resolvent_intervalIntegrable (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (y l r : ℝ) (hy : y ≠ 0) :
    IntervalIntegrable (fun x : ℝ ↦ resolvent U ((x : ℂ) + (y : ℂ) * Complex.I)) volume l r := by
  apply ContinuousOn.intervalIntegrable
  intro x _
  have hz : (x : ℂ) + (y : ℂ) * Complex.I ∈ resolventSet ℂ U := by
    apply mem_resolvent_of_im_ne_zero U hr
    simpa using hy
  exact ((spectrum.hasDerivAt_resolvent_const_left hz).continuousAt.comp
    (f := fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I)
    (by fun_prop)).continuousWithinAt

/-- Horizontal splitting does not require the splitting line to avoid spectrum:
its two oppositely oriented contributions cancel as total interval integrals. -/
theorem rectangleResolvent_split_horizontal (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l m r h : ℝ) (hh : h ≠ 0) :
    rectangleResolvent U l r h =
      rectangleResolvent U l m h + rectangleResolvent U m r h := by
  change boxResolvent U l r (-h) h = boxResolvent U l m (-h) h + boxResolvent U m r (-h) h
  simp only [boxResolvent_eq_boundary]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (horizontal_resolvent_intervalIntegrable U hr (-h) l m (neg_ne_zero.mpr hh))
    (horizontal_resolvent_intervalIntegrable U hr (-h) m r (neg_ne_zero.mpr hh)),
    ← intervalIntegral.integral_add_adjacent_intervals
    (horizontal_resolvent_intervalIntegrable U hr h l m hh)
    (horizontal_resolvent_intervalIntegrable U hr h m r hh)]
  simp only [smul_add, smul_sub]
  abel

/-- A real interval consisting of resolvent points selects no spectrum. -/
theorem rectangleResolvent_eq_zero_of_real_interval (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ)
    (hi : ∀ x ∈ uIcc l r, (x : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = 0 := by
  apply rectangleResolvent_eq_zero_of_closed_rectangle
  intro z hz
  exact mem_resolvent_of_re U hr (hi z.re hz.1)

/-- Moving the left endpoint through resolvent points preserves the integral. -/
theorem rectangleResolvent_move_left (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l l' r h : ℝ) (hh : h ≠ 0)
    (hi : ∀ x ∈ uIcc l l', (x : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = rectangleResolvent U l' r h := by
  rw [rectangleResolvent_split_horizontal U hr l l' r h hh,
    rectangleResolvent_eq_zero_of_real_interval U hr l l' h hi, zero_add]

/-- Moving the right endpoint through resolvent points preserves the integral. -/
theorem rectangleResolvent_move_right (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r r' h : ℝ) (hh : h ≠ 0)
    (hi : ∀ x ∈ uIcc r r', (x : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r' h = rectangleResolvent U l r h := by
  rw [rectangleResolvent_split_horizontal U hr l r r' h hh,
    rectangleResolvent_eq_zero_of_real_interval U hr r r' h hi, add_zero]

/-- Rectangles remain equivalent while each vertical side moves within a real
resolvent interval and the heights remain positive. -/
theorem rectangleResolvent_deformation (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l l' r r' h k : ℝ)
    (hh : 0 < h) (hk : 0 < k)
    (hl : ∀ x ∈ uIcc l l', (x : ℂ) ∈ resolventSet ℂ U)
    (hr' : ∀ x ∈ uIcc r r', (x : ℂ) ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = rectangleResolvent U l' r' k := by
  calc
    rectangleResolvent U l r h = rectangleResolvent U l' r h :=
      rectangleResolvent_move_left U hr l l' r h (ne_of_gt hh) hl
    _ = rectangleResolvent U l' r' h :=
      (rectangleResolvent_move_right U hr l' r r' h (ne_of_gt hh) hr').symm
    _ = rectangleResolvent U l' r' k :=
      rectangleResolvent_height_independent U hr l' r' h k hh hk
        (hl l' right_mem_uIcc) (hr' r' right_mem_uIcc)
end PaperN.PartII
