import PaperN.PartII.SecondOrderResolvent
import PaperN.PartII.RectangleScalarOutside

namespace PaperN.PartII
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def twiceWeightedSegment (U : E →L[ℂ] E) (p q : ℂ) : E →L[ℂ] E :=
  ∫ t in (0 : ℝ)..1, ((q-p)*(segmentParameter p q t)⁻¹ ^ 2) • resolvent U (segmentParameter p q t)

/-- The integrated second-order resolvent expansion on one edge. -/
theorem segmentResolvent_second_order (U : E →L[ℂ] E) (p q : ℂ)
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ∈ resolventSet ℂ U)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ≠ 0) :
    segmentResolvent U p q = scalarSegment 0 p q • (1 : E →L[ℂ] E) +
      (p⁻¹-q⁻¹) • U + (U.comp U).comp (twiceWeightedSegment U p q) := by
  let f := fun t : ℝ ↦ (q-p)*(segmentParameter p q t)⁻¹
  let g := fun t : ℝ ↦ (q-p)*(segmentParameter p q t)⁻¹ ^ 2
  let W := fun t : ℝ ↦ g t • resolvent U (segmentParameter p q t)
  let L := ContinuousLinearMap.compL ℂ E E E (U.comp U)
  have hc (t : ℝ) : ContinuousAt (segmentParameter p q) t := by unfold segmentParameter; fun_prop
  have hf : ContinuousOn f (Icc 0 1) := by
    intro t ht
    exact (continuousAt_const.mul ((hc t).inv₀ (hzero t ht))).continuousWithinAt
  have hg : ContinuousOn g (Icc 0 1) := by
    intro t ht
    exact (continuousAt_const.mul (((hc t).inv₀ (hzero t ht)).pow 2)).continuousWithinAt
  have hw : ContinuousOn W (Icc 0 1) := by
    intro t ht
    exact (hg t ht).smul (((spectrum.hasDerivAt_resolvent_const_left (hz t ht)).continuousAt.comp
      (f := segmentParameter p q) (hc t)).continuousWithinAt)
  have hfi := (hf.smul (continuousOn_const (c := (1 : E →L[ℂ] E)))).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hgi := (hg.smul (continuousOn_const (c := U))).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hwi := hw.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hli := (L.continuous.comp_continuousOn hw).intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  change IntervalIntegrable (fun t ↦ f t • (1 : E →L[ℂ] E)) volume 0 1 at hfi
  change IntervalIntegrable (fun t ↦ g t • U) volume 0 1 at hgi
  change IntervalIntegrable (fun t ↦ L (W t)) volume 0 1 at hli
  have he : segmentResolvent U p q = ∫ t in (0 : ℝ)..1,
      (f t • (1 : E →L[ℂ] E) + g t • U) + L (W t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    ext x
    have hv := congrArg (fun y : E ↦ (q-p) • y)
      (resolvent_apply_eq_second_order U _ (hz t ht') (hzero t ht') x)
    simpa [f,g,W,L,smul_add,smul_smul,map_smul] using hv
  rw [he, intervalIntegral.integral_add (hfi.add hgi) hli,
    intervalIntegral.integral_add hfi hgi, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_smul_const, L.intervalIntegral_comp_comm hwi]
  change (∫ t in (0 : ℝ)..1, f t) • (1 : E →L[ℂ] E) +
    (∫ t in (0 : ℝ)..1, g t) • U + L (∫ t in (0 : ℝ)..1, W t) = _
  have hfe : (∫ t in (0 : ℝ)..1, f t) = scalarSegment 0 p q := by simp [f,scalarSegment]
  have hge : (∫ t in (0 : ℝ)..1, g t) = p⁻¹-q⁻¹ := segment_inverse_square_integral p q hzero
  rw [hfe,hge]
  rfl

noncomputable def twiceWeightedQuadrilateral (U : E →L[ℂ] E) (p q r s : ℂ) : E →L[ℂ] E :=
  (2 * Real.pi * Complex.I)⁻¹ • (twiceWeightedSegment U p q + twiceWeightedSegment U q r +
    twiceWeightedSegment U r s + twiceWeightedSegment U s p)

/-- The inverse-square coefficient cancels after summing the four edges. -/
theorem quadrilateralResolvent_second_order (U : E →L[ℂ] E) (p q r s : ℂ)
    (hpq : EigenEdgeCondition U 0 p q) (hqr : EigenEdgeCondition U 0 q r)
    (hrs : EigenEdgeCondition U 0 r s) (hsp : EigenEdgeCondition U 0 s p) :
    quadrilateralResolvent U p q r s = scalarQuadrilateral 0 p q r s • (1 : E →L[ℂ] E) +
      (U.comp U).comp (twiceWeightedQuadrilateral U p q r s) := by
  have H (a b : ℂ) (h : EigenEdgeCondition U 0 a b) :=
    segmentResolvent_second_order U a b (fun t ht ↦ (h t ht).1) (fun t ht ↦ (h t ht).2)
  unfold quadrilateralResolvent
  rw [H p q hpq,H q r hqr,H r s hrs,H s p hsp]
  ext x
  simp [twiceWeightedQuadrilateral, scalarQuadrilateral, add_smul, sub_smul, mul_smul,
    smul_add, smul_sub, map_add, map_sub, map_smul]
  <;> abel

/-- If the scalar winding term vanishes, the four-edge integral factors through U squared. -/
theorem quadrilateralResolvent_square_factor (U : E →L[ℂ] E) (p q r s : ℂ)
    (hpq : EigenEdgeCondition U 0 p q) (hqr : EigenEdgeCondition U 0 q r)
    (hrs : EigenEdgeCondition U 0 r s) (hsp : EigenEdgeCondition U 0 s p)
    (hz : scalarQuadrilateral 0 p q r s = 0) :
    quadrilateralResolvent U p q r s = (U.comp U).comp (twiceWeightedQuadrilateral U p q r s) := by
  rw [quadrilateralResolvent_second_order U p q r s hpq hqr hrs hsp, hz, zero_smul, zero_add]

/-- Rectangle edges avoid zero if their height and vertical-side coordinates do. -/
theorem rectangle_zero_edge_condition (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (hl0 : l ≠ 0) (hr0 : r ≠ 0) : RectangleEigenCondition U 0 l r h := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := rectangle_edges_resolvent U hr l r h hh hl hr'
  refine ⟨?_,?_,?_,?_⟩
  · intro t ht
    refine ⟨h₁ t ht, ?_⟩
    intro he
    have hi := congrArg Complex.im he
    simp [segmentParameter, Complex.mul_im] at hi
    linarith
  · intro t ht
    refine ⟨h₂ t ht, ?_⟩
    intro he
    have hi := congrArg Complex.re he
    exact hr0 (by simpa [segmentParameter, Complex.mul_re] using hi)
  · intro t ht
    refine ⟨h₃ t ht, ?_⟩
    intro he
    have hi := congrArg Complex.im he
    simp [segmentParameter, Complex.mul_im] at hi
    linarith
  · intro t ht
    refine ⟨h₄ t ht, ?_⟩
    intro he
    have hi := congrArg Complex.re he
    exact hl0 (by simpa [segmentParameter, Complex.mul_re] using hi)

/-- A rectangle whose real interval avoids zero has range in the range of U squared. -/
theorem rectangleResolvent_range_le_square_range (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (hz : (0 : ℝ) ∉ uIcc l r) :
    LinearMap.range (rectangleResolvent U l r h).toLinearMap ≤
      LinearMap.range (U.comp U).toLinearMap := by
  have hl0 : l ≠ 0 := fun he ↦ hz (he ▸ left_mem_uIcc)
  have hr0 : r ≠ 0 := fun he ↦ hz (he ▸ right_mem_uIcc)
  obtain ⟨h₁,h₂,h₃,h₄⟩ := rectangle_zero_edge_condition U hr l r h hh hl hr' hl0 hr0
  have he := quadrilateralResolvent_square_factor U _ _ _ _ h₁ h₂ h₃ h₄
    (scalarRectangle_real_outside 0 l r h hz)
  change rectangleResolvent U l r h = _ at he
  rw [he]
  rintro y ⟨x,rfl⟩
  exact ⟨twiceWeightedQuadrilateral U _ _ _ _ x,rfl⟩
end PaperN.PartII
