import PaperN.PartII.SegmentResolvent

namespace PaperN.PartII
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem mem_resolvent_of_im_ne_zero (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ U := by
  by_contra h
  exact hz (hr z h)

omit [CompleteSpace E] in
theorem mem_resolvent_of_re (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0) {z : ℂ}
    (hz : (z.re : ℂ) ∈ resolventSet ℂ U) : z ∈ resolventSet ℂ U := by
  by_contra h
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hr z h)
  exact h (he ▸ hz)

omit [CompleteSpace E] in
/-- Lower, right, upper, left edges; positive orientation when l < r. -/
theorem rectangle_edges_resolvent (U : E →L[ℂ] E)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    (∀ t ∈ Icc (0 : ℝ) 1, segmentParameter ⟨l,-h⟩ ⟨r,-h⟩ t ∈ resolventSet ℂ U) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, segmentParameter ⟨r,-h⟩ ⟨r,h⟩ t ∈ resolventSet ℂ U) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, segmentParameter ⟨r,h⟩ ⟨l,h⟩ t ∈ resolventSet ℂ U) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, segmentParameter ⟨l,h⟩ ⟨l,-h⟩ t ∈ resolventSet ℂ U) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _
    apply mem_resolvent_of_im_ne_zero U hr
    simpa [segmentParameter, Complex.mul_im] using neg_ne_zero.mpr (ne_of_gt hh)
  · intro t _
    apply mem_resolvent_of_re U hr
    simpa [segmentParameter, Complex.mul_re] using hr'
  · intro t _
    apply mem_resolvent_of_im_ne_zero U hr
    simpa [segmentParameter, Complex.mul_im] using ne_of_gt hh
  · intro t _
    apply mem_resolvent_of_re U hr
    simpa [segmentParameter, Complex.mul_re] using hl

noncomputable def rectangleResolvent (U : E →L[ℂ] E) (l r h : ℝ) : E →L[ℂ] E :=
  quadrilateralResolvent U ⟨l,-h⟩ ⟨r,-h⟩ ⟨r,h⟩ ⟨l,h⟩

theorem rectangleResolvent_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (hc : ∀ x, R (U x) = T (R x))
    (hU : ∀ z ∈ spectrum ℂ U, z.im = 0) (hT : ∀ z ∈ spectrum ℂ T, z.im = 0)
    (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hr : (r : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T) :
    R.comp (rectangleResolvent U l r h) = (rectangleResolvent T l r h).comp R := by
  obtain ⟨u₁,u₂,u₃,u₄⟩ := rectangle_edges_resolvent U hU l r h hh hl.1 hr.1
  obtain ⟨t₁,t₂,t₃,t₄⟩ := rectangle_edges_resolvent T hT l r h hh hl.2 hr.2
  exact quadrilateralResolvent_intertwine U T R hc _ _ _ _
    (fun t ht ↦ ⟨u₁ t ht,t₁ t ht⟩) (fun t ht ↦ ⟨u₂ t ht,t₂ t ht⟩)
    (fun t ht ↦ ⟨u₃ t ht,t₃ t ht⟩) (fun t ht ↦ ⟨u₄ t ht,t₄ t ht⟩)
/-- The union of the positive and negative cutoff rectangles. -/
def cutoffRectangles (η B h : ℝ) : Set ℂ :=
  {z | ((η < z.re ∧ z.re < B) ∨ (-B < z.re ∧ z.re < -η)) ∧ |z.im| < h}

theorem cutoffRectangles_spectral_selection (S : Set ℂ) (η B h : ℝ)
    (hr : ∀ z ∈ S, z.im = 0) (hb : ∀ z ∈ S, ‖z‖ < B) (hh : 0 < h) :
    cutoffRectangles η B h ∩ S = {z ∈ S | η < ‖z‖} := by
  ext z
  by_cases hz : z ∈ S
  · have hi := hr z hz
    have hn : ‖z‖ = |z.re| := by
      have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hi)
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      rfl
    have hd := hb z hz
    rw [hn] at hd
    have hd' := abs_lt.mp hd
    simp only [mem_inter_iff, cutoffRectangles, mem_setOf_eq, hz, and_true, true_and, hi,
      abs_zero, hh, hn]
    constructor
    · rintro (hp | hn)
      · exact lt_of_lt_of_le hp.1 (le_abs_self _)
      · exact lt_of_lt_of_le (by linarith [hn.2]) (neg_le_abs _)
    · intro ha
      rcases lt_abs.mp ha with hp | hn
      · exact Or.inl ⟨hp,hd'.2⟩
      · exact Or.inr ⟨hd'.1, by linarith⟩
  · simp [hz]
end PaperN.PartII
