import PaperN.PartII.EigenRange

namespace PaperN.PartII
open Metric Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selector_eq_starProjection (U P : H →L[ℂ] H) (s : Set ℂ)
    (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (hfix : ∀ a ∈ s, ∀ v, U v = a • v → P v = v)
    (hkill : ∀ a ∉ s, ∀ v, U v = a • v → P v = 0) :
    P = (closedEigenSpan U s).starProjection := by
  have hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure]
    exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs
  have hid : P.comp P = P := by
    apply idempotent_of_dense_eigenspaces U P hd
    intro a v hv
    by_cases ha : a ∈ s
    · exact Or.inr (hfix a ha v hv)
    · exact Or.inl (hkill a ha v hv)
  have hrange := range_eq_closedEigenSpan U P s hd hfix hkill
  have hker := ker_eq_closedEigenSpan_compl U P s hd hfix hkill
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [← hrange]
    exact ⟨v, rfl⟩
  · apply closedEigenSpan_compl_le_orthogonal U hs s
    rw [← hker]
    change P (v - P v) = 0
    rw [map_sub]
    have hi : P (P v) = P v := DFunLike.congr_fun hid v
    rw [hi, sub_self]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def twoCircleResolvent (U : E →L[ℂ] E) (c d : ℂ) (r t : ℝ) : E →L[ℂ] E :=
  circleResolvent U c r + circleResolvent U d t

theorem twoCircleResolvent_fixes (U : E →L[ℂ] E) (c d : ℂ) (r t : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hw : ∀ z ∈ sphere d t, z ∈ resolventSet ℂ U)
    (hdis : Disjoint (ball c r) (ball d t))
    (a : ℂ) (ha : a ∈ ball c r ∪ ball d t) (v : E) (hv : U v = a • v) :
    twoCircleResolvent U c d r t v = v := by
  change circleResolvent U c r v + circleResolvent U d t v = v
  rcases ha with ha | ha
  · have hn : a ∉ ball d t := fun hb ↦ Set.disjoint_left.mp hdis ha hb
    rw [circleResolvent_fixes_inside U a c r hz ha v hv,
      circleResolvent_kills_not_inside U a d t ht hw hn v hv, add_zero]
  · have hn : a ∉ ball c r := fun hb ↦ Set.disjoint_left.mp hdis hb ha
    rw [circleResolvent_kills_not_inside U a c r hr hz hn v hv,
      circleResolvent_fixes_inside U a d t hw ha v hv, zero_add]

theorem twoCircleResolvent_kills (U : E →L[ℂ] E) (c d : ℂ) (r t : ℝ)
    (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hw : ∀ z ∈ sphere d t, z ∈ resolventSet ℂ U)
    (a : ℂ) (ha : a ∉ ball c r ∪ ball d t) (v : E) (hv : U v = a • v) :
    twoCircleResolvent U c d r t v = 0 := by
  change circleResolvent U c r v + circleResolvent U d t v = 0
  rw [circleResolvent_kills_not_inside U a c r hr hz (fun h ↦ ha (Or.inl h)) v hv,
    circleResolvent_kills_not_inside U a d t ht hw (fun h ↦ ha (Or.inr h)) v hv, add_zero]

theorem twoCircleResolvent_eq_starProjection (U : H →L[ℂ] H)
    (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (c d : ℂ) (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hw : ∀ z ∈ sphere d t, z ∈ resolventSet ℂ U)
    (hdis : Disjoint (ball c r) (ball d t)) :
    twoCircleResolvent U c d r t = (closedEigenSpan U (ball c r ∪ ball d t)).starProjection := by
  apply selector_eq_starProjection U _ _ hc hs
  · exact twoCircleResolvent_fixes U c d r t hr ht hz hw hdis
  · exact twoCircleResolvent_kills U c d r t hr ht hz hw

omit [CompleteSpace E] in
theorem circle_real_interval_resolvent (U : E →L[ℂ] E)
    (hreal : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (l b : ℝ) (hl : (l : ℂ) ∈ resolventSet ℂ U) (hb : (b : ℂ) ∈ resolventSet ℂ U) :
    ∀ z ∈ sphere (((l+b)/2 : ℝ) : ℂ) ((b-l)/2), z ∈ resolventSet ℂ U := by
  intro z hz
  by_contra hn
  have hi := hreal z hn
  have he : z = (z.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using hi
  rw [mem_sphere, he, Complex.isometry_ofReal.dist_eq, Real.dist_eq] at hz
  have hends : z.re = l ∨ z.re = b := by
    rcases le_total 0 (z.re - (l+b)/2) with h | h
    · rw [abs_of_nonneg h] at hz
      right; linarith
    · rw [abs_of_nonpos h] at hz
      left; linarith
  rcases hends with h | h
  · apply hn
    rw [he, h]
    exact hl
  · apply hn
    rw [he, h]
    exact hb

theorem real_mem_interval_ball (a l b : ℝ) :
    (a : ℂ) ∈ ball (((l+b)/2 : ℝ) : ℂ) ((b-l)/2) ↔ l < a ∧ a < b := by
  rw [mem_ball, Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

noncomputable def cutoffCircleOperator (U : E →L[ℂ] E) (η B : ℝ) : E →L[ℂ] E :=
  twoCircleResolvent U (((η+B)/2 : ℝ) : ℂ) (((-B + -η)/2 : ℝ) : ℂ)
    ((B-η)/2) ((-η - -B)/2)

theorem cutoffCircle_balls_disjoint (η B : ℝ) (hη : 0 ≤ η) (hB : η < B) :
    Disjoint (ball (((η+B)/2 : ℝ) : ℂ) ((B-η)/2))
      (ball (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2)) := by
  apply Metric.ball_disjoint_ball
  rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

theorem cutoffCircle_real_selection (a η B : ℝ) (hb : |a| < B) :
    (a : ℂ) ∈ ball (((η+B)/2 : ℝ) : ℂ) ((B-η)/2) ∪
      ball (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2) ↔ η < |a| := by
  simp only [mem_union, real_mem_interval_ball]
  have hab := abs_lt.mp hb
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h.trans_le (le_abs_self a)
    · exact lt_of_lt_of_le (by linarith : η < -a) (neg_le_abs a)
  · intro h
    rcases lt_abs.mp h with h | h
    · exact Or.inl ⟨h, hab.2⟩
    · exact Or.inr ⟨hab.1, by linarith⟩

theorem cutoffCircle_apply_eigenvector (U : E →L[ℂ] E) (η B : ℝ)
    (hη : 0 < η) (hB : η < B)
    (hbound : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U)
    (a : ℂ) (v : E) (hv : U v = a • v) :
    cutoffCircleOperator U η B v = if η < ‖a‖ then v else 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  have heig : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have haspec : a ∈ spectrum ℂ U := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact heig.mem_spectrum
  have ha := hbound a haspec
  have he : a = (a.re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa using ha.1
  have hanorm : ‖a‖ = |a.re| := by
    calc ‖a‖ = ‖(a.re : ℂ)‖ := congrArg norm he
         _ = |a.re| := by simp
  have hbpos : (B : ℂ) ∈ resolventSet ℂ U := by
    by_contra h
    have hh := (hbound _ h).2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hη.trans hB)] at hh
    exact (lt_irrefl B) hh
  have hbneg : ((-B : ℝ) : ℂ) ∈ resolventSet ℂ U := by
    by_contra h
    have hh := (hbound _ h).2
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (hη.trans hB)] at hh
    exact (lt_irrefl B) hh
  have hz := circle_real_interval_resolvent U (fun z hz ↦ (hbound z hz).1) η B hp hbpos
  have hw := circle_real_interval_resolvent U (fun z hz ↦ (hbound z hz).1) (-B) (-η) hbneg hn
  have hselect : a ∈ ball (((η+B)/2 : ℝ) : ℂ) ((B-η)/2) ∪
      ball (((-B + -η)/2 : ℝ) : ℂ) ((-η - -B)/2) ↔ η < ‖a‖ := by
    rw [hanorm, he]
    simpa only [Complex.ofReal_re] using
      cutoffCircle_real_selection a.re η B (by simpa only [hanorm] using ha.2)
  change twoCircleResolvent U _ _ _ _ v = _
  by_cases h : η < ‖a‖
  · rw [if_pos h]
    exact twoCircleResolvent_fixes U _ _ _ _ (by linarith) (by linarith) hz hw
      (cutoffCircle_balls_disjoint η B (le_of_lt hη) hB) a (hselect.mpr h) v hv
  · rw [if_neg h]
    exact twoCircleResolvent_kills U _ _ _ _ (by linarith) (by linarith) hz hw
      a (fun hh ↦ h (hselect.mp hh)) v hv

theorem cutoffCircle_eq_starProjection (U : H →L[ℂ] H)
    (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric) (η B : ℝ)
    (hη : 0 < η) (hB : η < B)
    (hbound : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    cutoffCircleOperator U η B = (closedEigenSpan U {a | η < ‖a‖}).starProjection := by
  apply selector_eq_starProjection U _ _ hc hs
  · intro a ha v hv
    rw [cutoffCircle_apply_eigenvector U η B hη hB hbound hp hn a v hv, if_pos (show η < ‖a‖ from ha)]
  · intro a ha v hv
    rw [cutoffCircle_apply_eigenvector U η B hη hB hbound hp hn a v hv, if_neg (show ¬ η < ‖a‖ from ha)]

namespace ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem distance_cutoffCircle_eq_starProjection (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hdiam : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) :
    cutoffCircleOperator (distanceOperator μ) η B =
      (closedEigenSpan (distanceOperator μ) {a | η < ‖a‖}).starProjection := by
  apply cutoffCircle_eq_starProjection _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) η B hη hB _ hp hn
  intro z hz
  obtain ⟨hi, hb⟩ := distanceOperator_spectrum_bound μ hz
  exact ⟨hi, hb.trans_lt hdiam⟩
theorem distance_cutoffCircle_explicit (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) :
    cutoffCircleOperator (distanceOperator μ) η (Metric.diam (Set.univ : Set X) + η + 1) =
      (closedEigenSpan (distanceOperator μ) {a | η < ‖a‖}).starProjection := by
  apply distance_cutoffCircle_eq_starProjection μ η _ hη _ _ hp hn
  · linarith [Metric.diam_nonneg (s := (Set.univ : Set X))]
  · linarith
end ComplexKernel
end PaperN.PartII
