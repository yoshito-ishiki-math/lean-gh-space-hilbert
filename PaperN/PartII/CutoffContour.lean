import PaperN.PartII.RectangleResolvent

namespace PaperN.PartII
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def cutoffOuter (D η : ℝ) : ℝ := D + η + 1

theorem cutoffOuter_gt (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η) :
    D < cutoffOuter D η ∧ η < cutoffOuter D η := by
  unfold cutoffOuter; constructor <;> linarith

omit [CompleteSpace E] in
theorem cutoffOuter_resolvent (U : E →L[ℂ] E) (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hb : ∀ z ∈ spectrum ℂ U, ‖z‖ ≤ D) :
    (cutoffOuter D η : ℂ) ∈ resolventSet ℂ U ∧
      (-cutoffOuter D η : ℂ) ∈ resolventSet ℂ U := by
  have hg := (cutoffOuter_gt D η hD hη).1
  have hp : 0 ≤ cutoffOuter D η := le_trans hD (le_of_lt hg)
  constructor
  · by_contra hz
    have hn := hb _ hz
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] at hn
    linarith
  · by_contra hz
    have hn := hb _ hz
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] at hn
    linarith

noncomputable def cutoffContourOperator (U : E →L[ℂ] E) (D η : ℝ) : E →L[ℂ] E :=
  rectangleResolvent U η (cutoffOuter D η) 1 +
    rectangleResolvent U (-cutoffOuter D η) (-η) 1

theorem cutoffContourOperator_intertwine (U : E →L[ℂ] E) (T : F →L[ℂ] F)
    (R : E →L[ℂ] F) (hc : ∀ x, R (U x) = T (R x)) (D η : ℝ)
    (hD : 0 ≤ D) (hη : 0 < η)
    (hU : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ ≤ D)
    (hT : ∀ z ∈ spectrum ℂ T, z.im = 0 ∧ ‖z‖ ≤ D)
    (hp : (η : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T)
    (hn : (-η : ℂ) ∈ resolventSet ℂ U ∩ resolventSet ℂ T) :
    R.comp (cutoffContourOperator U D η) = (cutoffContourOperator T D η).comp R := by
  obtain ⟨uPos,uNeg⟩ := cutoffOuter_resolvent U D η hD hη (fun z hz ↦ (hU z hz).2)
  obtain ⟨tPos,tNeg⟩ := cutoffOuter_resolvent T D η hD hη (fun z hz ↦ (hT z hz).2)
  have HPos := rectangleResolvent_intertwine U T R hc (fun z hz ↦ (hU z hz).1)
    (fun z hz ↦ (hT z hz).1) η (cutoffOuter D η) 1 (by norm_num) hp ⟨uPos,tPos⟩
  have HNeg := rectangleResolvent_intertwine U T R hc (fun z hz ↦ (hU z hz).1)
    (fun z hz ↦ (hT z hz).1) (-cutoffOuter D η) (-η) 1 (by norm_num)
    (by simpa using And.intro uNeg tNeg) (by simpa using hn)
  apply ContinuousLinearMap.ext
  intro x
  have hPos := congrArg (fun A : E →L[ℂ] F ↦ A x) HPos
  have hNeg := congrArg (fun A : E →L[ℂ] F ↦ A x) HNeg
  change R (_ + _) = _ + _
  rw [map_add]
  exact congrArg₂ (· + ·) hPos hNeg

theorem cutoffContour_spectral_selection (S : Set ℂ) (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hr : ∀ z ∈ S, z.im = 0) (hb : ∀ z ∈ S, ‖z‖ ≤ D) :
    cutoffRectangles η (cutoffOuter D η) 1 ∩ S = {z ∈ S | η < ‖z‖} :=
  cutoffRectangles_spectral_selection S η _ 1 hr
    (fun z hz ↦ (hb z hz).trans_lt (cutoffOuter_gt D η hD hη).1) (by norm_num)
theorem zero_not_mem_closure_cutoffRectangles (η B h : ℝ) (hη : 0 < η) :
    (0 : ℂ) ∉ closure (cutoffRectangles η B h) := by
  have hs : cutoffRectangles η B h ⊆ {z : ℂ | η ≤ |z.re|} := by
    intro z hz
    rcases hz.1 with hp | hn
    · exact (le_of_lt hp.1).trans (le_abs_self _)
    · exact (by linarith [hn.2] : η ≤ -z.re).trans (neg_le_abs _)
  have hc : IsClosed {z : ℂ | η ≤ |z.re|} :=
    isClosed_le continuous_const Complex.continuous_re.abs
  intro hz
  have hh := closure_minimal hs hc hz
  simp only [mem_setOf_eq, Complex.zero_re, abs_zero] at hh
  exact (not_le_of_gt hη) hh
end PaperN.PartII
