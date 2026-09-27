import PaperN.PartII.SegmentResolventConvergence
import PaperN.PartII.CutoffContour

namespace PaperN.PartII
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
variable (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
variable (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
include hs hk

/-- Strong convergence of the four-edge resolvent integral. -/
theorem collectivelyCompact_quadrilateralResolvent_tendsto
    (a b c d : ℂ)
    (hab : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U)
    (hbc : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter b c t ∈ resolventSet ℂ U)
    (hcd : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter c d t ∈ resolventSet ℂ U)
    (hda : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter d a t ∈ resolventSet ℂ U)
    (x : E) :
    Tendsto (fun n ↦ quadrilateralResolvent (Us n) a b c d x) atTop
      (𝓝 (quadrilateralResolvent U a b c d x)) := by
  exact (((collectivelyCompact_segmentResolvent_tendsto Us U hs hk a b hab x).add
    (collectivelyCompact_segmentResolvent_tendsto Us U hs hk b c hbc x)).add
    (collectivelyCompact_segmentResolvent_tendsto Us U hs hk c d hcd x)).add
    (collectivelyCompact_segmentResolvent_tendsto Us U hs hk d a hda x) |>.const_smul _

/-- Strong convergence along a rectangle whose boundary avoids the limit spectrum. -/
theorem collectivelyCompact_rectangleResolvent_tendsto
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U)
    (x : E) :
    Tendsto (fun n ↦ rectangleResolvent (Us n) l r h x) atTop
      (𝓝 (rectangleResolvent U l r h x)) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := rectangle_edges_resolvent U hr l r h hh hl hr'
  exact collectivelyCompact_quadrilateralResolvent_tendsto Us U hs hk _ _ _ _ h₁ h₂ h₃ h₄ x

/-- The strong-convergence component of the main cutoff projection input. -/
theorem collectivelyCompact_cutoffContourOperator_tendsto
    (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ ≤ D)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U)
    (x : E) :
    Tendsto (fun n ↦ cutoffContourOperator (Us n) D η x) atTop
      (𝓝 (cutoffContourOperator U D η x)) := by
  obtain ⟨ho,hno⟩ := cutoffOuter_resolvent U D η hD hη (fun z hz ↦ (hr z hz).2)
  exact (collectivelyCompact_rectangleResolvent_tendsto Us U hs hk
    (fun z hz ↦ (hr z hz).1) η (cutoffOuter D η) 1 (by norm_num) hp ho x).add
    (collectivelyCompact_rectangleResolvent_tendsto Us U hs hk
      (fun z hz ↦ (hr z hz).1) (-cutoffOuter D η) (-η) 1 (by norm_num)
      (by simpa using hno) hn x)
end PaperN.PartII
