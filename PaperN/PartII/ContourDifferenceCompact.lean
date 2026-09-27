import PaperN.PartII.SegmentDifferenceCompact
import PaperN.PartII.CutoffContour

namespace PaperN.PartII
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Unit-ball images of all sufficiently late terms share a compact container. -/
def CollectivelyCompactTail (Ts : ℕ → E →L[ℂ] E) : Prop :=
  ∃ N : ℕ, ∃ K : Set E, IsCompact K ∧ ∀ n, N ≤ n → ∀ x, ‖x‖ ≤ 1 → Ts n x ∈ K

theorem CollectivelyCompactTail.add {Ts Rs : ℕ → E →L[ℂ] E}
    (ht : CollectivelyCompactTail Ts) (hr : CollectivelyCompactTail Rs) :
    CollectivelyCompactTail (fun n ↦ Ts n + Rs n) := by
  obtain ⟨N,K,hK,hm⟩ := ht
  obtain ⟨M,L,hL,hl⟩ := hr
  refine ⟨max N M, (fun p : E × E ↦ p.1+p.2) '' (K ×ˢ L),
    (hK.prod hL).image (continuous_fst.add continuous_snd), ?_⟩
  intro n hn x hx
  exact ⟨(Ts n x,Rs n x), ⟨hm n (le_trans (le_max_left _ _) hn) x hx,
    hl n (le_trans (le_max_right _ _) hn) x hx⟩, rfl⟩

theorem CollectivelyCompactTail.smul {Ts : ℕ → E →L[ℂ] E}
    (ht : CollectivelyCompactTail Ts) (c : ℂ) :
    CollectivelyCompactTail (fun n ↦ c • Ts n) := by
  obtain ⟨N,K,hK,hm⟩ := ht
  refine ⟨N,(fun x : E ↦ c • x) '' K, hK.image (continuous_const.smul continuous_id), ?_⟩
  intro n hn x hx
  exact ⟨Ts n x,hm n hn x hx,rfl⟩

variable [CompleteSpace E]
variable (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
variable (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
variable (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
include hs hk

/-- Collective compactness of four-edge integral differences. -/
theorem collectivelyCompact_quadrilateral_difference_tail
    (a b c d : ℂ)
    (hab : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U)
    (hbc : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter b c t ∈ resolventSet ℂ U)
    (hcd : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter c d t ∈ resolventSet ℂ U)
    (hda : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter d a t ∈ resolventSet ℂ U) :
    CollectivelyCompactTail (fun n ↦ quadrilateralResolvent (Us n) a b c d -
      quadrilateralResolvent U a b c d) := by
  have H (p q : ℂ) (hpq : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t ∈ resolventSet ℂ U) :
      CollectivelyCompactTail (fun n ↦ segmentResolvent (Us n) p q - segmentResolvent U p q) :=
    collectivelyCompact_segmentResolvent_difference_tail Us U hs hk p q hpq
  have hh := (((H a b hab).add (H b c hbc)).add (H c d hcd)).add (H d a hda)
  have he := hh.smul (2 * Real.pi * Complex.I)⁻¹
  convert he using 1
  funext n
  unfold quadrilateralResolvent
  rw [← smul_sub]
  congr 1
  abel

/-- Collective compactness of rectangular contour differences. -/
theorem collectivelyCompact_rectangle_difference_tail
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0)
    (l r h : ℝ) (hh : 0 < h)
    (hl : (l : ℂ) ∈ resolventSet ℂ U) (hr' : (r : ℂ) ∈ resolventSet ℂ U) :
    CollectivelyCompactTail (fun n ↦ rectangleResolvent (Us n) l r h - rectangleResolvent U l r h) := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := rectangle_edges_resolvent U hr l r h hh hl hr'
  exact collectivelyCompact_quadrilateral_difference_tail Us U hs hk _ _ _ _ h₁ h₂ h₃ h₄

/-- Collective compactness of the actual positive-plus-negative cutoff contour differences. -/
theorem collectivelyCompact_cutoffContour_difference_tail
    (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ ≤ D)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U) :
    CollectivelyCompactTail (fun n ↦ cutoffContourOperator (Us n) D η - cutoffContourOperator U D η) := by
  obtain ⟨ho,hno⟩ := cutoffOuter_resolvent U D η hD hη (fun z hz ↦ (hr z hz).2)
  have hpos := collectivelyCompact_rectangle_difference_tail Us U hs hk
    (fun z hz ↦ (hr z hz).1) η (cutoffOuter D η) 1 (by norm_num) hp ho
  have hneg := collectivelyCompact_rectangle_difference_tail Us U hs hk
    (fun z hz ↦ (hr z hz).1) (-cutoffOuter D η) (-η) 1 (by norm_num) (by simpa using hno) hn
  convert hpos.add hneg using 1
  funext n
  unfold cutoffContourOperator
  abel
end PaperN.PartII
