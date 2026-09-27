import PaperN.PartII.ResolventNeighborhoodBound

namespace PaperN.PartII
open Set Filter Metric
open scoped Topology

/-- Uniform eventual resolvent bounds on compact subsets of the limit resolvent. -/
theorem collectivelyCompact_eventually_compact_resolvent_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ z ∈ A,
      z ∈ resolventSet ℂ (Us n) ∧ ‖resolvent (Us n) z‖ ≤ B := by
  classical
  have hh := fun z : A ↦ collectivelyCompact_eventually_resolvent_neighborhood
    Us U hs hk z (hr z.property)
  choose r B hpos hnonneg hev using hh
  obtain ⟨s, hcover⟩ := hA.elim_finite_subcover
    (fun z : A ↦ ball (z : ℂ) (r z)) (fun _ ↦ isOpen_ball) (by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (hpos ⟨z, hz⟩)⟩)
  refine ⟨∑ z ∈ s, B z, Finset.sum_nonneg (fun z _ ↦ hnonneg z), ?_⟩
  have hall : ∀ᶠ n in atTop, ∀ z ∈ s, ∀ w ∈ ball (z : ℂ) (r z),
      w ∈ resolventSet ℂ (Us n) ∧ ‖resolvent (Us n) w‖ ≤ B z :=
    s.finite_toSet.eventually_all.mpr (fun z _ ↦ hev z)
  filter_upwards [hall] with n hn
  intro w hw
  obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp (hcover hw)
  obtain ⟨hres, hbound⟩ := hn z hz w hwz
  exact ⟨hres, hbound.trans (Finset.single_le_sum (fun z _ ↦ hnonneg z) hz)⟩
end PaperN.PartII
