import PaperN.PartII.ProjectionRankStability
import PaperN.PartII.ContourDifferenceCompact
import PaperN.PartII.CutoffContourConvergence

namespace PaperN.PartII
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Eventual collective compactness suffices for finite projection rank stability. -/
theorem collectivelyCompactTail_projection_rank_stable
    (Ps : ℕ → E →L[ℂ] E) (P : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Ps n x) atTop (𝓝 (P x)))
    (hk : CollectivelyCompactTail (fun n ↦ Ps n-P))
    (hP : ∀ x, P (P x) = P x)
    (hPs : ∀ᶠ n in atTop, ∀ x, Ps n (Ps n x) = Ps n x)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)] :
    ∀ᶠ n in atTop, FiniteDimensional ℂ (LinearMap.range (Ps n).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (Ps n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
  obtain ⟨N,K,hK,hm⟩ := hk
  have hh := collectivelyCompact_projection_rank_stable (fun n ↦ Ps (n+N)) P
    (fun x ↦ (hs x).comp (tendsto_add_atTop_nat N))
    ⟨K,hK,fun n x hx ↦ hm (n+N) (by omega) x hx⟩ hP
    ((tendsto_add_atTop_nat N).eventually hPs)
  obtain ⟨M,hM⟩ := eventually_atTop.mp hh
  apply eventually_atTop.mpr
  refine ⟨M+N,fun n hn ↦ ?_⟩
  have hnN : N ≤ n := by omega
  have ht := hM (n-N) (by omega)
  rw [Nat.sub_add_cancel hnN] at ht
  exact ht

/-- The cutoff contour has stable finite rank whenever its projection identities hold. -/
theorem collectivelyCompact_cutoffContour_rank_stable
    [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (D η : ℝ) (hD : 0 ≤ D) (hη : 0 < η)
    (hr : ∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ ≤ D)
    (hp : (η : ℂ) ∈ resolventSet ℂ U) (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U)
    (hP : ∀ x, cutoffContourOperator U D η (cutoffContourOperator U D η x) = cutoffContourOperator U D η x)
    (hPs : ∀ᶠ n in atTop, ∀ x, cutoffContourOperator (Us n) D η
      (cutoffContourOperator (Us n) D η x) = cutoffContourOperator (Us n) D η x)
    [FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator U D η).toLinearMap)] :
    ∀ᶠ n in atTop,
      FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (Us n) D η).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (cutoffContourOperator (Us n) D η).toLinearMap) =
        Module.finrank ℂ (LinearMap.range (cutoffContourOperator U D η).toLinearMap) := by
  exact collectivelyCompactTail_projection_rank_stable
    (fun n ↦ cutoffContourOperator (Us n) D η) (cutoffContourOperator U D η)
    (collectivelyCompact_cutoffContourOperator_tendsto Us U hs hk D η hD hη hr hp hn)
    (collectivelyCompact_cutoffContour_difference_tail Us U hs hk D η hD hη hr hp hn) hP hPs
end PaperN.PartII
