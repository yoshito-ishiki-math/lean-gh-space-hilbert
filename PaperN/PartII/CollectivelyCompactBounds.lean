import PaperN.PartII.SelectedKernelConvergence
import PaperN.PartII.CircleIntertwining

namespace PaperN.PartII
open Set Filter
open scoped Topology

/-- Collective compactness of differences supplies a uniform operator-norm bound. -/
theorem collectivelyCompact_differences_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (h : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖Us n‖ ≤ C := by
  obtain ⟨K, hK, hk⟩ := h
  obtain ⟨R, hr, hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R + ‖U‖, add_nonneg hr.le (norm_nonneg _), ?_⟩
  intro n
  have hn : ‖Us n - U‖ ≤ R := ContinuousLinearMap.opNorm_le_of_unit_norm hr.le
    (fun x hx ↦ hb _ (hk n x hx.le))
  calc
    ‖Us n‖ = ‖(Us n - U) + U‖ := by rw [sub_add_cancel]
    _ ≤ ‖Us n - U‖ + ‖U‖ := norm_add_le _ _
    _ ≤ R + ‖U‖ := add_le_add hn le_rfl

/-- Strong convergence with uniform norm bounds also applies to moving convergent vectors. -/
theorem strong_tendsto_apply_of_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (C : ℝ) (hb : ∀ n, ‖Us n‖ ≤ C)
    (xs : ℕ → E) (x : E) (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n ↦ Us n (xs n)) atTop (𝓝 (U x)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlim := ((tendsto_iff_dist_tendsto_zero.mp hx).const_mul C).add
    (tendsto_iff_dist_tendsto_zero.mp (hs x))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero (fun n ↦ dist_nonneg) _ hlim
  intro n
  calc
    dist (Us n (xs n)) (U x) ≤ dist (Us n (xs n)) (Us n x) + dist (Us n x) (U x) := dist_triangle _ _ _
    _ ≤ C * dist (xs n) x + dist (Us n x) (U x) := by
      exact add_le_add (by
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact ((Us n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))) le_rfl
end PaperN.PartII
