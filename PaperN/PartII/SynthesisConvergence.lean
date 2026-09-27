import PaperN.PartII.CoordinateLpNorm
import PaperN.PartII.BasisTransform

namespace PaperN.PartII
open Filter Topology
variable {X ι : Type*} [TopologicalSpace X] [CompactSpace X] [Fintype ι]

theorem coordinateSynthesis_error_le (v w : ι → C(X, ℝ)) (a : EuclideanSpace ℝ ι) :
    ‖coordinateSynthesis v a - coordinateSynthesis w a‖ ≤
      (∑ i, ‖v i - w i‖) * ‖a‖ := by
  classical
  change ‖(∑ i, a i • v i) - ∑ i, a i • w i‖ ≤ _
  rw [← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  calc
    _ ≤ ∑ i, ‖a i • (v i - w i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖v i - w i‖ * ‖a‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le a i) (norm_nonneg _)
    _ = _ := (Finset.sum_mul ..).symm

theorem coordinateSynthesis_uniform_on_ball
    (vs : ℕ → ι → C(X, ℝ)) (v : ι → C(X, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) (R : ℝ) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ a : EuclideanSpace ℝ ι, ‖a‖ ≤ R →
      ‖coordinateSynthesis (vs n) a - coordinateSynthesis v a‖ < ε := by
  classical
  have ht : Tendsto (fun n ↦ (∑ i, ‖vs n i - v i‖) * R) atTop (𝓝 0) := by
    have hs : Tendsto (fun n ↦ ∑ i, ‖vs n i - v i‖) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ ((hv i).sub (tendsto_const_nhds (x := v i))).norm)
    simpa using hs.mul_const R
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro a ha
  exact (coordinateSynthesis_error_le (vs n) v a).trans_lt
    ((mul_le_mul_of_nonneg_left ha (Finset.sum_nonneg fun i _ ↦ norm_nonneg _)).trans_lt hn)

end PaperN.PartII
