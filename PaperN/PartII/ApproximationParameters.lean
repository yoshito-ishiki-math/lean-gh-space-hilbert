import PaperN.PartII.BestApproximationError
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

namespace PaperN.PartII
open Filter Topology MeasureTheory Metric Set

theorem exists_large_exponent (m D ε : ℝ) (hm : 0 < m) (hε : 0 < ε) :
    ∃ q : ℝ, 2 ≤ q ∧ D * (1 - m ^ (1 / q)) < ε := by
  have ht : Tendsto (fun n : ℕ ↦ m ^ (1 / (n : ℝ))) atTop (𝓝 1) := by
    simpa [Function.comp_def] using (Real.continuousAt_const_rpow (ne_of_gt hm) (b := 0)).tendsto.comp
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have he : Tendsto (fun n : ℕ ↦ D * (1 - m ^ (1 / (n : ℝ)))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := D)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub ht)
  obtain ⟨n, hn, hn2⟩ := ((he.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop 2)).exists
  exact ⟨n, by exact_mod_cast hn2, hn⟩

theorem exists_local_error_parameters {X : Type*} [MetricSpace X] [CompactSpace X]
    [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ r q ε : ℝ, 0 < r ∧ 2 ≤ q ∧ 0 < ε ∧
      2 * ε + diam (univ : Set X) *
        (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / q)) + 2*r < τ := by
  let r := τ / 8
  have hr : 0 < r := by dsimp [r]; positivity
  have hm := uniform_ball_mass_pos μ r hr
  obtain ⟨q, hq, he⟩ := exists_large_exponent _ (diam (univ : Set X)) (τ / 4) hm (by positivity)
  refine ⟨r, q, τ/8, hr, hq, by positivity, ?_⟩
  dsimp [r] at *
  linarith

end PaperN.PartII
