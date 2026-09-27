import PaperN.PartII.UniformCoefficientConvergence
import PaperN.PartII.LpNormTransport

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- Uniform distance control gives convergence of suprema on varying nonempty types. -/
theorem varying_sup_dist_tendsto {E : Type*} [MetricSpace E]
    (A : ℕ → Type*) [∀ n, Nonempty (A n)] (f g : ∀ n, A n → E)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ∀ a, dist (f n a) (g n a) < ε) :
    Tendsto (fun n ↦ ⨆ a, dist (f n a) (g n a)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  have hb : BddAbove (Set.range (fun a ↦ dist (f n a) (g n a))) :=
    ⟨ε / 2, by rintro _ ⟨a, rfl⟩; exact (hn a).le⟩
  have hlo : 0 ≤ ⨆ a, dist (f n a) (g n a) :=
    dist_nonneg.trans (le_ciSup hb (Classical.choice inferInstance))
  have hhi : (⨆ a, dist (f n a) (g n a)) ≤ ε / 2 := ciSup_le fun a ↦ (hn a).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using
    hhi.trans_lt (half_lt_self hε)

/-- Nearby-pair uniformity yields the exact supremum convergence used for correspondences. -/
theorem nearby_pair_sup_tendsto {Z E : Type*} [MetricSpace Z] [CompactSpace Z] [MetricSpace E]
    (A : ℕ → Type*) [∀ n, Nonempty (A n)] (x y : ∀ n, A n → Z)
    (f g : ∀ n, A n → E)
    (hd : Tendsto (fun n ↦ ⨆ a, dist (x n a) (y n a)) atTop (𝓝 0))
    (h : ∀ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) →
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ a, dist (x n a) (y n a) ≤ r n →
        dist (f n a) (g n a) < ε) :
    Tendsto (fun n ↦ ⨆ a, dist (f n a) (g n a)) atTop (𝓝 0) := by
  apply varying_sup_dist_tendsto A f g
  intro ε hε
  filter_upwards [h _ hd ε hε] with n hn
  intro a
  apply hn a
  have hb : BddAbove (Set.range (fun a ↦ dist (x n a) (y n a))) := by
    refine ⟨Metric.diam (Set.univ : Set Z), ?_⟩
    rintro _ ⟨b, rfl⟩
    exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _)
  exact le_ciSup hb a

variable {Z ι : Type*} [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι] [Nonempty ι]

theorem coordinateLpNorm_unitNormError_tendsto
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i))) :
    Tendsto (fun n ↦ unitNormError (coordinateLpNorm (μs n : Measure Z) p (vs n))
      (coordinateLpNorm (μ : Measure Z) p v)) atTop (𝓝 0) := by
  let K := Metric.sphere (0 : EuclideanSpace ℝ ι) 1
  have hne : K.Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  letI : Nonempty K := hne.to_subtype
  have hu := coordinateLpNorm_uniform_on_compact μs μ hμ p hp vs v hv K (isCompact_sphere _ _)
  simpa only [unitNormError, Real.dist_eq] using PartI.tendsto_sup_dist_of_uniform hu

end PaperN.PartII
