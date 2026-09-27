import PaperN.PartI.CompactIsometryEmbeddings
import PaperN.PartI.ProkhorovMapApproximation

namespace PaperN.PartI
open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction

/-- Uniform distance bounds the Hausdorff distance of the full images. -/
theorem hausdorffDist_range_le_uniform {X Z : Type*} [TopologicalSpace X]
    [MetricSpace Z] (f g : X →ᵇ Z) :
    hausdorffDist (range f) (range g) ≤ dist f g := by
  apply hausdorffDist_le_of_mem_dist dist_nonneg
  · rintro _ ⟨x, rfl⟩
    exact ⟨g x, mem_range_self x, BoundedContinuousFunction.dist_coe_le_dist x⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f x, mem_range_self x, by
      rw [dist_comm]
      exact BoundedContinuousFunction.dist_coe_le_dist x⟩

/-- Uniform convergence gives convergence of full images in Hausdorff distance. -/
theorem hausdorffDist_range_tendsto_of_uniform {X Z : Type*} [TopologicalSpace X]
    [MetricSpace Z] (f : ℕ → X →ᵇ Z) (g : X →ᵇ Z)
    (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n ↦ hausdorffDist (range (f n)) (range g)) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ hausdorffDist_nonneg)
    (fun n ↦ hausdorffDist_range_le_uniform (f n) g)
    (tendsto_iff_dist_tendsto_zero.mp h)

/-- Uniform convergence preserves the pushforward limit of a fixed probability. -/
theorem prokhorov_map_tendsto_of_uniform {X Z : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [MetricSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (f : ℕ → X →ᵇ Z) (g : X →ᵇ Z) (h : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n ↦ levyProkhorovDist (Measure.map (f n) μ) (Measure.map g μ))
      atTop (𝓝 0) := by
  exact levyProkhorovDist_map_tendsto_of_dist_le μ (fun n ↦ f n) g
    (fun n ↦ (f n).continuous.measurable) g.continuous.measurable
    (fun n ↦ dist (f n) g) (fun _ ↦ dist_nonneg)
    (tendsto_iff_dist_tendsto_zero.mp h)
    (fun _ x ↦ BoundedContinuousFunction.dist_coe_le_dist x)
end PaperN.PartI
