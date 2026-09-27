import PaperN.PartI.GHPStatements
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-! The analytic conversion for common embeddings. Existence of a common compact
ambient space for a GHP-convergent sequence is not assumed or proved here. -/
namespace PaperN.PartI
open MeasureTheory Filter TopologicalSpace
open scoped Topology

/-- On a separable metric space, Prokhorov convergence is weak convergence. -/
theorem weak_tendsto_iff_prokhorov {Z : Type*} [MetricSpace Z] [SeparableSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {ι : Type*} {l : Filter ι}
    (μ : ι → ProbabilityMeasure Z) (ν : ProbabilityMeasure Z) :
    Tendsto μ l (𝓝 ν) ↔
      Tendsto (fun i ↦ levyProkhorovDist (μ i : Measure Z) (ν : Measure Z)) l (𝓝 0) := by
  constructor
  · intro h
    have ht := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.continuousAt.tendsto.comp h
    exact tendsto_iff_dist_tendsto_zero.1 ht
  · intro h
    have ht : Tendsto (fun i ↦ LevyProkhorov.ofMeasure (μ i)) l
        (𝓝 (LevyProkhorov.ofMeasure ν)) := tendsto_iff_dist_tendsto_zero.2 h
    exact LevyProkhorov.continuous_toMeasure_probabilityMeasure.continuousAt.tendsto.comp ht
theorem weakProkhorov_spec {Z : Type*} [MetricSpace Z] [SeparableSpace Z]
    [MeasurableSpace Z] [BorelSpace Z] {ι : Type*} (l : Filter ι)
    (μ : ι → ProbabilityMeasure Z) (ν : ProbabilityMeasure Z) :
    WeakProkhorovStatement l μ ν := weak_tendsto_iff_prokhorov μ ν
end PaperN.PartI
