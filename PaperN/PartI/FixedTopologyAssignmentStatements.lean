import PaperN.PartI.CompatibleMetric
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace PaperN.PartI
open MeasureTheory Set Filter Metric
open scoped Topology
universe u
local instance statementMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance statementBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- The full fixed-topology statement of M1, M2, M3, for every universe u.
No seed probability, chosen representative, or external input occurs in the conclusion. -/
def FixedTopologyAssignmentStatement : Prop :=
  ∃ μ : ∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X],
      CompatibleMetric X → ProbabilityMeasure X,
    (∀ (X : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
      (d : CompatibleMetric X), (μ X d).toMeasure.support = univ) ∧
    (∀ (X Y : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
      [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
      (d : CompatibleMetric X) (e : CompatibleMetric Y),
      letI := d.toMetric
      letI := e.toMetric
      ∀ f : X ≃ᵢ Y, (μ X d).map f.continuous.measurable.aemeasurable = μ Y e) ∧
    (∀ (Xs : ℕ → Type u) (X Z : Type u)
      [∀ n, TopologicalSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
      [TopologicalSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Z] [CompactSpace Z]
      (ds : ∀ n, CompatibleMetric (Xs n)) (d : CompatibleMetric X),
      letI := fun n ↦ (ds n).toMetric
      letI := d.toMetric
      ∀ (es : ∀ n, Xs n → Z) (e : X → Z) (hes : ∀ n, Isometry (es n)) (he : Isometry e),
      Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0) →
      Tendsto (fun n ↦ (μ (Xs n) (ds n)).map (hes n).continuous.measurable.aemeasurable)
        atTop (𝓝 ((μ X d).map he.continuous.measurable.aemeasurable)))
end PaperN.PartI
