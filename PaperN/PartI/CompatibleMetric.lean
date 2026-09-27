import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Isometry

namespace PaperN.PartI
universe u

/-- The manuscript's D(X): all metrics inducing the specified topology. -/
structure CompatibleMetric (X : Type u) [t : TopologicalSpace X] where
  metric : MetricSpace X
  compatible : t = metric.toUniformSpace.toTopologicalSpace

/-- Keep the original topology definitionally, and hence its original Borel sigma algebra. -/
abbrev CompatibleMetric.toMetric {X : Type u} [TopologicalSpace X] (d : CompatibleMetric X) :
    MetricSpace X := d.metric.replaceTopology d.compatible

/-- Every metric space gives an element of D(X) for its own topology. -/
def CompatibleMetric.ofMetric (X : Type u) [m : MetricSpace X] : CompatibleMetric X := ⟨m, rfl⟩
theorem CompatibleMetric.nonempty (X : Type u) [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] : Nonempty (CompatibleMetric X) := by
  letI := TopologicalSpace.metrizableSpaceMetric X
  exact ⟨CompatibleMetric.ofMetric X⟩
end PaperN.PartI
