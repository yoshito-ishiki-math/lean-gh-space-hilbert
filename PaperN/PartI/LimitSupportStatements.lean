import PaperN.PartI.ProbabilityTopology
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace PaperN.PartI
open MeasureTheory Metric Filter
open scoped Topology

/-- `lem:limit-support`: weak limits retain full mass on the Hausdorff limit of compact sets. -/
def LimitSupportStatement : Prop :=
  ∀ {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (Ks : ℕ → Set Z) (K : Set Z),
    (∀ n, IsCompact (Ks n)) → (∀ n, (Ks n).Nonempty) →
    IsCompact K → K.Nonempty →
    Tendsto (fun n ↦ hausdorffDist (Ks n) K) atTop (𝓝 0) →
    ∀ (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z),
    Tendsto μs atTop (𝓝 μ) → (∀ n, (μs n : Measure Z) (Ks n) = 1) →
    (μ : Measure Z) K = 1
end PaperN.PartI
