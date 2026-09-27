import PaperN.PartII.DistanceKernel

namespace PaperN.PartII
open MeasureTheory Metric Set
open scoped ENNReal
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The Lp class of the difference of two continuous distance profiles. -/
noncomputable def distanceDifferenceLp (x y : X) : Lp ℝ p μ :=
  ContinuousMap.toLp p μ ℝ (distanceProfile x - distanceProfile y)
end PaperN.PartII
