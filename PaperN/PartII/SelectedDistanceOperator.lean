import PaperN.PartII.DistanceOperator
import PaperN.PartI.UniverseAssignment

namespace PaperN.PartII
open MeasureTheory PaperN.PartI
universe u
local instance (X : Type u) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance (X : Type u) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Apply the cited part to precisely the probability selected in Part I. -/
theorem selectedDistanceOperator_spectral (h : DistanceKernelSpectralInput.{u})
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    IsCompactOperator (distanceOperator (universalProbability hm hs X).toMeasure) ∧
    IsSelfAdjoint (distanceOperator (universalProbability hm hs X).toMeasure) :=
  h X _

/-- Full support is supplied by Part I, not required as another external input. -/
theorem selectedDistanceOperator_continuousRepresentative
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : Lp ℝ 2 (universalProbability hm hs X).toMeasure) (a : ℝ) (ha : a ≠ 0)
    (hf : distanceOperator (universalProbability hm hs X).toMeasure f = a • f) :
    ∃! g : C(X, ℝ), continuousToL2 (universalProbability hm hs X).toMeasure g = f := by
  letI := openPos_of_support_eq_univ _ (universalProbability_fullSupport hm hs X)
  exact eigenfunction_continuousRepresentative _ f a ha hf
end PaperN.PartII
