import PaperN.PartI.ValovInput
import PaperN.PartI.Definitions
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.GDelta.MetrizableSpace

namespace PaperN.PartI
open MeasureTheory Set
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Full support on a fixed carrier, not on the varying measured GH quotient. -/
def FixedFullSupportGDeltaStatement : Prop :=
  IsGδ {μ : ProbabilityMeasure X | (μ : Measure X).support = univ}

/-- Invariance under all surjective self-isometries of this fixed carrier. -/
def FixedInvariantClosedStatement : Prop :=
  IsClosed {μ : ProbabilityMeasure X | ∀ g : X ≃ᵢ X,
    Measure.map g (μ : Measure X) = (μ : Measure X)}

def FixedInvariantFullSupportGDeltaStatement : Prop :=
  IsGδ {μ : ProbabilityMeasure X | (μ : Measure X).support = univ ∧
    ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)}

/-- Averaging a law concentrated on invariant full-support probabilities preserves both properties. -/
def FixedLawAverageStatement : Prop :=
  ∀ η : ProbabilityMeasure (ProbabilityMeasure X),
    (η : Measure (ProbabilityMeasure X))
      {μ | (μ : Measure X).support = univ ∧
        ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)} = 1 →
    (barycenter η : Measure X).support = univ ∧
      ∀ g : X ≃ᵢ X, Measure.map g (barycenter η : Measure X) = (barycenter η : Measure X)

end PaperN.PartI
