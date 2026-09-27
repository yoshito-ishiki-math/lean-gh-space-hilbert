import PaperN.PartII.LpDistanceDefinitions
import Mathlib.MeasureTheory.Measure.OpenPos

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

/-- Full lem:lp-distance, with every finite real exponent p≥2. -/
def LpDistanceStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
    ∀ r : ℝ, 0 < r → (0 < ⨅ z : X, μ.real (ball z r)) ∧
      ∀ (p : ℝ) (hp : 2 ≤ p),
      letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
      ∀ x y : X,
      0 ≤ dist x y - ‖distanceDifferenceLp μ (ENNReal.ofReal p) x y‖ ∧
      dist x y - ‖distanceDifferenceLp μ (ENNReal.ofReal p) x y‖ ≤
        diam (univ : Set X) * (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p)) + 2*r
end PaperN.PartII
