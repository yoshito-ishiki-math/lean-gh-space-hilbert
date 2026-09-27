import PaperN.PartII.LpDistance
import PaperN.PartII.SelectedDistanceOperator

namespace PaperN.PartII
open MeasureTheory Metric Set PaperN.PartI
universe u
local instance selectedLpMeasurableSpace (X : Type u) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance selectedLpBorelSpace (X : Type u) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Full Lp estimate for precisely the probability selected in Part I. -/
theorem selectedLpDistance (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    let μ := (universalProbability hm hs X).toMeasure
    ∀ r : ℝ, 0 < r → (0 < ⨅ z : X, μ.real (ball z r)) ∧
      ∀ (p : ℝ) (hp : 2 ≤ p),
      letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
      ∀ x y : X,
      0 ≤ dist x y - ‖distanceDifferenceLp μ (ENNReal.ofReal p) x y‖ ∧
      dist x y - ‖distanceDifferenceLp μ (ENNReal.ofReal p) x y‖ ≤
        diam (univ : Set X) * (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p)) + 2*r := by
  letI := openPos_of_support_eq_univ _ (universalProbability_fullSupport hm hs X)
  exact lpDistance_spec X _
end PaperN.PartII
