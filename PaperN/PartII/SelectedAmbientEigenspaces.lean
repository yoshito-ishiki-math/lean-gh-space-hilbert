import PaperN.PartII.AmbientEigenspaces
import PaperN.PartII.SelectedDistanceOperator

namespace PaperN.PartII
open MeasureTheory PaperN.PartI
universe u v
local instance selectedAmbientMeasurableSpace (X : Type u) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance selectedAmbientBorelSpace (X : Type u) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

theorem selectedAmbientEigenspaces (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    {Z : Type v} [MetricSpace Z] [CompactSpace Z]
    (e : C(X, Z)) (he : Isometry e) :
    AmbientEigenspacesStatement e (universalProbability hm hs X).toMeasure :=
  ambientEigenspaces_spec e _ he
end PaperN.PartII
