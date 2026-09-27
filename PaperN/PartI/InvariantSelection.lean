import PaperN.PartI.InvariantSelectionStatements
import PaperN.PartI.InvariantPolish
import PaperN.PartI.OpenProjection
import PaperN.PartI.Valov

namespace PaperN.PartI
open MeasureTheory GromovHausdorff

/-- Apply Valov to the now-proved Polish space and continuous open surjection.
The resulting laws are on measured isometry classes, not yet probabilities on the carriers. -/
theorem invariantFiberLawSelection_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    InvariantFiberLawSelectionStatement hm := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  letI : PolishSpace InvariantMeasuredGHSpace.{0} := invariantMeasuredPolish_spec hm hp hc
  obtain ⟨_, ho, hs⟩ := openInvariantProjection_spec hm hg ha
  exact fiberLawSelection_spec (invariantProjectionMap hm) hv ho hs
end PaperN.PartI
