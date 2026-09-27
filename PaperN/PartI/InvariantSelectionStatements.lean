import PaperN.PartI.GHPExternal
import PaperN.PartI.ValovStatements
import PaperN.PartI.InvariantPolish

namespace PaperN.PartI
open MeasureTheory GromovHausdorff

/-- The actual forgetful map, with the topology induced by the cited GHP metric. -/
noncomputable def invariantProjectionMap (hm : GHPMetricInput.{0}) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    C(InvariantMeasuredGHSpace.{0}, GHSpace) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  exact ⟨fun x ↦ x.val.forget, (invariantProjectionContinuousSurjective_spec hm).1⟩

/-- The existing Valov input specialized to the actual projection; no extra conclusion is assumed. -/
def InvariantValovInput (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) : Prop :=
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  letI : PolishSpace InvariantMeasuredGHSpace.{0} := invariantMeasuredPolish_spec hm hp hc
  ValovProbabilityInput (invariantProjectionMap hm)

/-- Continuous laws on the actual invariant GHP fibers, before transport to a fixed carrier. -/
def InvariantFiberLawSelectionStatement (hm : GHPMetricInput.{0}) : Prop :=
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  FiberLawSelectionStatement (invariantProjectionMap hm)
end PaperN.PartI
