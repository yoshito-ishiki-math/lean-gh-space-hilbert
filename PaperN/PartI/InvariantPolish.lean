import PaperN.PartI.InvariantPolishStatements
import PaperN.PartI.InvariantGDelta
import PaperN.PartI.GDeltaPolish

namespace PaperN.PartI
open TopologicalSpace
universe u
/-- `prop:invariant-measured-polish`, using only the existing cited GHP inputs. -/
theorem invariantMeasuredPolish_spec (hm : GHPMetricInput.{u}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{u}) : InvariantMeasuredPolishStatement hm := by
  letI := hm.metricSpace
  letI := hp.complete
  letI := hp.separable
  letI := hm.invariantMetricSpace
  exact polishSpace_of_isGDelta (invariantFullSupportGDelta_spec hm hc)
end PaperN.PartI
