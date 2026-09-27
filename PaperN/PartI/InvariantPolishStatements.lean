import PaperN.PartI.GHPExternalStatements
import Mathlib.Topology.MetricSpace.Polish

namespace PaperN.PartI
open TopologicalSpace
universe u
/-- The subspace topology is Polish, without claiming completeness of the restricted GHP metric. -/
def InvariantMeasuredPolishStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  PolishSpace InvariantMeasuredGHSpace.{u}
end PaperN.PartI
