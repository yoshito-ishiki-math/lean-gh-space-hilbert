import PaperN.PartI.IsometryDefect
import PaperN.PartI.FullSupportStatements
import Mathlib.Topology.GDelta.Basic

namespace PaperN.PartI
open TopologicalSpace
universe u
/-- `lem:invariant-measures-gdelta` in the varying, whole-carrier GHP quotient. -/
def InvariantGDeltaStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  IsGδ {q : MeasuredGHSpace.{u} | q.invariant}
/-- The original invariant-full-support subset is a Gδ; Polishness is a separate step. -/
def InvariantFullSupportGDeltaStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  IsGδ {q : MeasuredGHSpace.{u} | q.invariantFullSupport}
end PaperN.PartI
