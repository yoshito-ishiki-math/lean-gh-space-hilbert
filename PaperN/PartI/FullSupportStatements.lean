import PaperN.PartI.MinimumBallMass
import Mathlib.Topology.GDelta.Basic

namespace PaperN.PartI
open MeasureTheory Set TopologicalSpace
universe u
namespace MeasuredGHSpace

/-- Full support on the entire carrier, descended through measured isometry. -/
def fullSupport (q : MeasuredGHSpace.{u}) : Prop :=
  Quotient.liftOn q (fun X ↦ X.measure.support = univ) (by
    intro X Y h
    apply propext
    change (X.probability : Measure X).support = univ ↔
      (Y.probability : Measure Y).support = univ
    rw [support_eq_univ_iff_minimumBallMass_pos, support_eq_univ_iff_minimumBallMass_pos]
    obtain ⟨e, he⟩ := h
    exact forall_congr' fun n ↦ by
      rw [minimumBallMass_isometryEquiv X.probability Y.probability e he])
end MeasuredGHSpace

/-- The varying-space `lem:full-support-gdelta`, in the actual GHP metric. -/
def FullSupportGDeltaStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  IsGδ {q : MeasuredGHSpace.{u} | q.fullSupport}
end PaperN.PartI
