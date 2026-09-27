import PaperN.PartI.GHPExternalStatements

namespace PaperN.PartI
/-- `prop:open-invariant-projection`, on mathlib's small GH model. -/
def OpenInvariantProjectionStatement (hm : GHPMetricInput.{0}) : Prop :=
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  Continuous (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget) ∧
    IsOpenMap (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget) ∧
    Function.Surjective (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget)
end PaperN.PartI
