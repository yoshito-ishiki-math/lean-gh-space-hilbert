import PaperN.PartI.GHPMetricInput
import PaperN.PartI.CommonRealization
import PaperN.PartI.MeasuredProjection

/-! Conditional target statements. Their external premises are never installed globally. -/
namespace PaperN.PartI
open TopologicalSpace
universe u

def GHPPolishStatement (h : GHPMetricInput.{u}) : Prop :=
  letI := h.metricSpace
  CompleteSpace MeasuredGHSpace.{u} ∧ SeparableSpace MeasuredGHSpace.{u} ∧
    SecondCountableTopology MeasuredGHSpace.{u}

def GHPForgetLipschitzStatement (h : GHPMetricInput.{u}) : Prop :=
  letI := h.metricSpace
  LipschitzWith 1 (MeasuredGHSpace.forget : MeasuredGHSpace.{u} → _)

noncomputable abbrev GHPMetricInput.invariantMetricSpace (h : GHPMetricInput.{u}) :
    MetricSpace InvariantMeasuredGHSpace.{u} := by
  letI := h.metricSpace
  exact inferInstanceAs (MetricSpace {x : MeasuredGHSpace.{u} // x.invariantFullSupport})

def InvariantProjectionContinuousSurjectiveStatement (h : GHPMetricInput.{0}) : Prop :=
  letI := h.metricSpace
  letI := h.invariantMetricSpace
  Continuous (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget) ∧
    Function.Surjective (fun x : InvariantMeasuredGHSpace.{0} ↦ x.val.forget)
end PaperN.PartI
