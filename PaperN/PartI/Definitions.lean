import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Isometry

/-! Definitions shared by the reviewable statements and their proofs. -/
namespace PaperN.PartI
open MeasureTheory

noncomputable def metricBump {X : Type*} [MetricSpace X]
    (x : X) (r : ℝ) (y : X) : ℝ := max (1 - dist x y / r) 0

noncomputable def normalizedMetricBump {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (x : X) (r : ℝ) (y : X) : ℝ :=
  metricBump x (r / 2) y / ∫ z, metricBump x (r / 2) z ∂μ

variable {X : Type*} [MeasurableSpace X]

/-- Average a law of probabilities by the measure monad's integral. -/
noncomputable def barycenter (η : ProbabilityMeasure (ProbabilityMeasure X)) :
    ProbabilityMeasure X :=
  ⟨(η : Measure (ProbabilityMeasure X)).bind (fun μ ↦ (μ : Measure X)),
    isProbabilityMeasure_bind measurable_subtype_coe.aemeasurable
      (ae_of_all _ fun μ ↦ μ.prop)⟩

end PaperN.PartI
