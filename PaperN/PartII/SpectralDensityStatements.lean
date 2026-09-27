import PaperN.PartII.ComplexifiedSpectrum

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

/-- All conclusions of lem:spectral-density, including endpoint avoidance in the
complexification and positive dimension for non-singleton carriers. -/
def SpectralDensityStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      FiniteDimensional ℝ (spectralCutoff μ η) ∧
      (⨆ x : X, infDist (distanceProfile x) (spectralCutoff μ η)) < ε ∧
      (Nontrivial X → 0 < Module.finrank ℝ (spectralCutoff μ η))
end PaperN.PartII
