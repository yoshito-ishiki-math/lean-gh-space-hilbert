import PaperN.PartII.SpectralDensity
import PaperN.PartII.SelectedDistanceOperator

namespace PaperN.PartII
open MeasureTheory Metric PaperN.PartI
universe u
local instance (X : Type u) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance (X : Type u) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Apply the full density theorem to the same probability chosen in Part I;
full support is obtained internally from that selection. -/
theorem selectedSpectralDensity
    (hd : DistanceKernelSpectralInput.{u}) (hf : CompactEigenvalueFinitenessInput.{u})
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (ε : ℝ) (hε : 0 < ε) :
    let μ := (universalProbability hm hs X).toMeasure
    ∃ η : ℝ, 0 < η ∧ (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      FiniteDimensional ℝ (spectralCutoff μ η) ∧
      (⨆ x : X, infDist (distanceProfile x) (spectralCutoff μ η)) < ε ∧
      (Nontrivial X → 0 < Module.finrank ℝ (spectralCutoff μ η)) := by
  letI := openPos_of_support_eq_univ _ (universalProbability_fullSupport hm hs X)
  exact spectralDensity_spec hd hf X _ ε hε
end PaperN.PartII
