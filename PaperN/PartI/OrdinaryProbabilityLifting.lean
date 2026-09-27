import PaperN.PartI.GHPSeparationProof
import PaperN.PartI.GHCommonEmbeddingProof
import PaperN.PartI.ProbabilityApproximationProof
import PaperN.PartI.CommonGHPConvergence

namespace PaperN.PartI
open Filter GromovHausdorff MeasureTheory
open scoped Topology
universe u

/-- Any GH-convergent sequence of whole carriers can carry probabilities
converging to a prescribed measured limit. No Polish or selection input is used. -/
theorem exists_probabilities_ghp_tendsto (Xs : ℕ → MeasuredCompact.{u})
    (X : MeasuredCompact.{u})
    (h : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X))) :
    ∃ μ : ∀ n, ProbabilityMeasure (Xs n),
      Tendsto (fun n ↦ ghpDist ((Xs n).withProbability (μ n)) X) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := ghCommonEmbeddingInput_proved Xs X h
  obtain ⟨μ, hμ⟩ := probabilityApproximationInput_proved Xs X C hC
  refine ⟨μ, (C.withProbabilities μ).ghpDist_tendsto hC ?_⟩
  exact (weak_tendsto_iff_prokhorov _ _).mpr hμ

/-- The same lifting conclusion in the internally constructed measured metric. -/
theorem exists_probability_classes_tendsto (Xs : ℕ → MeasuredCompact.{u})
    (X : MeasuredCompact.{u})
    (h : Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X))) :
    letI := ghpMetricInput_proved.metricSpace
    ∃ μ : ∀ n, ProbabilityMeasure (Xs n),
      Tendsto (fun n ↦ ((Xs n).withProbability (μ n)).toMeasuredGHSpace)
        atTop (𝓝 X.toMeasuredGHSpace) := by
  letI := ghpMetricInput_proved.metricSpace
  obtain ⟨μ, hμ⟩ := exists_probabilities_ghp_tendsto Xs X h
  exact ⟨μ, tendsto_iff_dist_tendsto_zero.mpr hμ⟩
end PaperN.PartI
