import PaperN.PartI.GHPSeparationProof
import PaperN.PartI.GHCommonEmbeddingProof
import PaperN.PartI.CommonGHEmbedding

namespace PaperN.PartI
open Filter GromovHausdorff
open scoped Topology
universe u

/-- Forgetting probability is 1-Lipschitz for the internally constructed GHP metric. -/
theorem measuredForget_lipschitz :
    letI := ghpMetricInput_proved.metricSpace
    LipschitzWith 1 (MeasuredGHSpace.forget : MeasuredGHSpace.{u} → GHSpace) := by
  letI := ghpMetricInput_proved.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist x.forget y.forget ≤ (1 : ℝ) * MeasuredGHSpace.distance x y
  simpa only [one_mul] using MeasuredGHSpace.forget_distance_le x y

/-- The whole underlying carriers of a GHP-Cauchy sequence have a compact
common realization and an actual compact Hausdorff limit. No Polish input is used. -/
theorem ghpCauchy_common_underlying (Xs : ℕ → MeasuredCompact.{u})
    (h : letI := ghpMetricInput_proved.metricSpace
      CauchySeq (fun n ↦ (Xs n).toMeasuredGHSpace)) :
    ∃ (X : MeasuredCompact.{u}) (C : CommonRealization Xs X),
      C.HausdorffConverges ∧
      Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) := by
  letI := ghpMetricInput_proved.metricSpace
  have hc := measuredForget_lipschitz.uniformContinuous.comp_cauchySeq h
  exact commonGHCauchyEmbedding_spec ghCommonEmbeddingInput_proved Xs hc
end PaperN.PartI
