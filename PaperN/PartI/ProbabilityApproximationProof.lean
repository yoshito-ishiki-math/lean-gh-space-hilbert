import PaperN.PartI.MeasurableNearMap
import PaperN.PartI.LiftInputs
import Mathlib.Analysis.SpecificLimits.Basic

namespace PaperN.PartI
open MeasureTheory Set Metric Filter
open scoped Topology

/-- Approximate the limiting probability by measurable near-point transport. -/
theorem probabilityApproximationInput_proved : ProbabilityApproximationInput.{u} := by
  classical
  intro Xs X C hC
  let δ := fun n ↦ hausdorffDist (range (C.seqMap n)) (range C.limitMap) + 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 ≤ δ n := fun n ↦ add_nonneg hausdorffDist_nonneg (by positivity)
  have hlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [add_zero] using hC.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs : ∀ n, ∃ s : X → Xs n, Measurable s ∧
      ∀ x, dist (C.limitMap x) (C.seqMap n (s x)) < δ n := by
    intro n
    apply exists_measurable_map_of_hausdorffDist_lt C.limitMap C.limit_isometry.continuous
      (C.seqMap n) (C.seq_isometry n).continuous (δ n)
    rw [hausdorffDist_comm]
    exact lt_add_of_pos_right _ (by positivity)
  choose s hm hd using hs
  let μ := fun n ↦ X.probability.map (hm n).aemeasurable
  refine ⟨μ, ?_⟩
  have h := levyProkhorovDist_map_tendsto_of_dist_le (X.probability : Measure X)
    (fun n ↦ C.seqMap n ∘ s n) C.limitMap
    (fun n ↦ (C.seq_isometry n).continuous.measurable.comp (hm n))
    C.limit_isometry.continuous.measurable δ hδ hlim
    (fun n x ↦ by simpa only [Function.comp_apply, dist_comm] using (hd n x).le)
  unfold CommonRealization.ProkhorovConverges
  convert h using 1
  funext n
  change levyProkhorovDist
    (((X.probability.map (hm n).aemeasurable).map
      (C.seq_isometry n).continuous.measurable.aemeasurable).toMeasure)
    ((X.probability.map C.limit_isometry.continuous.measurable.aemeasurable).toMeasure) = _
  simp only [ProbabilityMeasure.toMeasure_map,
    Measure.map_map (C.seq_isometry n).continuous.measurable (hm n)]
end PaperN.PartI
