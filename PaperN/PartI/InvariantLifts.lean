import PaperN.PartI.InvariantLiftsStatements
import PaperN.PartI.InvariantApproximation

namespace PaperN.PartI
open MeasureTheory Filter GromovHausdorff
open scoped Topology
universe u

/-- The whole lifting lemma, conditional only on explicit geometric/probability inputs
and the GHP metric axioms. Full support and invariance are proved by construction. -/
theorem invariantLifts_spec (hm : GHPMetricInput.{u}) (hg : GHCommonEmbeddingInput.{u})
    (ha : ProbabilityApproximationInput.{u}) : InvariantLiftsStatement hm := by
  letI := hm.metricSpace
  intro Xs X hX hconv
  obtain ⟨C, hH⟩ := hg Xs X hconv
  obtain ⟨μ, hμ⟩ := ha Xs X C hH
  let D := C.withProbabilities μ
  have hW : D.WeakConverges :=
    (weak_tendsto_iff_prokhorov D.seqProbability D.limitProbability).mpr hμ
  obtain ⟨ν, hν, _, hdist⟩ := D.invariantApproximation_spec hH hW hX.2
  refine ⟨ν, hν, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact hdist
end PaperN.PartI
