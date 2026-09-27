import PaperN.PartI.GHPExternalStatements
import PaperN.PartI.CommonAmbient

/-! Connecting cited GHP inputs to the manuscript. Every external theorem remains
an explicit argument; the theorems below are conditional on those arguments. -/
namespace PaperN.PartI
open MeasureTheory Filter TopologicalSpace
open scoped Topology
universe u

/-- thm:ghp-polish, conditional on the explicitly cited metric and Polish inputs. -/
theorem ghpPolish_spec (h : GHPMetricInput.{u}) (hp : GHPPolishInput h) : GHPPolishStatement h := by
  letI := h.metricSpace
  letI := hp.complete
  letI := hp.separable
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The previously proved numerical GH bound now gives the actual Lipschitz map. -/
theorem ghpForgetLipschitz_spec (h : GHPMetricInput.{u}) : GHPForgetLipschitzStatement h := by
  letI := h.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist x.forget y.forget ≤ (1 : ℝ) * MeasuredGHSpace.distance x y
  simpa only [one_mul] using MeasuredGHSpace.forget_distance_le x y

/-- Continuity and surjectivity only; openness remains an original-proof obligation. -/
theorem invariantProjectionContinuousSurjective_spec (h : GHPMetricInput.{0}) :
    InvariantProjectionContinuousSurjectiveStatement h := by
  letI := h.metricSpace
  letI := h.invariantMetricSpace
  exact ⟨(ghpForgetLipschitz_spec h).continuous.comp continuous_subtype_val,
    invariant_projection_surjective⟩

/-- lem:common-measured-embedding. Geometry is the explicit Khezeli input;
the weak-convergence conclusion is derived through the checked Prokhorov bridge. -/
theorem commonMeasuredEmbedding_spec (h : GHPCommonEmbeddingInput.{u}) :
    CommonMeasuredEmbeddingStatement.{u} := by
  intro Xs X hconv
  obtain ⟨C, hH, hP⟩ := h Xs X hconv
  exact ⟨C, hH, (weak_tendsto_iff_prokhorov C.seqProbability C.limitProbability).2 hP⟩

/-- The same conclusion starting from convergence in the conditional GHP metric. -/
theorem commonMeasuredEmbedding_of_tendsto (hm : GHPMetricInput.{u})
    (hc : GHPCommonEmbeddingInput.{u}) (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}) :
    letI := hm.metricSpace
    Tendsto (fun n ↦ (Xs n).toMeasuredGHSpace) atTop
      (𝓝 X.toMeasuredGHSpace) →
    ∃ C : CommonRealization Xs X, C.HausdorffConverges ∧ C.WeakConverges := by
  letI := hm.metricSpace
  intro hconv
  apply commonMeasuredEmbedding_spec hc Xs X
  change Tendsto (fun n ↦ dist (Xs n).toMeasuredGHSpace
    X.toMeasuredGHSpace) atTop (𝓝 0)
  exact tendsto_iff_dist_tendsto_zero.1 hconv
end PaperN.PartI
