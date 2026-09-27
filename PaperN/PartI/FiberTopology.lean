import PaperN.PartI.FiberTransport
import PaperN.PartI.CommonGHPConvergence

namespace PaperN.PartI
open MeasureTheory Set Metric Filter TopologicalSpace Topology
open scoped Topology
universe u

/-- On a fixed carrier, the identity coupling bounds GHP by Prokhorov. -/
theorem ghpDist_withProbability_le (X : MeasuredCompact.{u}) (μ ν : ProbabilityMeasure X) :
    ghpDist (X.withProbability μ) (X.withProbability ν) ≤
      levyProkhorovDist (μ : Measure X) (ν : Measure X) := by
  let C : CommonRealization (fun _ ↦ X.withProbability μ) (X.withProbability ν) :=
    ⟨X, inferInstance, inferInstance, fun _ ↦ id, id, fun _ ↦ isometry_id, isometry_id⟩
  have h := C.ghpDist_le_max 0
  change ghpDist (X.withProbability μ) (X.withProbability ν) ≤
    max (hausdorffDist (range (id : X → X)) (range id))
      (levyProkhorovDist (Measure.map id (μ : Measure X)) (Measure.map id (ν : Measure X))) at h
  simpa only [hausdorffDist_self_zero, Measure.map_id,
    max_eq_right (show 0 ≤ levyProkhorovDist (μ : Measure X) (ν : Measure X) from
      ENNReal.toReal_nonneg)] using h

/-- Weak convergence on a fixed carrier implies convergence of its measured classes. -/
theorem continuous_probabilityClass (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
    letI := hm.metricSpace
    Continuous (fun μ : ProbabilityMeasure X ↦ (X.withProbability μ).toMeasuredGHSpace) := by
  letI := hm.metricSpace
  apply continuous_iff_continuousAt.mpr
  intro μ
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hP := (weak_tendsto_iff_prokhorov (id : ProbabilityMeasure X → ProbabilityMeasure X) μ).mp
    (tendsto_id : Tendsto id (𝓝 μ) (𝓝 μ))
  exact squeeze_zero (fun _ ↦ ENNReal.toReal_nonneg)
    (fun ν ↦ ghpDist_withProbability_le X ν μ) hP

instance (X : MeasuredCompact.{u}) : CompactSpace (InvariantProbability X) := by
  apply isCompact_iff_compactSpace.mp
  exact (show IsClosed {μ : ProbabilityMeasure X | ∀ g : X ≃ᵢ X,
    Measure.map g (μ : Measure X) = (μ : Measure X)} from fixedInvariantClosed_spec).isCompact

/-- Compactness makes the injective map on all invariant probabilities a topological embedding. -/
theorem isEmbedding_invariantProbabilityClass (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
    letI := hm.metricSpace
    IsEmbedding (fun μ : InvariantProbability X ↦ (X.withProbability μ.val).toMeasuredGHSpace) := by
  letI := hm.metricSpace
  have hinj : Function.Injective (fun μ : InvariantProbability X ↦
      (X.withProbability μ.val).toMeasuredGHSpace) := by
    intro μ ν h
    apply Subtype.ext
    exact probability_eq_of_invariant_class_eq X _ _ μ.property h
  exact (((continuous_probabilityClass hm X).comp continuous_subtype_val).isClosedEmbedding hinj).isEmbedding

/-- The actual fiber transport is continuous, including its full-support restriction. -/
theorem continuous_fiberProbability (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    Continuous (fiberProbability X) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  let F : InvariantFiber X → InvariantProbability X := fun q ↦
    ⟨fiberProbability X q, (fiberProbability_fullSupport_invariant X q).2⟩
  have hF : Continuous F := by
    apply (isEmbedding_invariantProbabilityClass hm X).continuous_iff.mpr
    have he : (fun μ : InvariantProbability X ↦ (X.withProbability μ.val).toMeasuredGHSpace) ∘ F =
        (fun q : InvariantFiber X ↦ q.val.val) := by
      funext q
      exact fiberProbability_class X q
    rw [he]
    exact continuous_subtype_val.comp continuous_subtype_val
  exact continuous_subtype_val.comp hF
end PaperN.PartI
