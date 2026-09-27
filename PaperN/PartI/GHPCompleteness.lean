import PaperN.PartI.GHPCauchyRealization
import PaperN.PartI.VaryingFiberTransport
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace PaperN.PartI
open Filter Metric Set MeasureTheory
open scoped Topology
universe u

/-- Completeness of the exact max-infimum GHP metric, without the Polish input. -/
theorem ghp_completeSpace :
    letI := ghpMetricInput_proved.metricSpace
    CompleteSpace MeasuredGHSpace.{u} := by
  letI := ghpMetricInput_proved.metricSpace
  apply Metric.complete_of_cauchySeq_tendsto
  intro qs hqs
  choose Xs hXs using fun n ↦ Quotient.exists_rep (qs n)
  have hrep : (fun n ↦ (Xs n).toMeasuredGHSpace) = qs := funext hXs
  have hc : CauchySeq (fun n ↦ (Xs n).toMeasuredGHSpace) := by rwa [hrep]
  obtain ⟨X, C, hH, _⟩ := ghpCauchy_common_underlying Xs hc
  obtain ⟨ν, φ, hφ, hv⟩ := CompactSpace.tendsto_subseq C.seqProbability
  have hclosed : IsClosed (range C.limitMap) :=
    (isCompact_range C.limit_isometry.continuous).isClosed
  have hmass : (ν : Measure C) (range C.limitMap) = 1 := by
    apply limitSupport_spec (fun k ↦ range (C.seqMap (φ k))) (range C.limitMap)
      (fun k ↦ isCompact_range (C.seq_isometry (φ k)).continuous)
      (fun k ↦ range_nonempty _) (isCompact_range C.limit_isometry.continuous)
      (range_nonempty _) (hH.comp hφ.tendsto_atTop) (fun k ↦ C.seqProbability (φ k)) ν hv
    intro k
    change Measure.map (C.seqMap (φ k)) (Xs (φ k)).measure _ = 1
    rw [Measure.map_apply (C.seq_isometry (φ k)).continuous.measurable
      (isCompact_range (C.seq_isometry (φ k)).continuous).measurableSet]
    simp
  have he := C.limit_isometry.isClosedEmbedding.measurableEmbedding
  let ρ : ProbabilityMeasure X := ⟨(ν : Measure C).comap C.limitMap,
    he.isProbabilityMeasure_comap ((mem_ae_iff_prob_eq_one hclosed.measurableSet).mpr hmass)⟩
  have hρ : ρ.map C.limit_isometry.continuous.measurable.aemeasurable = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    change Measure.map C.limitMap ((ν : Measure C).comap C.limitMap) = _
    rw [he.map_comap]
    exact Measure.restrict_eq_self_of_ae_mem
      ((mem_ae_iff_prob_eq_one hclosed.measurableSet).mpr hmass)
  let D : CommonRealization (fun k ↦ Xs (φ k)) (X.withProbability ρ) := {
    Carrier := C, metric := inferInstance, compact := inferInstance,
    seqMap := fun k ↦ C.seqMap (φ k), limitMap := C.limitMap,
    seq_isometry := fun k ↦ C.seq_isometry (φ k), limit_isometry := C.limit_isometry }
  have hDW : D.WeakConverges := by
    change Tendsto (fun k ↦ C.seqProbability (φ k)) atTop (𝓝 (ρ.map _))
    rw [hρ]
    exact hv
  have hd := D.ghpDist_tendsto (hH.comp hφ.tendsto_atTop) hDW
  have ht : Tendsto (fun k ↦ (Xs (φ k)).toMeasuredGHSpace) atTop
      (𝓝 (X.withProbability ρ).toMeasuredGHSpace) :=
    tendsto_iff_dist_tendsto_zero.mpr hd
  refine ⟨(X.withProbability ρ).toMeasuredGHSpace, ?_⟩
  apply tendsto_nhds_of_cauchySeq_of_subseq hqs hφ.tendsto_atTop
  have heq : (fun k ↦ (Xs (φ k)).toMeasuredGHSpace) = qs ∘ φ :=
    funext (fun k ↦ hXs (φ k))
  rwa [heq] at ht
end PaperN.PartI
