import PaperN.PartI.LimitSupport
import PaperN.PartI.FiberTopology
import PaperN.PartI.VaryingFiberTransportStatements

namespace PaperN.PartI
open MeasureTheory Metric Filter Set
open scoped Topology
universe u

/-- `eq:fiber-pullbacks`, for arbitrary prescribed embeddings into a compact ambient space.
Only the existing GHP metric input is needed; no common-embedding existence input is used. -/
theorem varying_fiberProbability_tendsto (hm : GHPMetricInput.{u})
    (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges)
    (qs : ∀ n, InvariantFiber (Xs n)) (q : InvariantFiber X) :
    letI := hm.metricSpace
    Tendsto (fun n ↦ (qs n).val.val) atTop (𝓝 q.val.val) →
    Tendsto (fun n ↦ (fiberProbability (Xs n) (qs n)).map
      (C.seq_isometry n).continuous.measurable.aemeasurable) atTop
      (𝓝 ((fiberProbability X q).map C.limit_isometry.continuous.measurable.aemeasurable)) := by
  letI := hm.metricSpace
  intro hq
  let ps (n : ℕ) : ProbabilityMeasure C :=
    (fiberProbability (Xs n) (qs n)).map (C.seq_isometry n).continuous.measurable.aemeasurable
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ν hν
  obtain ⟨φ, hφ, hv⟩ := hν.tendsto_subseq
  have hclosed : IsClosed (range C.limitMap) :=
    (isCompact_range C.limit_isometry.continuous).isClosed
  have hmass : (ν : Measure C) (range C.limitMap) = 1 := by
    apply limitSupport_spec (fun k ↦ range (C.seqMap (φ k))) (range C.limitMap)
      (fun k ↦ isCompact_range (C.seq_isometry (φ k)).continuous)
      (fun k ↦ range_nonempty _) (isCompact_range C.limit_isometry.continuous)
      (range_nonempty _) (hH.comp hφ.tendsto_atTop) (fun k ↦ ps (φ k)) ν hv
    intro k
    change Measure.map (C.seqMap (φ k))
      (fiberProbability (Xs (φ k)) (qs (φ k)) : Measure (Xs (φ k))) _ = 1
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
  let D : CommonRealization
      (fun k ↦ (Xs (φ k)).withProbability (fiberProbability (Xs (φ k)) (qs (φ k))))
      (X.withProbability ρ) := {
    Carrier := C
    metric := inferInstance
    compact := inferInstance
    seqMap := fun k ↦ C.seqMap (φ k)
    limitMap := C.limitMap
    seq_isometry := fun k ↦ C.seq_isometry (φ k)
    limit_isometry := C.limit_isometry }
  have hDH : D.HausdorffConverges := hH.comp hφ.tendsto_atTop
  have hDW : D.WeakConverges := by
    change Tendsto (fun k ↦ ps (φ k)) atTop (𝓝 (ρ.map _))
    rw [hρ]
    exact hv
  have hconv : Tendsto (fun k ↦ (qs (φ k)).val.val) atTop
      (𝓝 (X.withProbability ρ).toMeasuredGHSpace) := by
    have hd := D.ghpDist_tendsto hDH hDW
    have ht : Tendsto
        (fun k ↦ ((Xs (φ k)).withProbability (fiberProbability (Xs (φ k)) (qs (φ k)))).toMeasuredGHSpace)
        atTop (𝓝 (X.withProbability ρ).toMeasuredGHSpace) :=
      tendsto_iff_dist_tendsto_zero.mpr hd
    simpa only [fiberProbability_class] using ht
  have hclass : (X.withProbability ρ).toMeasuredGHSpace = q.val.val :=
    tendsto_nhds_unique hconv (hq.comp hφ.tendsto_atTop)
  have heq := fiberProbability_unique X q ρ hclass
  exact hρ.symm.trans (congrArg (fun p : ProbabilityMeasure X ↦ p.map
    C.limit_isometry.continuous.measurable.aemeasurable) heq.symm)
/-- Connection to the separately reviewable varying-carrier statement. -/
theorem varyingFiberTransport_spec (hm : GHPMetricInput.{u}) :
    VaryingFiberTransportStatement hm := varying_fiberProbability_tendsto hm

/-- Continuous test functions commute with fiber transport along varying carriers. -/
theorem varying_fiberProbability_integral_tendsto (hm : GHPMetricInput.{u})
    (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges)
    (qs : ∀ n, InvariantFiber (Xs n)) (q : InvariantFiber X) (f : C(C, ℝ)) :
    letI := hm.metricSpace
    Tendsto (fun n ↦ (qs n).val.val) atTop (𝓝 q.val.val) →
    Tendsto (fun n ↦ ∫ x, f (C.seqMap n x) ∂(fiberProbability (Xs n) (qs n) : Measure (Xs n)))
      atTop (𝓝 (∫ x, f (C.limitMap x) ∂(fiberProbability X q : Measure X))) := by
  letI := hm.metricSpace
  intro hq
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (varying_fiberProbability_tendsto hm Xs X C hH qs q hq)
    (BoundedContinuousFunction.mkOfCompact f)
  change Tendsto (fun n ↦ ∫ z, f z ∂Measure.map (C.seqMap n)
    (fiberProbability (Xs n) (qs n) : Measure (Xs n))) atTop
    (𝓝 (∫ z, f z ∂Measure.map C.limitMap (fiberProbability X q : Measure X))) at ht
  simpa only [integral_map
    (C.seq_isometry _).continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable,
    integral_map C.limit_isometry.continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable] using ht
end PaperN.PartI
