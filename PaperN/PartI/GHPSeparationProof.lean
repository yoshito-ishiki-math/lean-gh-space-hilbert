import PaperN.PartI.UniformEmbeddingLimits
import PaperN.PartI.CompactRealizationRestriction
import PaperN.PartI.ZeroCostCoupling
import PaperN.PartI.GHPMetricFromSeparation

namespace PaperN.PartI
open Set Metric Filter MeasureTheory TopologicalSpace
open scoped Topology BoundedContinuousFunction
universe u

theorem isomorphic_of_ghpDist_eq_zero (X Y : MeasuredCompact.{u})
    (h : ghpDist X Y = 0) : X.Isomorphic Y := by
  obtain ⟨C, hh, hp⟩ := zero_ghp_compact_common_realization X Y h
  let f : ℕ → Y →ᵇ C := fun n ↦
    BoundedContinuousFunction.mkOfCompact ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
  obtain ⟨g, φ, hg, hφ, ht⟩ := isometry_embeddings_subsequence f C.seq_isometry
  let Ks : ℕ → NonemptyCompacts C := fun n ↦
    ⟨⟨range (f (φ n)), isCompact_range (f (φ n)).continuous⟩, range_nonempty _⟩
  let K : NonemptyCompacts C :=
    ⟨⟨range C.limitMap, isCompact_range C.limit_isometry.continuous⟩, range_nonempty _⟩
  let L : NonemptyCompacts C :=
    ⟨⟨range g, isCompact_range g.continuous⟩, range_nonempty _⟩
  have hK : Tendsto Ks atTop (𝓝 K) :=
    tendsto_iff_dist_tendsto_zero.mpr (hh.comp hφ.tendsto_atTop)
  have hL : Tendsto Ks atTop (𝓝 L) :=
    tendsto_iff_dist_tendsto_zero.mpr (hausdorffDist_range_tendsto_of_uniform (f ∘ φ) g ht)
  have hr : range g = range C.limitMap :=
    congrArg (fun k : NonemptyCompacts C ↦ (k : Set C)) (tendsto_nhds_unique hL hK)
  let ν : ProbabilityMeasure C := Y.probability.map g.continuous.measurable.aemeasurable
  have hν : Tendsto (fun n ↦ C.seqProbability (φ n)) atTop (𝓝 ν) :=
    (weak_tendsto_iff_prokhorov _ _).mpr
      (prokhorov_map_tendsto_of_uniform Y.measure (f ∘ φ) g ht)
  have hμ : Tendsto (fun n ↦ C.seqProbability (φ n)) atTop (𝓝 C.limitProbability) :=
    ((weak_tendsto_iff_prokhorov _ _).mpr hp).comp hφ.tendsto_atTop
  have hm : Measure.map g Y.measure = Measure.map C.limitMap X.measure :=
    congrArg ProbabilityMeasure.toMeasure (tendsto_nhds_unique hν hμ)
  let D : CompactCoupling Y X := {
    Carrier := C, metric := inferInstance, compact := inferInstance,
    left := g, right := C.limitMap, left_isometry := hg,
    right_isometry := C.limit_isometry }
  apply MeasuredCompact.isomorphic_symm
  apply D.isomorphic_of_cost_eq_zero
  change max (hausdorffEDist (range g) (range C.limitMap))
    (levyProkhorovEDist (Measure.map g Y.measure) (Measure.map C.limitMap X.measure)) = 0
  rw [hr, hm, hausdorffEDist_self, levyProkhorovEDist_self, max_self]

/-- Separation for the whole-carrier measured isometry quotient. -/
theorem ghpSeparation_proved : GHPSeparationStatement.{u} := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro X Y h
  exact Quotient.sound (isomorphic_of_ghpDist_eq_zero X Y h)

/-- The max-infimum GHP metric axioms are proved internally. -/
theorem ghpMetricInput_proved : GHPMetricInput.{u} :=
  ghpMetricInput_of_separation ghpSeparation_proved
end PaperN.PartI
