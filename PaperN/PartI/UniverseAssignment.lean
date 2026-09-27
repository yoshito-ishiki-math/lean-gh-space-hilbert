import PaperN.PartI.GHSection

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff Filter Metric
open scoped Topology
universe u v w
local instance universeMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance universeBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

noncomputable def smallCarrier (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    MeasuredCompact.{0} := ghRepresentative (toGHSpace X)

noncomputable def smallCarrierEquiv (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    smallCarrier X ≃ᵢ X :=
  (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))).some

/-- One and the same small selection, transported to every universe. -/
noncomputable def universalProbability (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    @ProbabilityMeasure X (borel X) :=
  (selectedProbability hm hs (smallCarrier X)).map
    (smallCarrierEquiv X)

/-- The result is independent of the chosen small representative and identifying isometry. -/
theorem universalProbability_eq_map (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Y : MeasuredCompact.{0}) (e : Y ≃ᵢ X) :
    universalProbability hm hs X =
      (selectedProbability hm hs Y).map e := by
  letI : MeasurableSpace X := borel X
  let k := e.trans (smallCarrierEquiv X).symm
  have h := selectedProbability_natural hm hs Y (smallCarrier X) k
  unfold universalProbability
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [← congrArg ProbabilityMeasure.toMeasure h]
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (smallCarrierEquiv X).continuous.measurable k.continuous.measurable]
  congr 1
  funext x
  exact (smallCarrierEquiv X).apply_symm_apply (e x)

theorem universalProbability_natural (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) (Y : Type v) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (e : X ≃ᵢ Y) :
    (universalProbability hm hs X).map e =
      universalProbability hm hs Y := by
  letI : MeasurableSpace X := borel X
  letI : MeasurableSpace Y := borel Y
  rw [universalProbability_eq_map hm hs Y (smallCarrier X) ((smallCarrierEquiv X).trans e)]
  apply ProbabilityMeasure.toMeasure_injective
  simp only [universalProbability, ProbabilityMeasure.toMeasure_map]
  exact Measure.map_map e.continuous.measurable (smallCarrierEquiv X).continuous.measurable

theorem universalProbability_fullSupport (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X] :
    (universalProbability hm hs X).toMeasure.support = univ := by
  letI : MeasurableSpace X := borel X
  let μ := selectedProbability hm hs (smallCarrier X)
  haveI : Measure.IsOpenPosMeasure (μ : Measure (smallCarrier X)) :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs _).1
  haveI : Measure.IsOpenPosMeasure (universalProbability hm hs X).toMeasure := by
    constructor
    intro U hU hne
    change Measure.map (smallCarrierEquiv X) μ U ≠ 0
    rw [Measure.map_apply (smallCarrierEquiv X).continuous.measurable hU.measurableSet]
    exact (hU.preimage (smallCarrierEquiv X).continuous).measure_ne_zero _
      (hne.preimage (smallCarrierEquiv X).surjective)
  exact Measure.support_eq_univ
theorem small_range (Y : Type u) (Z : Type w)
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [Nonempty Z] (f : Y → Z) :
    range ((smallCarrierEquiv Z).symm ∘ f ∘ smallCarrierEquiv Y) =
      (smallCarrierEquiv Z).symm '' range f := by
  simp only [range_comp, (smallCarrierEquiv Y).surjective.range_eq, image_univ]

theorem small_mapped (hm : GHPMetricInput.{0})
  (hs : InvariantFiberLawSelectionStatement hm)
  (Z : Type w) [MetricSpace Z] [CompactSpace Z] [Nonempty Z]
  (Y : Type u) [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    (f : Y → Z) (hf : Isometry f) :
    ((selectedProbability hm hs (smallCarrier Y)).map
      ((smallCarrierEquiv Z).symm ∘ f ∘ smallCarrierEquiv Y)).map
      (smallCarrierEquiv Z) =
    (universalProbability hm hs Y).map f := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [universalProbability, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (smallCarrierEquiv Z).continuous.measurable
    ((smallCarrierEquiv Z).symm.isometry.comp (hf.comp (smallCarrierEquiv Y).isometry)).continuous.measurable,
    Measure.map_map hf.continuous.measurable (smallCarrierEquiv Y).continuous.measurable]
  congr 1
  funext y
  exact (smallCarrierEquiv Z).apply_symm_apply (f (smallCarrierEquiv Y y))

/-- M3 in any prescribed compact ambient, allowing unrelated carrier universes. -/
theorem universalProbability_tendsto (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    (Xs : ℕ → Type u) (X : Type v) (Z : Type w)
    [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
    [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Z] [CompactSpace Z]
    (es : ∀ n, Xs n → Z) (e : X → Z) (hes : ∀ n, Isometry (es n)) (he : Isometry e)
    (hH : Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (universalProbability hm hs (Xs n)).map
      (es n)) atTop
      (𝓝 ((universalProbability hm hs X).map e)) := by
  letI : Nonempty Z := ⟨e (Classical.choice inferInstance)⟩
  let C : CommonRealization (fun n ↦ smallCarrier (Xs n)) (smallCarrier X) := {
    Carrier := smallCarrier Z
    metric := inferInstance
    compact := inferInstance
    seqMap := fun n ↦ (smallCarrierEquiv Z).symm ∘ es n ∘ smallCarrierEquiv (Xs n)
    limitMap := (smallCarrierEquiv Z).symm ∘ e ∘ smallCarrierEquiv X
    seq_isometry := fun n ↦ (smallCarrierEquiv Z).symm.isometry.comp
      ((hes n).comp (smallCarrierEquiv (Xs n)).isometry)
    limit_isometry := (smallCarrierEquiv Z).symm.isometry.comp
      (he.comp (smallCarrierEquiv X).isometry) }
  have hC : C.HausdorffConverges := by
    simpa only [CommonRealization.HausdorffConverges, C, small_range,
      hausdorffDist_image (smallCarrierEquiv Z).symm.isometry] using hH
  have h := selectedProbability_tendsto hm hp hs _ _ C hC
  have h' := (ProbabilityMeasure.continuous_map (smallCarrierEquiv Z).continuous).continuousAt.tendsto.comp h
  convert h' using 1
  · funext n
    exact (small_mapped hm hs Z (Xs n) (es n) (hes n)).symm
  · exact congrArg nhds (small_mapped hm hs Z X e he).symm
end PaperN.PartI
