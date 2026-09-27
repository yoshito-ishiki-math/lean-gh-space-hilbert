import PaperN.PartI.Barycenter

namespace PaperN.PartI
open MeasureTheory Set
variable {A : Type*} [MeasurableSpace A]

/-- A probability giving full mass to a measurable subset, viewed as a probability on that subset. -/
noncomputable def probabilityOnSubtype (η : ProbabilityMeasure A) (s : Set A)
    (hs : MeasurableSet s) (hη : (η : Measure A) s = 1) : ProbabilityMeasure s := by
  refine ⟨(η : Measure A).comap Subtype.val, ?_⟩
  apply (MeasurableEmbedding.subtype_coe hs).isProbabilityMeasure_comap
  rw [Subtype.range_coe]
  change s ∈ ae (η : Measure A)
  exact (mem_ae_iff_prob_eq_one hs).mpr hη

/-- Restricting to a full-mass subset and including it again recovers the original law. -/
theorem map_probabilityOnSubtype (η : ProbabilityMeasure A) (s : Set A)
    (hs : MeasurableSet s) (hη : (η : Measure A) s = 1) :
    (probabilityOnSubtype η s hs hη).map measurable_subtype_coe.aemeasurable = η := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map Subtype.val ((η : Measure A).comap Subtype.val) = (η : Measure A)
  rw [map_comap_subtype_coe hs]
  exact Measure.restrict_eq_self_of_ae_mem ((mem_ae_iff_prob_eq_one hs).mpr hη)
end PaperN.PartI
