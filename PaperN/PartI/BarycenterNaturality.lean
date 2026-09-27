import PaperN.PartI.Barycenter
import PaperN.PartI.ValovInput

namespace PaperN.PartI
open MeasureTheory Set
variable {A B : Type*} [MetricSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  [MetricSpace B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]

/-- Barycenters commute with pushforward by a continuous map. -/
theorem barycenter_map (f : C(A, B)) (η : ProbabilityMeasure (ProbabilityMeasure A)) :
    (barycenter η).map f =
      barycenter (η.map (probabilityPushforward f)) := by
  apply ProbabilityMeasure.toMeasure_injective
  ext S hS
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply f.continuous.measurable hS,
    barycenter_apply _ (f.continuous.measurable hS), barycenter_apply _ hS,
    ProbabilityMeasure.toMeasure_map]
  rw [lintegral_map (show Measurable (fun μ : ProbabilityMeasure B ↦ (μ : Measure B) S)
    from (Measure.measurable_coe hS).comp measurable_subtype_coe)
    (probabilityPushforward f).continuous.measurable]
  apply lintegral_congr
  intro μ
  exact (Measure.map_apply f.continuous.measurable hS).symm
end PaperN.PartI
