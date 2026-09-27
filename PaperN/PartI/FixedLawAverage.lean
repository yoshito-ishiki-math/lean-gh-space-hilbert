import PaperN.PartI.FixedProbability
import PaperN.PartI.Solution

namespace PaperN.PartI
open MeasureTheory Set Filter
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Borel measurability here uses the proved Giry/weak-Borel bridge on compact carriers. -/
theorem measurableSet_fixedInvariantFullSupport :
    MeasurableSet {μ : ProbabilityMeasure X | (μ : Measure X).support = univ ∧
      ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)} :=
  (fixedInvariantFullSupportGDelta_spec (X := X)).measurableSet

/-- The fixed-carrier averaging step in the proof of `thm:invariant-measures`.
Obtaining and transporting the law from the varying measured-GH fiber is a separate task. -/
theorem fixedLawAverage_spec : FixedLawAverageStatement (X := X) := by
  intro η hη
  let S : Set (ProbabilityMeasure X) := {μ | (μ : Measure X).support = univ ∧
    ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)}
  have hS : MeasurableSet S := measurableSet_fixedInvariantFullSupport
  have ha : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)), μ ∈ S :=
    (mem_ae_iff_prob_eq_one hS).mpr hη
  obtain ⟨_, _, _, hfull, hinv⟩ := continuousBarycenter_spec (X := X)
  refine ⟨hfull η S hS hη (fun μ hμ ↦ hμ.1), fun g ↦ hinv η g ?_⟩
  filter_upwards [ha] with μ hμ
  exact hμ.2 g

end PaperN.PartI
