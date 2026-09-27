import PaperN.PartII.ProjectionCutoffDimension
import PaperN.PartII.AmbientContourProperties

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI
open scoped Topology

/-- Fixed-contour form of the spectral-projection proposition. Properties of
sequence projections are asserted only eventually, after gap exclusion. -/
def SpectralProjectionsStatement
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
    (C : CommonRealization Xs X) (η : ℝ) : Prop :=
  let P := cutoffContourOperator (selectedLimitOperator hm hs C) (Metric.diam (Set.univ : Set C)) η
  let Ps := fun n ↦ cutoffContourOperator (selectedSequenceOperator hm hs C n)
    (Metric.diam (Set.univ : Set C)) η
  SpectralProjectionProperties (selectedLimitOperator hm hs C) P η ∧
  (∀ᶠ n in atTop,
    (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs (Xs n) : Measure (Xs n))) ∧
    ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs (Xs n) : Measure (Xs n))) ∧
    Module.finrank ℝ (spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) =
      Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η) ∧
    SpectralProjectionProperties (selectedSequenceOperator hm hs C n) (Ps n) η) ∧
  ∀ f, Tendsto (fun n ↦ Ps n f) atTop (𝓝 (P f))

theorem spectralProjections_spec
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
    (C : CommonRealization Xs X)


    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : C.HausdorffConverges) (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    SpectralProjectionsStatement hm hs C η := by
  refine ⟨?_, ?_, selectedCutoffProjection_strong hm hp hs C hH η hη hpos hneg⟩
  · exact ambient_commonContour_properties ⟨C.limitMap, C.limit_isometry.continuous⟩
      (selectedProbability hm hs X : Measure X) hf   C.limit_isometry η hη hpos hneg
  · filter_upwards [selectedDistanceOperator_eventually_cutoff_resolvent hm hp hs C  hH η hη hpos hneg,
      selectedCutoff_eventual_real_dimension hm hp hs C   hf   hH η hη hpos hneg] with n hn hd
    exact ⟨hn.1, hn.2, hd,
      ambient_commonContour_properties ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
        (selectedProbability hm hs (Xs n) : Measure (Xs n)) hf   (C.seq_isometry n) η hη hn.1 hn.2⟩

end PaperN.PartII.AmbientKernel
