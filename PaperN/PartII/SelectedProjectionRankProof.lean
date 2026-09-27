import PaperN.PartII.AmbientContourProperties
import PaperN.PartII.CutoffRankStability

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI
open scoped Topology
set_option maxHeartbeats 800000

theorem selectedCutoffProjection_rank_proved
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
    ∀ᶠ n in atTop,
      Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedSequenceOperator hm hs C n)
        (Metric.diam (Set.univ : Set C)) η).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedLimitOperator hm hs C)
        (Metric.diam (Set.univ : Set C)) η).toLinearMap) := by
  have hlim := ambient_commonContour_properties ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability hm hs X : Measure X) hf   C.limit_isometry η hη hpos hneg
  letI : FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator
      (selectedLimitOperator hm hs C) (Metric.diam (Set.univ : Set C)) η).toLinearMap) := hlim.2.1
  have hseq : ∀ᶠ n in atTop, ∀ f,
      cutoffContourOperator (selectedSequenceOperator hm hs C n) (Metric.diam (Set.univ : Set C)) η
        (cutoffContourOperator (selectedSequenceOperator hm hs C n) (Metric.diam (Set.univ : Set C)) η f) =
      cutoffContourOperator (selectedSequenceOperator hm hs C n) (Metric.diam (Set.univ : Set C)) η f := by
    filter_upwards [selectedDistanceOperator_eventually_cutoff_resolvent hm hp hs C hH η hη hpos hneg] with n hn
    have h := ambient_commonContour_properties ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
      (selectedProbability hm hs (Xs n) : Measure (Xs n)) hf   (C.seq_isometry n) η hη hn.1 hn.2
    intro f
    exact congrArg (fun T : C(C, ℂ) →L[ℂ] C(C, ℂ) ↦ T f) h.1
  have hcompact := collectivelyCompact_cutoffContour_difference_tail
    (selectedSequenceOperator hm hs C) (selectedLimitOperator hm hs C)
    (selectedSequenceOperator_strong hm hs C hp hH)
    (selectedSequenceOperator_differences_collectivelyCompact hm hs C)
    (Metric.diam (Set.univ : Set C)) η Metric.diam_nonneg hη
    (fun z hz ↦ selectedLimitOperator_spectrum_bound hm hs C hz)
    ((nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry (η : ℂ) (by exact_mod_cast ne_of_gt hη)).mpr hpos)
    ((nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry ((-η : ℝ) : ℂ) (by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη))).mpr hneg)
  have hrank := collectivelyCompactTail_projection_rank_stable
    (fun n ↦ cutoffContourOperator (selectedSequenceOperator hm hs C n) (Metric.diam (Set.univ : Set C)) η)
    (cutoffContourOperator (selectedLimitOperator hm hs C) (Metric.diam (Set.univ : Set C)) η)
    (selectedCutoffProjection_strong hm hp hs C hH η hη hpos hneg) hcompact
    (fun f ↦ congrArg (fun T : C(C, ℂ) →L[ℂ] C(C, ℂ) ↦ T f) hlim.1) hseq
  exact hrank.mono (fun _ h ↦ h.2)
end PaperN.PartII.AmbientKernel
