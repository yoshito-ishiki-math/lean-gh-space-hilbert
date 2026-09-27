import PaperN.PartII.CollectivelyCompactSpectralInput
import PaperN.PartII.ContourComparison
import PaperN.PartII.CutoffContourConvergence

namespace PaperN.PartII
open Filter
open scoped Topology
universe u

/-- Anselone--Palmer Proposition 6.3, for the fixed positive/negative
rectangular contour. An explicit general input; no inhabitant is asserted. -/
def CutoffProjectionConvergenceInput : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E),
    (∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x))) →
    (∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) →
    ∀ D η : ℝ, 0 ≤ D → 0 < η →
    (∀ z ∈ spectrum ℂ U, z.im = 0 ∧ ‖z‖ ≤ D) →
    (η : ℂ) ∈ resolventSet ℂ U → ((-η : ℝ) : ℂ) ∈ resolventSet ℂ U →
    (∀ x, Tendsto (fun n ↦ cutoffContourOperator (Us n) D η x) atTop
      (𝓝 (cutoffContourOperator U D η x))) ∧
    (FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator U D η).toLinearMap) →
      ∀ᶠ n in atTop,
        FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (Us n) D η).toLinearMap) ∧
        Module.finrank ℂ (LinearMap.range (cutoffContourOperator (Us n) D η).toLinearMap) =
          Module.finrank ℂ (LinearMap.range (cutoffContourOperator U D η).toLinearMap))

namespace AmbientKernel
open MeasureTheory PaperN.PartI
variable (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
variable (hs : InvariantFiberLawSelectionStatement hm)
variable {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
variable (C : CommonRealization Xs X)

theorem selectedLimitOperator_spectrum_bound {z : ℂ}
    (hz : z ∈ spectrum ℂ (selectedLimitOperator hm hs C)) :
    z.im = 0 ∧ ‖z‖ ≤ Metric.diam (Set.univ : Set C) := by
  have h := ambient_spectrum_interval ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability hm hs X : Measure X) C.limit_isometry hz
  refine ⟨h.1, ?_⟩
  have he : z = (z.re : ℂ) := Complex.ext rfl (by simpa using h.1)
  calc
    ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm he
    _ = |z.re| := by simp
    _ ≤ _ := abs_le.mpr h.2

include hp in
theorem selectedCutoffProjection_strong
    (hH : C.HausdorffConverges)
    (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    ∀ f, Tendsto (fun n ↦ cutoffContourOperator (selectedSequenceOperator hm hs C n)
      (Metric.diam (Set.univ : Set C)) η f) atTop
      (𝓝 (cutoffContourOperator (selectedLimitOperator hm hs C)
        (Metric.diam (Set.univ : Set C)) η f)) := by
  intro f
  apply collectivelyCompact_cutoffContourOperator_tendsto
    (selectedSequenceOperator hm hs C) (selectedLimitOperator hm hs C)
    (selectedSequenceOperator_strong hm hs C hp hH)
    (selectedSequenceOperator_differences_collectivelyCompact hm hs C)
    _ η Metric.diam_nonneg hη
  · intro z hz
    exact selectedLimitOperator_spectrum_bound hm hs C hz
  · exact (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry (η : ℂ) (by exact_mod_cast ne_of_gt hη)).mpr hpos
  · exact (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry ((-η : ℝ) : ℂ)
      (by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη))).mpr hneg

include hp in
theorem selectedCutoffProjection_convergence
    (hP : CutoffProjectionConvergenceInput.{0}) (hH : C.HausdorffConverges)
    (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    (∀ f, Tendsto (fun n ↦ cutoffContourOperator (selectedSequenceOperator hm hs C n)
      (Metric.diam (Set.univ : Set C)) η f) atTop
      (𝓝 (cutoffContourOperator (selectedLimitOperator hm hs C) (Metric.diam (Set.univ : Set C)) η f))) ∧
    (FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (selectedLimitOperator hm hs C)
      (Metric.diam (Set.univ : Set C)) η).toLinearMap) →
      ∀ᶠ n in atTop,
        FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (selectedSequenceOperator hm hs C n)
          (Metric.diam (Set.univ : Set C)) η).toLinearMap) ∧
        Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedSequenceOperator hm hs C n)
          (Metric.diam (Set.univ : Set C)) η).toLinearMap) =
        Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedLimitOperator hm hs C)
          (Metric.diam (Set.univ : Set C)) η).toLinearMap)) := by
  apply hP C(C, ℂ) _ _ (selectedSequenceOperator_strong hm hs C hp hH)
    (selectedSequenceOperator_differences_collectivelyCompact hm hs C)
    _ η Metric.diam_nonneg hη
  · intro z hz
    exact selectedLimitOperator_spectrum_bound hm hs C hz
  · exact (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry (η : ℂ) (by exact_mod_cast ne_of_gt hη)).mpr hpos
  · exact (nonzero_resolventSet_iff ⟨C.limitMap, C.limit_isometry.continuous⟩ _
      C.limit_isometry ((-η : ℝ) : ℂ)
      (by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη))).mpr hneg

theorem selectedLimitProjection_finiteDimensional
    (hf : CompactEigenvalueFinitenessInput.{0})
     (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (selectedLimitOperator hm hs C)
      (Metric.diam (Set.univ : Set C)) η).toLinearMap) := by
  let e : C(X, C) := ⟨C.limitMap, C.limit_isometry.continuous⟩
  let μ := (selectedProbability hm hs X : Measure X)
  have he : Isometry e := C.limit_isometry
  have hne : (η : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη
  have hnne : ((-η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη)
  have hd : Metric.diam (Set.univ : Set X) ≤ Metric.diam (Set.univ : Set C) := by
    rw [← he.diam_image (Set.univ : Set X)]
    exact Metric.diam_mono (Set.subset_univ _) isCompact_univ.isBounded
  have hr := ambient_cutoffContour_eq_circle_of_bound e μ he _ Metric.diam_nonneg hd η hη hpos hneg
  change FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (ambientOperator e μ)
    (Metric.diam (Set.univ : Set C)) η).toLinearMap)
  rw [hr]
  have ho := cutoffOuter_gt (Metric.diam (Set.univ : Set C)) η Metric.diam_nonneg hη
  change FiniteDimensional ℂ (LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η _).toLinearMap)
  rw [ambient_cutoffCircle_range e μ  he η _ hη ho.2 (hd.trans_lt ho.1) hpos hneg]
  exact ambientCutoff_finiteDimensional e μ hf he η hη

include hp in
theorem selectedCutoffProjection_eventual_rank
    (hP : CutoffProjectionConvergenceInput.{0}) (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : C.HausdorffConverges) (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X))) :
    ∀ᶠ n in atTop,
      FiniteDimensional ℂ (LinearMap.range (cutoffContourOperator (selectedSequenceOperator hm hs C n)
        (Metric.diam (Set.univ : Set C)) η).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedSequenceOperator hm hs C n)
        (Metric.diam (Set.univ : Set C)) η).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (cutoffContourOperator (selectedLimitOperator hm hs C)
        (Metric.diam (Set.univ : Set C)) η).toLinearMap) :=
  (selectedCutoffProjection_convergence hm hp hs C hP hH η hη hpos hneg).2
    (selectedLimitProjection_finiteDimensional hm hs C hf   η hη hpos hneg)

end AmbientKernel
end PaperN.PartII
