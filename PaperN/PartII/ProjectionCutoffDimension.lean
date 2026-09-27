import PaperN.PartII.CutoffDimension
import PaperN.PartII.SelectedProjectionRankProof
import PaperN.PartII.CutoffProjectionConvergence
import PaperN.PartII.CollectivelyCompactSpectralInput

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem ambientProjection_finrank_eq_realCutoff
    (hf : CompactEigenvalueFinitenessInput.{u})
     (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    Module.finrank ℂ (LinearMap.range (cutoffContourOperator (ambientOperator e μ)
      (Metric.diam (Set.univ : Set Z)) η).toLinearMap) =
      Module.finrank ℝ (spectralCutoff μ η) := by
  have hb : ∀ z ∈ spectrum ℂ (ambientOperator e μ), z.im = 0 ∧ ‖z‖ ≤ Metric.diam (Set.univ : Set Z) := by
    intro z hz
    have h := ambient_spectrum_interval e μ he hz
    refine ⟨h.1, ?_⟩
    have hz' : z = (z.re : ℂ) := Complex.ext rfl (by simpa using h.1)
    calc
      ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hz'
      _ = |z.re| := by simp
      _ ≤ _ := abs_le.mpr h.2
  have hne : (η : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hη
  have hnne : ((-η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast neg_ne_zero.mpr (ne_of_gt hη)
  have hd : Metric.diam (Set.univ : Set X) ≤ Metric.diam (Set.univ : Set Z) := by
    rw [← he.diam_image (Set.univ : Set X)]
    exact Metric.diam_mono (Set.subset_univ _) isCompact_univ.isBounded
  rw [ambient_cutoffContour_eq_circle_of_bound e μ he _ Metric.diam_nonneg hd η hη hp hn]
  have ho := cutoffOuter_gt (Metric.diam (Set.univ : Set Z)) η Metric.diam_nonneg hη
  calc
    _ = Module.finrank ℂ (complexAlgebraicCutoff (ComplexKernel.distanceOperator μ) η) :=
      (restrictionCircleRangeEquiv e μ  he η _ hη ho.2 (hd.trans_lt ho.1) hp hn).finrank_eq
    _ = _ := complexCutoff_finrank_eq_continuous_real μ hf η hη

end PaperN.PartII.AmbientKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI
open scoped Topology

theorem selectedCutoff_eventual_real_dimension
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
      Module.finrank ℝ (spectralCutoff (selectedProbability hm hs (Xs n) : Measure (Xs n)) η) =
      Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η) := by
  filter_upwards [selectedDistanceOperator_eventually_cutoff_resolvent hm hp hs C  hH η hη hpos hneg,
    selectedCutoffProjection_rank_proved hm hp hs C hf   hH η hη hpos hneg] with n hn hr
  letI : (selectedProbability hm hs X : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI : (selectedProbability hm hs (Xs n) : Measure (Xs n)).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs (Xs n)).1
  have hs' := ambientProjection_finrank_eq_realCutoff
    ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
    (selectedProbability hm hs (Xs n) : Measure (Xs n)) hf   (C.seq_isometry n) η hη hn.1 hn.2
  have hl := ambientProjection_finrank_eq_realCutoff
    ⟨C.limitMap, C.limit_isometry.continuous⟩
    (selectedProbability hm hs X : Measure X) hf   C.limit_isometry η hη hpos hneg
  exact hs'.symm.trans (hr.trans hl)

end PaperN.PartII.AmbientKernel
