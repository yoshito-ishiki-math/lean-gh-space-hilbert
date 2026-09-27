import PaperN.PartII.CutoffDimension
import PaperN.PartII.CutoffProjectionConvergence

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v

/-- Properties of the actual contour integral, including its projection law. -/
def SpectralProjectionProperties {Z : Type v} [MetricSpace Z] [CompactSpace Z]
    (U P : C(Z, ℂ) →L[ℂ] C(Z, ℂ)) (η : ℝ) : Prop :=
  P.comp P = P ∧
  FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∧
  LinearMap.range P.toLinearMap =
    (⨆ a : ℂ, ⨆ (_ : a ∈ spectrum ℂ U), ⨆ (_ : η < ‖a‖),
      Module.End.maxGenEigenspace U.toLinearMap a) ∧
  iSupIndep (fun a : {a : ℂ // a ∈ spectrum ℂ U ∧ η < ‖a‖} ↦
    Module.End.maxGenEigenspace U.toLinearMap (a : ℂ)) ∧
  ∀ f : C(Z, ℝ), ∀ z : Z, (P (continuousRealEmbed f) z).im = 0

variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambient_cutoff_spectrum_iSup (he : Isometry e) (η : ℝ) (hη : 0 < η) :
    (⨆ a : ℂ, ⨆ (_ : η < ‖a‖), Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a) =
    (⨆ a : ℂ, ⨆ (_ : a ∈ spectrum ℂ (ambientOperator e μ)), ⨆ (_ : η < ‖a‖),
      Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a) := by
  apply le_antisymm
  · refine iSup_le fun a ↦ iSup_le fun ha ↦ ?_
    by_cases hs : a ∈ spectrum ℂ (ambientOperator e μ)
    · exact le_iSup_of_le a (le_iSup_of_le hs (le_iSup_of_le ha le_rfl))
    · have hn : a ≠ 0 := norm_pos_iff.mp (hη.trans ha)
      rw [ambient_maxGenEigenspace e μ he a hn]
      have hh := (ambientOperator_compact e μ).hasEigenvalue_iff_mem_spectrum hn
      have hz : Module.End.eigenspace (ambientOperator e μ).toLinearMap a = ⊥ := by
        by_contra h
        exact hs (hh.mp h)
      rw [hz]
      exact bot_le
  · exact iSup_le fun a ↦ iSup_le fun _ ↦ iSup_le fun ha ↦
      le_iSup_of_le a (le_iSup_of_le ha le_rfl)

theorem ambient_commonContour_properties
    (hf : CompactEigenvalueFinitenessInput.{u})
     (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    SpectralProjectionProperties (ambientOperator e μ)
      (cutoffContourOperator (ambientOperator e μ) (Metric.diam (Set.univ : Set Z)) η) η := by
  have hd : Metric.diam (Set.univ : Set X) ≤ Metric.diam (Set.univ : Set Z) := by
    rw [← he.diam_image (Set.univ : Set X)]
    exact Metric.diam_mono (Set.subset_univ _) isCompact_univ.isBounded
  have hc := ambient_cutoffContour_eq_circle_of_bound e μ he _ Metric.diam_nonneg hd η hη hp hn
  rw [hc]
  have ho := cutoffOuter_gt (Metric.diam (Set.univ : Set Z)) η Metric.diam_nonneg hη
  have hr := ambient_cutoffCircle_range e μ  he η _ hη ho.2 (hd.trans_lt ho.1) hp hn
  refine ⟨ambient_cutoffCircle_idempotent e μ  he η _ hη ho.2 (hd.trans_lt ho.1) hp hn, ?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact ambientCutoff_finiteDimensional e μ hf he η hη
  · rw [hr, ← ambient_cutoff_spectrum_iSup e μ he η hη,
      ambient_cutoff_generalized_eq e μ he η hη]
  · exact (Module.End.independent_maxGenEigenspace (ambientOperator e μ).toLinearMap).comp Subtype.val_injective
  · exact ambient_cutoffCircle_real_pointwise e μ hf  he η _ hη ho.2 (hd.trans_lt ho.1) hp hn

end PaperN.PartII.AmbientKernel

