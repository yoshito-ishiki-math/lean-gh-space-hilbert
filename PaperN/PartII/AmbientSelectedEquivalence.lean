import PaperN.PartII.FactorSelectedEigenspaces
import PaperN.PartII.ComplexCutoffFinite

namespace PaperN.PartII.AmbientKernel
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_map_selected (he : Isometry e) (s : Set ℂ) (hs : 0 ∉ s) :
    Submodule.map (restriction e μ).toLinearMap
      (selectedEigenspaces (ambientOperator e μ).toLinearMap s) =
      selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap s := by
  have hc : (restriction e μ).toLinearMap.comp (distanceToContinuous e μ).toLinearMap =
      (ComplexKernel.distanceOperator μ).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (restriction_extension e μ he)
  have hh := factor_map_selectedEigenspaces (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap s hs
  rw [hc] at hh
  exact hh

theorem restriction_selected_zero (s : Set ℂ) (hs : 0 ∉ s) (f : C(Z,ℂ))
    (hf : f ∈ selectedEigenspaces (ambientOperator e μ).toLinearMap s)
    (hr : restriction e μ f = 0) : f = 0 :=
  factor_selected_restrict_zero (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap s hs f hf hr

noncomputable def restrictionSelectedEquiv (he : Isometry e) (s : Set ℂ) (hs : 0 ∉ s) :
    selectedEigenspaces (ambientOperator e μ).toLinearMap s ≃ₗ[ℂ]
      selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap s := by
  let V := selectedEigenspaces (ambientOperator e μ).toLinearMap s
  let W := selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap s
  let R : V →ₗ[ℂ] W := ((restriction e μ).toLinearMap.domRestrict V).codRestrict W (by
    intro x
    change restriction e μ x ∈ selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap s
    rw [← restriction_map_selected e μ he s hs]
    exact ⟨x,x.property,rfl⟩)
  apply LinearEquiv.ofBijective R
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply restriction_selected_zero e μ s hs _ (V.sub_mem x.property y.property)
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
  · intro y
    have hy : (y : Lp ℂ 2 μ) ∈ selectedEigenspaces (ComplexKernel.distanceOperator μ).toLinearMap s := y.property
    rw [← restriction_map_selected e μ he s hs] at hy
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩

theorem restrictionSelectedEquiv_apply (he : Isometry e) (s : Set ℂ) (hs : 0 ∉ s)
    (f : selectedEigenspaces (ambientOperator e μ).toLinearMap s) :
    (restrictionSelectedEquiv e μ he s hs f : Lp ℂ 2 μ) = restriction e μ f := rfl

noncomputable abbrev ambientAlgebraicCutoff (η : ℝ) : Submodule ℂ C(Z,ℂ) :=
  selectedEigenspaces (ambientOperator e μ).toLinearMap {a | η < ‖a‖}

noncomputable def restrictionCutoffEquiv (he : Isometry e) (η : ℝ) (hη : 0 < η) :
    (ambientAlgebraicCutoff e μ η) ≃ₗ[ℂ]
      complexAlgebraicCutoff (ComplexKernel.distanceOperator μ) η :=
  restrictionSelectedEquiv e μ he {a | η < ‖a‖} (by simp [not_lt.mpr hη.le])

theorem restrictionCutoffEquiv_apply (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (f : ambientAlgebraicCutoff e μ η) :
    (restrictionCutoffEquiv e μ he η hη f : Lp ℂ 2 μ) = restriction e μ f := rfl

theorem ambientCutoff_finiteDimensional (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η : ℝ) (hη : 0 < η) :
    FiniteDimensional ℂ
      (ambientAlgebraicCutoff e μ η) := by
  letI finiteTarget := ComplexKernel.distance_complexAlgebraicCutoff_finiteDimensional μ hf η hη
  exact (restrictionCutoffEquiv e μ he η hη).symm.finiteDimensional
end PaperN.PartII.AmbientKernel
