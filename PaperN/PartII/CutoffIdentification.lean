import PaperN.PartII.SpectralCutoff

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The full L² cutoff: the sum of all eigenspaces with absolute eigenvalue above η. -/
noncomputable def l2SpectralCutoff (η : ℝ) : Submodule ℝ (Lp ℝ 2 μ) :=
  ⨆ (a : ℝ) (_ : η < |a|), Module.End.eigenspace (distanceOperator μ).toLinearMap a

/-- Continuous representatives identify the entire cutoff, not only a finite chosen family. -/
theorem spectralCutoff_map_eq [μ.IsOpenPosMeasure] {η : ℝ} (hη : 0 < η) :
    (spectralCutoff μ η).map (continuousToL2 μ).toLinearMap = l2SpectralCutoff μ η := by
  apply le_antisymm
  · rw [spectralCutoff, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro f ⟨g,⟨a,ha,hg⟩,rfl⟩
    have hle : Module.End.eigenspace (distanceOperator μ).toLinearMap a ≤
        l2SpectralCutoff μ η := le_iSup_of_le a (le_iSup_of_le ha le_rfl)
    exact hle (Module.End.mem_eigenspace_iff.mpr hg)
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha f hf
    have hane : a ≠ 0 := abs_pos.mp (hη.trans ha)
    obtain ⟨g,hg,_⟩ := eigenfunction_continuousRepresentative μ f a hane
      (Module.End.mem_eigenspace_iff.mp hf)
    refine ⟨g,Submodule.subset_span ⟨a,ha,?_⟩,hg⟩
    rw [hg]
    exact Module.End.mem_eigenspace_iff.mp hf

/-- Canonical linear identification induced by sending a continuous function to its L² class. -/
noncomputable def spectralCutoffEquiv [μ.IsOpenPosMeasure] {η : ℝ} (hη : 0 < η) :
    spectralCutoff μ η ≃ₗ[ℝ] l2SpectralCutoff μ η :=
  ((spectralCutoff μ η).equivMapOfInjective (continuousToL2 μ).toLinearMap
    (continuousToL2_injective μ)).trans (LinearEquiv.ofEq _ _ (spectralCutoff_map_eq μ hη))

/-- Finiteness of the eigenvalue set suffices: individual eigenspace dimensions
are supplied by mathlib's compact-operator theorem. -/
theorem l2SpectralCutoff_finiteDimensional_of_finite
    (hc : IsCompactOperator (distanceOperator μ)) {η : ℝ} (hη : 0 < η)
    (hfin : Set.Finite {a : ℝ | η < |a| ∧
      Module.End.HasEigenvalue (distanceOperator μ).toLinearMap a}) :
    FiniteDimensional ℝ (l2SpectralCutoff μ η) := by
  classical
  let A := {a : ℝ | η < |a| ∧ Module.End.HasEigenvalue (distanceOperator μ).toLinearMap a}
  letI : Finite A := hfin.to_subtype
  let E (a : A) := Module.End.eigenspace (distanceOperator μ).toLinearMap a.val
  have heq : l2SpectralCutoff μ η = ⨆ a : A, E a := by
    apply le_antisymm
    · apply iSup_le
      intro a
      apply iSup_le
      intro ha
      by_cases he : Module.End.HasEigenvalue (distanceOperator μ).toLinearMap a
      · exact le_iSup E ⟨a,ha,he⟩
      · have hz : Module.End.eigenspace (distanceOperator μ).toLinearMap a = ⊥ :=
          not_ne_iff.mp he
        rw [hz]
        exact bot_le
    · apply iSup_le
      intro a
      exact le_iSup_of_le a.val (le_iSup_of_le a.property.1 le_rfl)
  letI (a : A) : FiniteDimensional ℝ (E a) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc a.val
      (abs_pos.mp (hη.trans a.property.1))
  rw [heq]
  infer_instance

theorem spectralCutoff_finiteDimensional_of_finite [μ.IsOpenPosMeasure]
    (hc : IsCompactOperator (distanceOperator μ)) {η : ℝ} (hη : 0 < η)
    (hfin : Set.Finite {a : ℝ | η < |a| ∧
      Module.End.HasEigenvalue (distanceOperator μ).toLinearMap a}) :
    FiniteDimensional ℝ (spectralCutoff μ η) := by
  letI := l2SpectralCutoff_finiteDimensional_of_finite μ hc hη hfin
  exact (spectralCutoffEquiv μ hη).symm.finiteDimensional

theorem spectralCutoff_finrank_eq [μ.IsOpenPosMeasure] {η : ℝ} (hη : 0 < η) :
    Module.finrank ℝ (spectralCutoff μ η) = Module.finrank ℝ (l2SpectralCutoff μ η) :=
  (spectralCutoffEquiv μ hη).finrank_eq

end PaperN.PartII
