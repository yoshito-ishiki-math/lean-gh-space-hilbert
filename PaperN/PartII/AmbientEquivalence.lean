import PaperN.PartII.ComplexSymmetry

namespace PaperN.PartII.AmbientKernel
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem distance_maxGenEigenspace (a : ℂ) :
    Module.End.maxGenEigenspace (ComplexKernel.distanceOperator μ).toLinearMap a =
      Module.End.eigenspace (ComplexKernel.distanceOperator μ).toLinearMap a :=
  (ComplexKernel.distanceOperator_symmetric μ).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a

theorem distance_power_kernel (a : ℂ) (n : ℕ) (hn : 0 < n) :
    LinearMap.ker (((ComplexKernel.distanceOperator μ).toLinearMap - a • 1)^n) =
      LinearMap.ker ((ComplexKernel.distanceOperator μ).toLinearMap - a • 1) :=
  symmetric_power_kernel _ (ComplexKernel.distanceOperator_symmetric μ) a n hn

noncomputable def restrictionGeneralizedEquiv (he : Isometry e) (a : ℂ) (ha : a ≠ 0) :
    Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a ≃ₗ[ℂ]
      Module.End.maxGenEigenspace (ComplexKernel.distanceOperator μ).toLinearMap a := by
  have hc : (restriction e μ).toLinearMap.comp (distanceToContinuous e μ).toLinearMap =
      (ComplexKernel.distanceOperator μ).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (restriction_extension e μ he)
  let F := factorGeneralizedEigenspaceEquiv (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap (restriction_extension_symmetric e μ he) a ha
  exact {
    toFun := fun x ↦ ⟨restriction e μ x, by exact hc ▸ (F x).property⟩
    invFun := fun y ↦ ⟨a⁻¹ • distanceToContinuous e μ y, by
      have hy : (y : Lp ℂ 2 μ) ∈ Module.End.maxGenEigenspace
          ((restriction e μ).toLinearMap.comp (distanceToContinuous e μ).toLinearMap) a := by
        rw [hc]; exact y.property
      exact (F.symm ⟨y, hy⟩).property⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      have hx := x.property
      simp only [ambient_maxGenEigenspace e μ he a ha, Module.End.mem_eigenspace_iff] at hx
      change ambientOperator e μ x = a • (x : C(Z, ℂ)) at hx
      change a⁻¹ • ambientOperator e μ x = x
      rw [hx, smul_smul, inv_mul_cancel₀ ha, one_smul]
    right_inv := fun y ↦ by
      apply Subtype.ext
      have hy := y.property
      simp only [distance_maxGenEigenspace μ a, Module.End.mem_eigenspace_iff] at hy
      change ComplexKernel.distanceOperator μ y = a • (y : Lp ℂ 2 μ) at hy
      change restriction e μ (a⁻¹ • distanceToContinuous e μ y) = y
      rw [map_smul]
      change a⁻¹ • ((restriction e μ).comp (distanceToContinuous e μ)) y = y
      rw [restriction_extension e μ he, hy, smul_smul, inv_mul_cancel₀ ha, one_smul]
    map_add' := fun x y ↦ by apply Subtype.ext; exact map_add _ _ _
    map_smul' := fun c x ↦ by apply Subtype.ext; exact map_smul _ _ _ }

theorem restrictionGeneralizedEquiv_apply (he : Isometry e) (a : ℂ) (ha : a ≠ 0)
    (x : Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a) :
    (restrictionGeneralizedEquiv e μ he a ha x : Lp ℂ 2 μ) = restriction e μ x := rfl

theorem restrictionGeneralizedEquiv_symm_apply (he : Isometry e) (a : ℂ) (ha : a ≠ 0)
    (y : Module.End.maxGenEigenspace (ComplexKernel.distanceOperator μ).toLinearMap a) :
    ((restrictionGeneralizedEquiv e μ he a ha).symm y : C(Z, ℂ)) =
      a⁻¹ • distanceToContinuous e μ y := rfl

end PaperN.PartII.AmbientKernel
