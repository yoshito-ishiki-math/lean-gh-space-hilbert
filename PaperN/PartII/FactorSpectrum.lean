import PaperN.PartII.FactorEigenspaces
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

namespace PaperN.PartII
section Spectrum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable (A : F →L[ℂ] E) (B : E →L[ℂ] F)

/-- Fredholm plus the explicit eigenspace equivalence identifies nonzero spectra
of the two compact factorizations, even on different Banach spaces. -/
theorem factor_mem_spectrum_iff
    (hU : IsCompactOperator (A.comp B)) (hT : IsCompactOperator (B.comp A))
    (a : ℂ) (ha : a ≠ 0) : a ∈ spectrum ℂ (A.comp B) ↔ a ∈ spectrum ℂ (B.comp A) := by
  rw [← hU.hasEigenvalue_iff_mem_spectrum ha, ← hT.hasEigenvalue_iff_mem_spectrum ha]
  exact factor_hasEigenvalue_iff A.toLinearMap B.toLinearMap a ha

theorem factor_nonzero_spectrum_eq
    (hU : IsCompactOperator (A.comp B)) (hT : IsCompactOperator (B.comp A)) :
    spectrum ℂ (A.comp B) \ {0} = spectrum ℂ (B.comp A) \ {0} := by
  ext a
  simp only [Set.mem_sdiff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨h,ha⟩
    exact ⟨(factor_mem_spectrum_iff A B hU hT a ha).mp h,ha⟩
  · rintro ⟨h,ha⟩
    exact ⟨(factor_mem_spectrum_iff A B hU hT a ha).mpr h,ha⟩
end Spectrum

section Symmetric
variable {𝕜 E H : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable (A : H →ₗ[𝕜] E) (B : E →ₗ[𝕜] H)

/-- The algebraic stabilization needed for the ambient restriction-extension pair. -/
theorem factor_symmetric_power_kernel (hT : (B.comp A).IsSymmetric)
    (a : 𝕜) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    LinearMap.ker ((A.comp B - a • 1)^n) = LinearMap.ker (A.comp B - a • 1) :=
  factor_power_kernel_eq A B a ha n hn (symmetric_power_kernel _ hT a n hn)

theorem factor_symmetric_maxGenEigenspace (hT : (B.comp A).IsSymmetric)
    (a : 𝕜) (ha : a ≠ 0) :
    Module.End.maxGenEigenspace (A.comp B) a = Module.End.eigenspace (A.comp B) a :=
  factor_maxGenEigenspace_eq A B a ha (fun n hn ↦ symmetric_power_kernel _ hT a n hn)
/-- Restriction on maximal generalized eigenspaces, with inverse a⁻¹ A. -/
noncomputable def factorGeneralizedEigenspaceEquiv (hT : (B.comp A).IsSymmetric)
    (a : 𝕜) (ha : a ≠ 0) :
    Module.End.maxGenEigenspace (A.comp B) a ≃ₗ[𝕜] Module.End.maxGenEigenspace (B.comp A) a :=
  { toFun := fun x ↦ ⟨B x, by
      rw [hT.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a]
      exact (factorEigenspaceEquiv A B a ha
        ⟨x, by rw [← factor_symmetric_maxGenEigenspace A B hT a ha]; exact x.property⟩).property⟩
    invFun := fun y ↦ ⟨a⁻¹ • A y, by
      rw [factor_symmetric_maxGenEigenspace A B hT a ha]
      exact ((factorEigenspaceEquiv A B a ha).symm
        ⟨y, by rw [← hT.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a]; exact y.property⟩).property⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      have hx := x.property
      simp only [factor_symmetric_maxGenEigenspace A B hT a ha, Module.End.mem_eigenspace_iff] at hx
      change a⁻¹ • (A.comp B) x = x
      rw [hx,smul_smul,inv_mul_cancel₀ ha,one_smul]
    right_inv := fun y ↦ by
      apply Subtype.ext
      have hy := y.property
      simp only [hT.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a, Module.End.mem_eigenspace_iff] at hy
      change B (a⁻¹ • A y) = y
      rw [map_smul]
      change a⁻¹ • (B.comp A) y = y
      rw [hy,smul_smul,inv_mul_cancel₀ ha,one_smul]
    map_add' := fun x y ↦ by apply Subtype.ext; exact B.map_add _ _
    map_smul' := fun c x ↦ by apply Subtype.ext; exact B.map_smul _ _ }

theorem factorGeneralizedEigenspaceEquiv_apply (hT : (B.comp A).IsSymmetric)
    (a : 𝕜) (ha : a ≠ 0) (x : Module.End.maxGenEigenspace (A.comp B) a) :
    (factorGeneralizedEigenspaceEquiv A B hT a ha x : H) = B x := rfl

theorem factorGeneralizedEigenspaceEquiv_symm_apply (hT : (B.comp A).IsSymmetric)
    (a : 𝕜) (ha : a ≠ 0) (y : Module.End.maxGenEigenspace (B.comp A) a) :
    ((factorGeneralizedEigenspaceEquiv A B hT a ha).symm y : E) = a⁻¹ • A y := rfl
end Symmetric
end PaperN.PartII
