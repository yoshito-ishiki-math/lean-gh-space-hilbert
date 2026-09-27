import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.InnerProductSpace.Semisimple

namespace PaperN.PartII
open Module
section Algebra
variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]
variable (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F)

/-- Restriction intertwines the shifted operators at every power. -/
theorem factor_shift_pow (a : 𝕜) (n : ℕ) (x : E) :
    ((B.comp A - a • 1)^n) (B x) = B (((A.comp B - a • 1)^n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [pow_succ', Module.End.mul_apply, ih]

/-- On the kernel of restriction, powers act by the scalar (-a)^n. -/
theorem factor_shift_pow_of_restrict_zero (a : 𝕜) (n : ℕ) (x : E) (hx : B x = 0) :
    ((A.comp B - a • 1)^n) x = (-a)^n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [pow_succ', Module.End.mul_apply, ih, hx, smul_smul, mul_comm]

/-- Restriction has zero kernel on every generalized eigenspace at a nonzero eigenvalue. -/
theorem factor_power_kernel_restrict_zero (a : 𝕜) (ha : a ≠ 0) (n : ℕ) (x : E)
    (hx : ((A.comp B - a • 1)^n) x = 0) (hB : B x = 0) : x = 0 := by
  rw [factor_shift_pow_of_restrict_zero A B a n x hB] at hx
  exact (smul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr ha))

/-- The ordinary nonzero eigenspaces are canonically isomorphic; the inverse is a⁻¹ A. -/
noncomputable def factorEigenspaceEquiv (a : 𝕜) (ha : a ≠ 0) :
    Module.End.eigenspace (A.comp B) a ≃ₗ[𝕜] Module.End.eigenspace (B.comp A) a where
  toFun x := ⟨B x, by
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    apply Module.End.mem_eigenspace_iff.mpr
    change B (A (B x)) = a • B x
    rw [← map_smul, ← hx]
    rfl⟩
  invFun y := ⟨a⁻¹ • A y, by
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    apply Module.End.mem_eigenspace_iff.mpr
    change A (B (a⁻¹ • A y)) = a • (a⁻¹ • A y)
    simp only [map_smul]
    change a⁻¹ • A ((B.comp A) y) = _
    rw [hy,map_smul,smul_smul,inv_mul_cancel₀ ha,one_smul,smul_smul,mul_inv_cancel₀ ha,one_smul]⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Module.End.mem_eigenspace_iff.mp x.property
    change a⁻¹ • (A.comp B) x = x
    rw [hx,smul_smul,inv_mul_cancel₀ ha,one_smul]
  right_inv y := by
    apply Subtype.ext
    have hy := Module.End.mem_eigenspace_iff.mp y.property
    change B (a⁻¹ • A y) = y
    rw [map_smul]
    change a⁻¹ • (B.comp A) y = y
    rw [hy,smul_smul,inv_mul_cancel₀ ha,one_smul]
  map_add' x y := by apply Subtype.ext; exact B.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact B.map_smul _ _
theorem factorEigenspaceEquiv_apply (a : 𝕜) (ha : a ≠ 0)
    (x : Module.End.eigenspace (A.comp B) a) :
    (factorEigenspaceEquiv A B a ha x : F) = B x := rfl

theorem factorEigenspaceEquiv_symm_apply (a : 𝕜) (ha : a ≠ 0)
    (y : Module.End.eigenspace (B.comp A) a) :
    ((factorEigenspaceEquiv A B a ha).symm y : E) = a⁻¹ • A y := rfl

/-- Stabilization of shifted power kernels transfers across the factorization
at every nonzero scalar. No compactness or dimension assumption is needed. -/
theorem factor_power_kernel_eq (a : 𝕜) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n)
    (hT : LinearMap.ker ((B.comp A - a • 1)^n) = LinearMap.ker (B.comp A - a • 1)) :
    LinearMap.ker ((A.comp B - a • 1)^n) = LinearMap.ker (A.comp B - a • 1) := by
  apply le_antisymm
  · intro x hx
    have hx0 : ((A.comp B - a • 1)^n) x = 0 := hx
    have hy : B x ∈ LinearMap.ker ((B.comp A - a • 1)^n) := by
      change ((B.comp A - a • 1)^n) (B x) = 0
      rw [factor_shift_pow A B a n x,hx0,map_zero]
    rw [hT] at hy
    have hB : B ((A.comp B - a • 1) x) = 0 := by
      have h := factor_shift_pow A B a 1 x
      simp only [pow_one] at h
      exact h.symm.trans hy
    have hz : ((A.comp B - a • 1)^n) ((A.comp B - a • 1) x) = 0 := by
      rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply,hx0,map_zero]
    exact factor_power_kernel_restrict_zero A B a ha n _ hz hB
  · intro x hx
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    change ((A.comp B - a • 1)^(k+1)) x = 0
    rw [pow_succ,Module.End.mul_apply,show (A.comp B - a • 1) x = 0 from hx,map_zero]
/-- Equality of nonzero eigenvalue sets under reversing the factors. -/
theorem factor_hasEigenvalue_iff (a : 𝕜) (ha : a ≠ 0) :
    Module.End.HasEigenvalue (A.comp B) a ↔ Module.End.HasEigenvalue (B.comp A) a := by
  simp only [Module.End.hasEigenvalue_iff, ← Submodule.nontrivial_iff_ne_bot]
  exact (factorEigenspaceEquiv A B a ha).toEquiv.nontrivial_congr

/-- Stabilization at every positive power identifies the maximal generalized eigenspace. -/
theorem factor_maxGenEigenspace_eq (a : 𝕜) (ha : a ≠ 0)
    (hT : ∀ n : ℕ, 0 < n →
      LinearMap.ker ((B.comp A - a • 1)^n) = LinearMap.ker (B.comp A - a • 1)) :
    Module.End.maxGenEigenspace (A.comp B) a = Module.End.eigenspace (A.comp B) a := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := Module.End.mem_genEigenspace_top.mp hx
    cases n with
    | zero =>
      have hx0 : x = 0 := by simpa using hn
      subst x
      exact Submodule.zero_mem _
    | succ n =>
      rw [factor_power_kernel_eq A B a ha (n+1) (by omega) (hT (n+1) (by omega))] at hn
      simpa only [Module.End.eigenspace_def] using hn
  · intro hx
    apply Module.End.mem_genEigenspace_top.mpr
    exact ⟨1,by simpa only [pow_one,Module.End.eigenspace_def] using hx⟩
end Algebra

section Symmetric
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A symmetric operator has no nontrivial generalized eigenvectors. -/
theorem symmetric_power_kernel (T : Module.End 𝕜 H) (hT : T.IsSymmetric)
    (a : 𝕜) (n : ℕ) (hn : 0 < n) :
    LinearMap.ker ((T - a • 1)^n) = LinearMap.ker (T - a • 1) := by
  have hn' : (0 : ℕ∞) < (n : ℕ∞) := by exact_mod_cast hn
  simpa only [Module.End.genEigenspace_nat, Module.End.eigenspace_def] using
    hT.isFinitelySemisimple.genEigenspace_eq_eigenspace a hn'

end Symmetric
end PaperN.PartII
