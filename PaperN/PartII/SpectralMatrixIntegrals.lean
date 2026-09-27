import PaperN.PartII.SpectralIsometryMatrix
import Mathlib.LinearAlgebra.UnitaryGroup

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure] (η : ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))

/-- Integral orthonormality, with no choice of almost-everywhere representatives. -/
def SpectralBasisIntegralOrthonormal : Prop :=
  ∀ i j, (∫ x, (b i : C(X, ℝ)) x * (b j : C(X, ℝ)) x ∂(μ : Measure X)) =
    if i = j then 1 else 0

omit [(μ : Measure X).IsOpenPosMeasure] [Fintype ι] in
/-- Extract a finite-basis coefficient using the integral inner product. -/
theorem spectralBasis_coefficient_integral
    (hb : SpectralBasisIntegralOrthonormal μ η b)
    (f : spectralCutoff (μ : Measure X) η) (i : ι) :
    b.repr f i = ∫ x, (b i : C(X, ℝ)) x * (f : C(X, ℝ)) x ∂(μ : Measure X) := by
  have hint (f : spectralCutoff (μ : Measure X) η) :
      Integrable (fun x ↦ (b i : C(X, ℝ)) x * (f : C(X, ℝ)) x) (μ : Measure X) :=
    ((b i : C(X, ℝ)).continuous.mul (f : C(X, ℝ)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let L : spectralCutoff (μ : Measure X) η →ₗ[ℝ] ℝ := {
    toFun f := ∫ x, (b i : C(X, ℝ)) x * (f : C(X, ℝ)) x ∂(μ : Measure X)
    map_add' f h := by
      change (∫ x, (b i : C(X, ℝ)) x * ((f : C(X, ℝ)) x + (h : C(X, ℝ)) x)
        ∂(μ : Measure X)) = _
      simp_rw [mul_add]
      exact integral_add (hint f) (hint h)
    map_smul' a f := by
      change (∫ x, (b i : C(X, ℝ)) x * (a * (f : C(X, ℝ)) x) ∂(μ : Measure X)) =
        a * ∫ x, (b i : C(X, ℝ)) x * (f : C(X, ℝ)) x ∂(μ : Measure X)
      simp_rw [mul_left_comm ((b i : C(X, ℝ)) _) a]
      exact integral_const_mul _ _ }
  have hL : L = (Finsupp.lapply i).comp b.repr.toLinearMap := by
    apply b.ext
    intro j
    change (∫ x, (b i : C(X, ℝ)) x * (b j : C(X, ℝ)) x ∂(μ : Measure X)) = b.repr (b j) i
    rw [hb i j]
    simp [Finsupp.single_apply, eq_comm]
  exact (congrArg (fun T : spectralCutoff (μ : Measure X) η →ₗ[ℝ] ℝ ↦ T f) hL).symm

variable (hinv : ∀ g : X ≃ᵢ X, μ.map g = μ)

/-- The exact matrix-entry formula in eq:local-isometry-representation-2. -/
theorem spectralIsometryMatrix_integral
    (hb : SpectralBasisIntegralOrthonormal μ η b) (g : X ≃ᵢ X) (i j : ι) :
    spectralIsometryMatrix μ hinv η b g i j =
      ∫ x, (b i : C(X, ℝ)) (g x) * (b j : C(X, ℝ)) x ∂(μ : Measure X) := by
  rw [spectralIsometryMatrix_apply, spectralBasis_coefficient_integral μ η b hb]
  have he := spectralIsometryAction_integral_mul μ hinv η g
    (spectralIsometryAction μ hinv η g.symm (b i)) (b j)
  simpa only [spectralIsometryAction_apply, IsometryEquiv.symm_symm,
    IsometryEquiv.apply_symm_apply] using he

/-- For an integral-orthonormal basis, the inverse-group matrix is the transpose. -/
theorem spectralIsometryMatrix_inverse_transpose
    (hb : SpectralBasisIntegralOrthonormal μ η b) (g : X ≃ᵢ X) :
    spectralIsometryMatrix μ hinv η b g⁻¹ = (spectralIsometryMatrix μ hinv η b g).transpose := by
  ext i j
  rw [Matrix.transpose_apply, spectralIsometryMatrix_integral μ η b hinv hb,
    spectralIsometryMatrix_apply, spectralBasis_coefficient_integral μ η b hb]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [spectralIsometryAction_apply]
  exact mul_comm _ _

/-- Both orthogonality identities, including a zero-dimensional cutoff. -/
theorem spectralIsometryMatrix_orthogonal
    (hb : SpectralBasisIntegralOrthonormal μ η b) (g : X ≃ᵢ X) :
    (spectralIsometryMatrix μ hinv η b g).transpose * spectralIsometryMatrix μ hinv η b g = 1 ∧
    spectralIsometryMatrix μ hinv η b g * (spectralIsometryMatrix μ hinv η b g).transpose = 1 := by
  rw [← spectralIsometryMatrix_inverse_transpose μ η b hinv hb]
  exact spectralIsometryMatrix_inv_mul μ hinv η b g

/-- The manuscript's direct-composition basis transformation, with row i coefficients. -/
theorem spectralIsometryMatrix_direct_basis_expansion
    (hb : SpectralBasisIntegralOrthonormal μ η b) (g : X ≃ᵢ X) (i : ι) (x : X) :
    (b i : C(X, ℝ)) (g x) =
      ∑ j, spectralIsometryMatrix μ hinv η b g i j * (b j : C(X, ℝ)) x := by
  have he := spectralIsometryMatrix_basis_expansion μ hinv η b g⁻¹ i x
  rw [spectralIsometryMatrix_inverse_transpose μ η b hinv hb] at he
  exact he.symm

/-- The orthogonal-group-valued representation asserted in the local-model remark. -/
noncomputable def spectralOrthogonalRepresentation
    (hb : SpectralBasisIntegralOrthonormal μ η b) :
    (X ≃ᵢ X) →* Matrix.orthogonalGroup ι ℝ where
  toFun g := ⟨spectralIsometryMatrix μ hinv η b g,
    (Matrix.mem_orthogonalGroup_iff ι ℝ).mpr
      (spectralIsometryMatrix_orthogonal μ η b hinv hb g).2⟩
  map_one' := Subtype.ext (spectralIsometryMatrix_one μ hinv η b)
  map_mul' g h := Subtype.ext (spectralIsometryMatrix_mul μ hinv η b g h)

theorem continuous_spectralOrthogonalRepresentation
    (hb : SpectralBasisIntegralOrthonormal μ η b) :
    Continuous (spectralOrthogonalRepresentation μ η b hinv hb) :=
  (continuous_spectralIsometryMatrix μ hinv η b).subtype_mk _

end PaperN.PartII
