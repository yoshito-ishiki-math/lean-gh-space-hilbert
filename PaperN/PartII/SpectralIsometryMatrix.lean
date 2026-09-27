import PaperN.PartII.SpectralIsometryAction
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
  (hinv : ∀ g : X ≃ᵢ X, μ.map g = μ) (η : ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))

/-- Matrix of inverse pullback, with column j the coordinates of the image of basis vector j. -/
noncomputable def spectralIsometryMatrix (g : X ≃ᵢ X) : Matrix ι ι ℝ :=
  LinearMap.toMatrix b b (spectralIsometryAction μ hinv η g).toLinearMap

theorem spectralIsometryMatrix_apply (g : X ≃ᵢ X) (i j : ι) :
    spectralIsometryMatrix μ hinv η b g i j =
      b.repr (spectralIsometryAction μ hinv η g (b j)) i :=
  LinearMap.toMatrix_apply b b _ i j

theorem spectralIsometryMatrix_one : spectralIsometryMatrix μ hinv η b 1 = 1 := by
  simp [spectralIsometryMatrix]

theorem spectralIsometryMatrix_mul (g h : X ≃ᵢ X) :
    spectralIsometryMatrix μ hinv η b (g * h) =
      spectralIsometryMatrix μ hinv η b g * spectralIsometryMatrix μ hinv η b h := by
  simp only [spectralIsometryMatrix, map_mul]
  exact LinearMap.toMatrix_comp b b b _ _

/-- The matrix representation as a genuine monoid homomorphism. -/
noncomputable def spectralIsometryMatrixHom : (X ≃ᵢ X) →* Matrix ι ι ℝ where
  toFun := spectralIsometryMatrix μ hinv η b
  map_one' := spectralIsometryMatrix_one μ hinv η b
  map_mul' := spectralIsometryMatrix_mul μ hinv η b

theorem continuous_spectralIsometryMatrix : Continuous (spectralIsometryMatrix μ hinv η b) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simpa only [spectralIsometryMatrix_apply] using
    continuous_spectralIsometryAction_coefficient μ hinv η b i j

/-- The group inverse yields a two-sided inverse matrix, before choosing an orthonormal basis. -/
theorem spectralIsometryMatrix_inv_mul (g : X ≃ᵢ X) :
    spectralIsometryMatrix μ hinv η b g⁻¹ * spectralIsometryMatrix μ hinv η b g = 1 ∧
    spectralIsometryMatrix μ hinv η b g * spectralIsometryMatrix μ hinv η b g⁻¹ = 1 := by
  constructor <;> rw [← spectralIsometryMatrix_mul] <;> simp [spectralIsometryMatrix_one]

/-- The matrix reconstructs the transformed basis functions pointwise. -/
theorem spectralIsometryMatrix_basis_expansion (g : X ≃ᵢ X) (j : ι) (x : X) :
    ∑ i, spectralIsometryMatrix μ hinv η b g i j * (b i : C(X, ℝ)) x =
      (b j : C(X, ℝ)) (g.symm x) := by
  have he := congrArg (fun f : spectralCutoff (μ : Measure X) η ↦ (f : C(X, ℝ)) x)
    (b.sum_repr (spectralIsometryAction μ hinv η g (b j)))
  simp only [Submodule.coe_sum, Submodule.coe_smul, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul, spectralIsometryAction_apply] at he
  simpa only [spectralIsometryMatrix_apply] using he

end PaperN.PartII
