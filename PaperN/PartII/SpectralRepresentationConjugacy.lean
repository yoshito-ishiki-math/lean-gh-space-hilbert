import PaperN.PartII.SpectralCoordinateEquivariance
import PaperN.PartII.OrthonormalCoordinateChange

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
  (hinv : ∀ g : X ≃ᵢ X, μ.map g = μ) (η : ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b c : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))

/-- The transition matrix sends b-coordinates to c-coordinates. -/
noncomputable def spectralBasisTransition : Matrix ι ι ℝ :=
  LinearMap.toMatrix b c LinearMap.id

omit [(μ : Measure X).IsOpenPosMeasure] in
/-- Reversing the bases gives the two-sided inverse transition matrix. -/
theorem spectralBasisTransition_inverse :
    spectralBasisTransition μ η b c * spectralBasisTransition μ η c b = 1 ∧
    spectralBasisTransition μ η c b * spectralBasisTransition μ η b c = 1 := by
  constructor
  · rw [spectralBasisTransition, spectralBasisTransition, ← LinearMap.toMatrix_comp]
    simp
  · rw [spectralBasisTransition, spectralBasisTransition, ← LinearMap.toMatrix_comp]
    simp

/-- Changing coordinates conjugates the spectral matrix representation. -/
theorem spectralIsometryMatrix_conjugacy (g : X ≃ᵢ X) :
    spectralIsometryMatrix μ hinv η c g =
      spectralBasisTransition μ η b c * spectralIsometryMatrix μ hinv η b g *
        spectralBasisTransition μ η c b := by
  unfold spectralIsometryMatrix spectralBasisTransition
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  simp

/-- Any synthesis-compatible orthogonal coordinate change intertwines the actions. -/
theorem spectral_coordinateChange_intertwines
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateSynthesis (fun i ↦ (c i : C(X, ℝ))) (O a) =
      coordinateSynthesis (fun i ↦ (b i : C(X, ℝ))) a)
    (g : X ≃ᵢ X) (a : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η c g) (O a) =
      O (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) := by
  apply coordinateSynthesis_injective (fun i ↦ (c i : C(X, ℝ)))
    (c.linearIndependent.map' (spectralCutoff (μ : Measure X) η).subtype
      (Submodule.ker_subtype _))
  rw [spectral_coordinateSynthesis, hO, hO, spectral_coordinateSynthesis]

/-- In the new coordinates the action is O M(g) O inverse. -/
theorem spectral_coordinateChange_conjugacy
    (O : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hO : ∀ a, coordinateSynthesis (fun i ↦ (c i : C(X, ℝ))) (O a) =
      coordinateSynthesis (fun i ↦ (b i : C(X, ℝ))) a)
    (g : X ≃ᵢ X) (a : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η c g) a =
      O (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) (O.symm a)) := by
  simpa only [O.apply_symm_apply] using
    spectral_coordinateChange_intertwines μ hinv η b c O hO g (O.symm a)

/-- The existing orthonormal basis-change construction satisfies conjugacy. -/
theorem spectral_orthonormalCoordinateChange_conjugacy
    (S : Submodule ℝ (Lp ℝ 2 (μ : Measure X)))
    (d e : OrthonormalBasis ι ℝ S)
    (hd : ∀ i, ContinuousMap.toLp 2 (μ : Measure X) ℝ (b i) = (d i : Lp ℝ 2 (μ : Measure X)))
    (he : ∀ i, ContinuousMap.toLp 2 (μ : Measure X) ℝ (c i) = (e i : Lp ℝ 2 (μ : Measure X)))
    (g : X ≃ᵢ X) (a : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η c g) a =
      orthonormalCoordinateChange (μ : Measure X) S d e
        (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g)
          ((orthonormalCoordinateChange (μ : Measure X) S d e).symm a)) :=
  spectral_coordinateChange_conjugacy μ hinv η b c _
    (coordinateSynthesis_change_basis (μ : Measure X) S d e _ _ hd he) g a

end PaperN.PartII
