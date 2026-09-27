import PaperN.PartII.ChosenSpectralRepresentation
import PaperN.PartII.LpNormTransport

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
  (hinv : ∀ g : X ≃ᵢ X, μ.map g = μ) (η : ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))

/-- Synthesis intertwines the matrix action and inverse pullback of functions. -/
theorem spectral_coordinateSynthesis (g : X ≃ᵢ X) (a : EuclideanSpace ℝ ι) :
    coordinateSynthesis (fun i ↦ (b i : C(X, ℝ)))
      (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) =
    (coordinateSynthesis (fun i ↦ (b i : C(X, ℝ))) a).comp ⟨g.symm, g.symm.continuous⟩ := by
  ext x
  change (∑ i, (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) i •
    (b i : C(X, ℝ))) x = (∑ i, a i • (b i : C(X, ℝ))) (g.symm x)
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  change (∑ i, (∑ j, spectralIsometryMatrix μ hinv η b g i j * a j) *
    (b i : C(X, ℝ)) x) = ∑ j, a j * (b j : C(X, ℝ)) (g.symm x)
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = a j * ∑ i, spectralIsometryMatrix μ hinv η b g i j * (b i : C(X, ℝ)) x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [spectralIsometryMatrix_basis_expansion]

/-- The coordinate Lp norm is invariant under the same representation matrix. -/
theorem spectral_coordinateLpNorm (g : X ≃ᵢ X) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (a : EuclideanSpace ℝ ι) :
    coordinateLpNorm (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ)))
      (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) =
    coordinateLpNorm (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ))) a := by
  have hn := coordinateLpNorm_map μ (⟨g.symm, g.symm.continuous⟩ : C(X, X)) p hp
    (fun i ↦ (b i : C(X, ℝ))) a
  erw [hinv g.symm] at hn
  rw [hn]
  change ‖ContinuousMap.toLp p _ ℝ (coordinateSynthesis _ _)‖ =
    ‖ContinuousMap.toLp p _ ℝ (coordinateSynthesis _ _)‖
  congr 2
  rw [spectral_coordinateSynthesis]
  ext x
  change (∑ i, a i • (b i : C(X, ℝ))) (g.symm x) =
    (∑ i, a i • ((b i : C(X, ℝ)).comp ⟨g.symm, g.symm.continuous⟩)) x
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, ContinuousMap.comp_apply]
  rfl

end PaperN.PartII
