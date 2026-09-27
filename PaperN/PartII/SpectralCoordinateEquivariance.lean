import PaperN.PartII.SpectralCoordinateNorm
import PaperN.PartII.BestApproximationPullback

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : ProbabilityMeasure X) [(μ : Measure X).IsOpenPosMeasure]
  (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))

/-- Every coefficient vector has a preimage under the spectral matrix action. -/
theorem spectral_matrix_surjective (g : X ≃ᵢ X) :
    Function.Surjective (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g)) := by
  intro a
  refine ⟨Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g⁻¹) a, ?_⟩
  have h := congrArg (fun M : Matrix ι ι ℝ ↦ Matrix.toLpLin 2 2 M a)
    (spectralIsometryMatrix_inv_mul μ hinv η b g).2
  simpa only [Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    Matrix.toLpLin_one, LinearMap.id_apply] using h

/-- Simultaneously transporting the point and coefficients preserves the objective. -/
theorem spectral_distanceObjective (g : X ≃ᵢ X) (q : ℝ) (hq : 0 ≤ q)
    (x : X) (a : EuclideanSpace ℝ ι) :
    distanceObjective μ q (fun i ↦ (b i : C(X, ℝ))) (g x)
      (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) =
    distanceObjective μ q (fun i ↦ (b i : C(X, ℝ))) x a := by
  have h := distanceObjective_map_isometry μ g g.isometry q hq
    (fun i ↦ (b i : C(X, ℝ))) x
    (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a)
  rw [hinv g] at h
  rw [h]
  unfold distanceObjective
  apply integral_congr_ae
  filter_upwards [] with z
  have hs := congrArg (fun f : C(X, ℝ) ↦ f (g z))
    (spectral_coordinateSynthesis μ hinv η b g a)
  change (∑ i, (Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g) a) i •
    (b i : C(X, ℝ))) (g z) = (∑ i, a i • (b i : C(X, ℝ))) (g.symm (g z)) at hs
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    g.symm_apply_apply] at hs
  simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hs]

/-- Best-approximation coordinates transform by the very same spectral matrix. -/
theorem spectral_coordinateLpMinimizer (g : X ≃ᵢ X) (p : ENNReal) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))] (x : X) :
    coordinateLpMinimizer (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ)))
      (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile (g x))) =
    Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g)
      (coordinateLpMinimizer (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ)))
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x))) := by
  symm
  apply distanceObjective_minimizer_eq μ p hp _
    (b.linearIndependent.map' (spectralCutoff (μ : Measure X) η).subtype
      (Submodule.ker_subtype _)) (g x)
  intro c
  obtain ⟨a, rfl⟩ := spectral_matrix_surjective μ hinv η b g c
  simp only [Function.comp_def, Submodule.subtype_apply]
  rw [spectral_distanceObjective μ hinv η b g p.toReal ENNReal.toReal_nonneg,
    spectral_distanceObjective μ hinv η b g p.toReal ENNReal.toReal_nonneg]
  exact coordinateLpMinimizer_objective_minimal μ p hp _ x a

/-- The continuous coordinate map satisfies the manuscript equivariance identity. -/
theorem spectral_bestApproximationCoordinates (g : X ≃ᵢ X) (p : ENNReal) [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (hb : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ)))) (x : X) :
    bestApproximationCoordinates (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ))) hb (g x) =
    Matrix.toEuclideanLin (spectralIsometryMatrix μ hinv η b g)
      (bestApproximationCoordinates (μ : Measure X) p (fun i ↦ (b i : C(X, ℝ))) hb x) :=
  spectral_coordinateLpMinimizer μ hinv η b g p hp x

end PaperN.PartII
