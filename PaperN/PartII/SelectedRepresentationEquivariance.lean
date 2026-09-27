import PaperN.PartII.SpectralRepresentationConjugacy
import PaperN.PartII.ZeroCoordinateClass

namespace PaperN.PartII.AmbientKernel
open MeasureTheory PaperN.PartI

/-- The actual selected spectral coordinate class admits a representative carrying
its integral orthogonal representation, coordinate equivariance and invariant norm. -/
theorem selected_spectral_equivariant_representative
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hf : CompactEigenvalueFinitenessInput.{0}) (X : MeasuredCompact.{0})
    (η : ℝ) (hη : 0 < η) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    (n : ℕ)
    (hn : n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η)) :
    ∃ b : Module.Basis (Fin n) ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η),
      Orthonormal ℝ (fun i ↦ continuousToL2 (selectedProbability hm hs X : Measure X) (b i)) ∧
      ∃ A : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
        (Quotient.mk _ A : NormedCoordinateClass X (EuclideanSpace ℝ (Fin n))) =
          selectedSpectralCoordinateClass hm hs hf X η hη p n hn ∧
        ∃ ρ : (X ≃ᵢ X) →* Matrix.orthogonalGroup (Fin n) ℝ,
          Continuous ρ ∧
          (∀ g i j, (ρ g : Matrix (Fin n) (Fin n) ℝ) i j =
            ∫ x, (b i : C(X, ℝ)) (g x) * (b j : C(X, ℝ)) x
              ∂(selectedProbability hm hs X : Measure X)) ∧
          (∀ g x, A.coordinates (g x) = Matrix.toEuclideanLin (ρ g : Matrix _ _ ℝ)
            (A.coordinates x)) ∧
          (∀ g a, A.norm (Matrix.toEuclideanLin (ρ g : Matrix _ _ ℝ) a) = A.norm a) := by
  let μ := selectedProbability hm hs X
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI := ComplexKernel.realCutoff_finiteDimensional (μ : Measure X) hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η) :=
    (spectralCutoffEquiv (μ : Measure X) hη).symm.finiteDimensional
  let b := subspaceOrthonormalBasis (μ : Measure X) (spectralCutoff (μ : Measure X) η) n hn
  have hb := chosenSpectralBasis_integralOrthonormal μ η n hn
  have ho := subspaceOrthonormalBasis_orthonormal (μ : Measure X)
    (spectralCutoff (μ : Measure X) η) n hn
  have hli : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ))) :=
    LinearIndependent.of_comp (continuousToL2 (μ : Measure X)).toLinearMap ho.linearIndependent
  have hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ :=
    fun g ↦ selectedProbability_natural hm hs X X g
  refine ⟨b, ho, bestApproximationCoordinatePair (μ : Measure X) p _ hli, rfl,
    spectralOrthogonalRepresentation μ η b hinv hb,
    continuous_spectralOrthogonalRepresentation μ η b hinv hb, ?_, ?_, ?_⟩
  · exact fun g i j ↦ spectralIsometryMatrix_integral μ η b hinv hb g i j
  · exact fun g x ↦ spectral_bestApproximationCoordinates μ hinv η b g p hp hli x
  · exact fun g a ↦ spectral_coordinateLpNorm μ hinv η b g p hp a

end PaperN.PartII.AmbientKernel

namespace PaperN.PartII

/-- The constant model used throughout the singleton neighborhood carries the
trivial continuous one-dimensional orthogonal representation on every carrier. -/
theorem zeroCoordinateClass_equivariant_representative
    (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ A : NormedCoordinatePair X (EuclideanSpace ℝ (Fin 1)),
      (Quotient.mk _ A : NormedCoordinateClass X (EuclideanSpace ℝ (Fin 1))) =
        zeroCoordinateClass X ∧
      ∃ ρ : (X ≃ᵢ X) →* Matrix.orthogonalGroup (Fin 1) ℝ,
        Continuous ρ ∧ (∀ g, ρ g = 1) ∧
        (∀ g x, A.coordinates (g x) =
          Matrix.toEuclideanLin (ρ g : Matrix _ _ ℝ) (A.coordinates x)) ∧
        (∀ g a, A.norm (Matrix.toEuclideanLin (ρ g : Matrix _ _ ℝ) a) = A.norm a) := by
  refine ⟨zeroCoordinatePair X, rfl, 1, continuous_const, fun _ ↦ rfl, ?_, ?_⟩
  · intro g x
    change (0 : EuclideanSpace ℝ (Fin 1)) = Matrix.toLpLin 2 2 1 0
    simp
  · intro g a
    change (zeroCoordinatePair X).norm (Matrix.toLpLin 2 2 (1 : Matrix (Fin 1) (Fin 1) ℝ) a) = _
    simp

end PaperN.PartII
