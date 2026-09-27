import PaperN.PartII.SpectralMatrixIntegrals
import PaperN.PartII.GramRestriction

namespace PaperN.PartII
open MeasureTheory PaperN.PartI
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- L2 orthonormality of continuous representatives is exactly the integral condition. -/
theorem spectralBasis_integralOrthonormal_of_L2 (μ : ProbabilityMeasure X) (η : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (spectralCutoff (μ : Measure X) η))
    (hb : Orthonormal ℝ (fun i ↦ continuousToL2 (μ : Measure X) (b i))) :
    SpectralBasisIntegralOrthonormal μ η b := by
  rw [orthonormal_iff_ite] at hb
  intro i j
  simpa only [continuousToL2_inner] using hb i j

/-- The exact chosen basis used by subspaceCoordinateClass satisfies integral orthonormality. -/
theorem chosenSpectralBasis_integralOrthonormal (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure] (η : ℝ)
    [FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η)]
    (n : ℕ) (hn : n = Module.finrank ℝ (spectralCutoff (μ : Measure X) η)) :
    SpectralBasisIntegralOrthonormal μ η
      (subspaceOrthonormalBasis (μ : Measure X) (spectralCutoff (μ : Measure X) η) n hn) :=
  spectralBasis_integralOrthonormal_of_L2 μ η _
    (subspaceOrthonormalBasis_orthonormal (μ : Measure X) _ n hn)

/-- The representation using precisely the basis chosen for the coordinate class. -/
noncomputable def chosenSpectralRepresentation (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    [FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η)]
    (n : ℕ) (hn : n = Module.finrank ℝ (spectralCutoff (μ : Measure X) η)) :
    (X ≃ᵢ X) →* Matrix.orthogonalGroup (Fin n) ℝ :=
  spectralOrthogonalRepresentation μ η
    (subspaceOrthonormalBasis (μ : Measure X) _ n hn) hinv
    (chosenSpectralBasis_integralOrthonormal μ η n hn)

theorem continuous_chosenSpectralRepresentation (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ) (η : ℝ)
    [FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η)]
    (n : ℕ) (hn : n = Module.finrank ℝ (spectralCutoff (μ : Measure X) η)) :
    Continuous (chosenSpectralRepresentation μ hinv η n hn) :=
  continuous_spectralOrthogonalRepresentation μ η _ hinv _

namespace AmbientKernel

/-- Actual selected-measure spectral basis and continuous orthogonal representation.
The existing compact spectral finiteness input discharges finite dimensionality. -/
theorem selected_exists_orthogonalRepresentation
    (hm : GHPMetricInput.{0}) (hs : InvariantFiberLawSelectionStatement hm)
    (hf : CompactEigenvalueFinitenessInput.{0}) (X : MeasuredCompact.{0})
    (η : ℝ) (hη : 0 < η) (n : ℕ)
    (hn : n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η)) :
    ∃ b : Module.Basis (Fin n) ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η),
      Orthonormal ℝ (fun i ↦ continuousToL2 (selectedProbability hm hs X : Measure X) (b i)) ∧
      ∃ ρ : (X ≃ᵢ X) →* Matrix.orthogonalGroup (Fin n) ℝ,
        Continuous ρ ∧ ∀ g i j,
          (ρ g : Matrix (Fin n) (Fin n) ℝ) i j =
            ∫ x, (b i : C(X, ℝ)) (g x) * (b j : C(X, ℝ)) x
              ∂(selectedProbability hm hs X : Measure X) := by
  let μ := selectedProbability hm hs X
  letI : (μ : Measure X).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs X).1
  letI := ComplexKernel.realCutoff_finiteDimensional (μ : Measure X) hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff (μ : Measure X) η) :=
    (spectralCutoffEquiv (μ : Measure X) hη).symm.finiteDimensional
  let b := subspaceOrthonormalBasis (μ : Measure X) (spectralCutoff (μ : Measure X) η) n hn
  have hb := chosenSpectralBasis_integralOrthonormal μ η n hn
  have hinv : ∀ g : X ≃ᵢ X, μ.map g.continuous.measurable.aemeasurable = μ :=
    fun g ↦ selectedProbability_natural hm hs X X g
  refine ⟨b, subspaceOrthonormalBasis_orthonormal (μ : Measure X) _ n hn,
    spectralOrthogonalRepresentation μ η b hinv hb,
    continuous_spectralOrthogonalRepresentation μ η b hinv hb, ?_⟩
  intro g i j
  exact spectralIsometryMatrix_integral μ η b hinv hb g i j

end AmbientKernel
end PaperN.PartII
