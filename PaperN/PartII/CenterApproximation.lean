import PaperN.PartII.ApproximationParameters
import PaperN.PartII.CoefficientCompetitors

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

theorem exists_center_approximation_parameters
    (hd : DistanceKernelSpectralInput.{u}) (hf : CompactEigenvalueFinitenessInput.{u})
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (τ : ℝ) (hτ : 0 < τ) :
    ∃ q η : ℝ, 2 ≤ q ∧ 0 < η ∧
      (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      FiniteDimensional ℝ (spectralCutoff μ η) ∧
      (Nontrivial X → 0 < Module.finrank ℝ (spectralCutoff μ η)) ∧
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] [StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) μ)]
        (n : ℕ) (b : Module.Basis (Fin n) ℝ (spectralCutoff μ η))
        (hv : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ)))),
        (⨆ z : X × X, |(bestApproximationCoordinatePair μ (ENNReal.ofReal q)
          (fun i ↦ (b i : C(X, ℝ))) hv).pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  obtain ⟨r, q, ε, hr, hq, hε, herr⟩ := exists_local_error_parameters μ τ hτ
  obtain ⟨η, hη, hp, hn, hfin, he, hdim⟩ := spectralDensity_spec hd hf X μ ε hε
  refine ⟨q, η, hq, hη, hp, hn, hfin, hdim, ?_⟩
  intro _ _ n b hv
  have h := based_subspace_uniform_model_error μ (ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))) ENNReal.ofReal_ne_top
    (spectralCutoff μ η) b hv r hr ε he
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] at h
  exact h.trans_lt herr

end PaperN.PartII
