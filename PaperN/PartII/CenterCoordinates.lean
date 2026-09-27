import PaperN.PartII.CenterApproximation
import PaperN.PartII.ContinuousOrthonormalBasis

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

theorem exists_center_coordinates
    (hd : DistanceKernelSpectralInput.{u}) (hf : CompactEigenvalueFinitenessInput.{u})
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (τ : ℝ) (hτ : 0 < τ) :
    ∃ q η : ℝ, 2 ≤ q ∧ 0 < η ∧
      (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ∀ [Fact (1 ≤ ENNReal.ofReal q)] [StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) μ)],
        ∃ n : ℕ, ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
          n = Module.finrank ℝ (spectralCutoff μ η) ∧
          (Nontrivial X → 0 < n) ∧
          (∀ x : X, a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X)) ∧
          (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  obtain ⟨q, η, hq, hη, hp, hn, hfin, hdim, herr⟩ :=
    exists_center_approximation_parameters hd hf X μ τ hτ
  letI := hfin
  refine ⟨q, η, hq, hη, hp, hn, ?_⟩
  intro _ _
  obtain ⟨n, b, hnb, ho⟩ := exists_continuous_orthonormal_basis μ (spectralCutoff μ η)
  have hi : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ))) :=
    LinearIndependent.of_comp (continuousToL2 μ).toLinearMap ho.linearIndependent
  refine ⟨n, bestApproximationCoordinatePair μ (ENNReal.ofReal q) (fun i ↦ (b i : C(X, ℝ))) hi,
    hnb, ?_, ?_, herr n b hi⟩
  · intro ht
    rw [hnb]
    exact hdim ht
  · intro x
    exact coordinateLpMinimizer_norm_le_two_diam μ (ENNReal.ofReal q) (fun i ↦ (b i : C(X, ℝ))) x

end PaperN.PartII
