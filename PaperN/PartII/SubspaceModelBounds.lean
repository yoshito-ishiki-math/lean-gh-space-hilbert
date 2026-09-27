import PaperN.PartII.LocalSpectralContinuity

namespace PaperN.PartII
open MeasureTheory Metric Set

/-- The class value bound holds for every finite continuous subspace. -/
theorem subspaceCoordinateClass_value_le_two_diam
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]
    (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]
    (n : ℕ) (hd : n = Module.finrank ℝ S) (x : X) :
    (subspaceCoordinateClass μ S p n hd).value x ≤ 2 * diam (univ : Set X) := by
  exact coordinateLpMinimizer_norm_le_two_diam μ p
    (fun i ↦ (subspaceOrthonormalBasis μ S n hd i : C(X, ℝ))) x

/-- The bound is a property of the class, so every representative satisfies it. -/
theorem subspaceCoordinateClass_representative_bound
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (S : Submodule ℝ C(X, ℝ)) [FiniteDimensional ℝ S]
    (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]
    (n : ℕ) (hd : n = Module.finrank ℝ S)
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)))
    (ha : Quotient.mk _ a = subspaceCoordinateClass μ S p n hd) (x : X) :
    a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X) := by
  have h := subspaceCoordinateClass_value_le_two_diam μ S p n hd x
  rw [← ha] at h
  exact h

namespace AmbientKernel.SpectralModelNeighborhood
open PaperN.PartI GromovHausdorff ComplexKernel

/-- All representatives of the local spectral class satisfy the model bound. -/
theorem representative_bound
    {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
    {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}
    (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (Y : MeasuredCompact.{0}) (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius)
    (p : ENNReal) [Fact (1 ≤ p)]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))]
    (a : NormedCoordinatePair Y (EuclideanSpace ℝ (Fin n)))
    (ha : Quotient.mk _ a = B.coordinateClass hf hη Y hY p) (x : Y) :
    a.norm (a.coordinates x) ≤ 2 * diam (univ : Set Y) := by
  let μ := selectedProbability hm hs Y
  letI : (μ : Measure Y).IsOpenPosMeasure :=
    openPos_of_support_eq_univ _ (selectedProbability_fullSupport_invariant hm hs Y).1
  letI := realCutoff_finiteDimensional (μ : Measure Y) hf η hη
  letI : FiniteDimensional ℝ (spectralCutoff (μ : Measure Y) η) :=
    (spectralCutoffEquiv (μ : Measure Y) hη).symm.finiteDimensional
  exact subspaceCoordinateClass_representative_bound (μ : Measure Y)
    (spectralCutoff (μ : Measure Y) η) p n (B.rank Y hY) a ha x

end AmbientKernel.SpectralModelNeighborhood
end PaperN.PartII
