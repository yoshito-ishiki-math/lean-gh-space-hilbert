import PaperN.PartII.CenterResolventApproximation

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set PaperN.PartI GromovHausdorff

/-- Every non-singleton center has a positive-rank spectral neighborhood whose
local coordinate class approximates its metric to any prescribed accuracy. -/
theorem exists_approximating_spectral_neighborhood
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (X : MeasuredCompact.{0}) [Nontrivial X] (τ : ℝ) (hτ : 0 < τ) :
    ∃ q η : ℝ, 2 ≤ q ∧ ∃ hη : 0 < η, ∃ n : ℕ, 0 < n ∧
      ∃ B : SpectralModelNeighborhood hm hs X η n,
        ∃ hX : dist (toGHSpace X) (toGHSpace X) < B.radius,
        ∀ [Fact (1 ≤ ENNReal.ofReal q)]
          [StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) (selectedProbability hm hs X : Measure X))]
          (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n))),
          Quotient.mk _ a = B.coordinateClass hf hη X hX (ENNReal.ofReal q) →
          (∀ x : X, a.norm (a.coordinates x) ≤ 2 * diam (univ : Set X)) ∧
          (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|) < τ := by
  obtain ⟨q, η, hq, hη, hpos, hneg, n, hdim, hn, herr⟩ :=
    exists_center_class_approximation_resolvent hm hs hk hf X τ hτ
  obtain ⟨B⟩ := exists_spectralModelNeighborhood hm hp hs hg X   hf
    η hη hpos hneg n hdim
  have hX : dist (toGHSpace X) (toGHSpace X) < B.radius := by
    simpa only [dist_self] using B.radius_pos
  refine ⟨q, η, hq, hη, n, hn inferInstance, B, hX, ?_⟩
  intro _ _ a ha
  exact herr a ha

end PaperN.PartII.AmbientKernel
