import PaperN.PartII.SpectralCompetitors
import PaperN.PartII.BestApproximationError

namespace PaperN.PartII
variable {X ι : Type*} [MetricSpace X] [CompactSpace X] [Fintype ι]

omit [CompactSpace X] in
/-- Every function in a finite based subspace has Euclidean synthesis coefficients. -/
theorem exists_coordinateSynthesis_eq (S : Submodule ℝ C(X, ℝ))
    (b : Module.Basis ι ℝ S) (g : S) :
    ∃ a : EuclideanSpace ℝ ι, coordinateSynthesis (fun i ↦ (b i : C(X, ℝ))) a = g := by
  classical
  refine ⟨(WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm (fun i ↦ b.repr g i), ?_⟩
  change (∑ i, b.repr g i • (b i : C(X, ℝ))) = (g : C(X, ℝ))
  exact_mod_cast b.sum_repr g

theorem exists_uniform_coefficient_competitor (S : Submodule ℝ C(X, ℝ))
    (b : Module.Basis ι ℝ S) (ε : ℝ)
    (hε : (⨆ x : X, Metric.infDist (distanceProfile x) (S : Set C(X, ℝ))) < ε)
    (x : X) : ∃ a : EuclideanSpace ℝ ι,
      ‖distanceProfile x - coordinateSynthesis (fun i ↦ (b i : C(X, ℝ))) a‖ < ε := by
  obtain ⟨g, hg, he⟩ := exists_uniform_subspace_competitor S ε hε x
  obtain ⟨a, ha⟩ := exists_coordinateSynthesis_eq S b ⟨g, hg⟩
  exact ⟨a, by simpa only [ha] using he⟩

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory Metric Set
variable {X ι : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
  (p : ENNReal) [Fact (1 ≤ p)] [StrictConvexSpace ℝ (Lp ℝ p μ)]

theorem based_subspace_uniform_model_error (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    (S : Submodule ℝ C(X, ℝ)) (b : Module.Basis ι ℝ S)
    (hv : LinearIndependent ℝ (fun i ↦ (b i : C(X, ℝ))))
    (r : ℝ) (hr : 0 < r) (ε : ℝ)
    (hε : (⨆ x : X, infDist (distanceProfile x) (S : Set C(X, ℝ))) < ε) :
    (⨆ z : X × X, |(bestApproximationCoordinatePair μ p
      (fun i ↦ (b i : C(X, ℝ))) hv).pseudometric z.1 z.2 - dist z.1 z.2|) ≤
      2 * ε + diam (univ : Set X) *
        (1 - (⨅ z : X, μ.real (ball z r)) ^ (1 / p.toReal)) + 2*r := by
  apply bestApproximation_pseudometric_uniform_error μ p hp0 hp _ hv r hr ε
  intro x
  obtain ⟨a, ha⟩ := exists_uniform_coefficient_competitor S b ε hε x
  exact ⟨a, ha.le⟩

end PaperN.PartII
