import PaperN.PartII.ModelFeatureSequence

namespace PaperN.PartII.AmbientKernel
open PaperN.PartI GromovHausdorff

/-- Every positive continuous error control admits a continuous approximation
through the concrete separable metric sphere-block orbit space. AR and homotopy
properties are deliberately separate conclusions, not assumptions here. -/
theorem exists_continuous_orbit_approximation
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (ε : GHSpace → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) :
    ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧
      ∃ f : GHSpace → SphereOrbit.Space n,
        Continuous f ∧ Continuous (SphereOrbit.realization n ∘ f) ∧
        (∀ q, dist q (SphereOrbit.realization n (f q)) < ε q / 2) := by
  obtain ⟨a, M, ρ, hρ, _, he⟩ := exists_localModel_partition hm hp hs hg hk   hf   ε hε hpos
  have hc := continuous_modelApproximation M ρ hρ hg
  exact ⟨fun i ↦ (M i).dimension, fun i ↦ (M i).dimension_pos,
    modelApproximation M ρ, hc, (SphereOrbit.realization_lipschitz _).continuous.comp hc,
    modelApproximation_realization_dist_lt M ρ hρ ε he⟩

end PaperN.PartII.AmbientKernel
