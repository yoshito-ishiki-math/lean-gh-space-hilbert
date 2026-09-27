import PaperN.PartII.SpectralDensityStatements

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [Nonempty X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
variable [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

/-- Simultaneous cutoff choice for all conclusions, with no endpoint-avoidance input. -/
theorem spectral_density (hs : CompactEigenvalueFinitenessInput.{u})
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      FiniteDimensional ℝ (spectralCutoff μ η) ∧
      (⨆ x : X, infDist (distanceProfile x) (spectralCutoff μ η)) < ε ∧
      (Nontrivial X → 0 < Module.finrank ℝ (spectralCutoff μ η)) := by
  classical
  obtain ⟨δ,hδ,happrox⟩ := spectralCutoff_uniform_approximation μ hc ha ε hε
  by_cases hn : Nontrivial X
  · letI := hn
    obtain ⟨ρ,hρ,hdim⟩ := spectralCutoff_positive_finrank μ hs hc ha
    obtain ⟨η,hη,hbound,hplus,hminus⟩ := exists_complexified_spectral_gap hs
      (distanceOperator μ) hc ha (lt_min hδ hρ)
    exact ⟨η,hη,hplus,hminus,spectralCutoff_finiteDimensional μ hs hc ha hη,
      happrox η (hbound.trans_le (min_le_left _ _)),
      fun _ ↦ hdim η hη (hbound.trans_le (min_le_right _ _))⟩
  · obtain ⟨η,hη,hbound,hplus,hminus⟩ := exists_complexified_spectral_gap hs
      (distanceOperator μ) hc ha hδ
    exact ⟨η,hη,hplus,hminus,spectralCutoff_finiteDimensional μ hs hc ha hη,
      happrox η hbound,fun h ↦ (hn h).elim⟩

theorem spectralDensity_spec (hd : DistanceKernelSpectralInput.{u})
    (hs : CompactEigenvalueFinitenessInput.{u}) : SpectralDensityStatement.{u} := by
  intro X _ _ _ _ _ μ _ _ ε hε
  obtain ⟨hc,ha⟩ := hd X μ
  exact spectral_density μ hs hc ha ε hε
end PaperN.PartII
