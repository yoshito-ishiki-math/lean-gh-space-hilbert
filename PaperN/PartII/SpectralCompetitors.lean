import PaperN.PartII.SelectedSpectralDensity
import PaperN.PartII.CoordinateLpNorm

namespace PaperN.PartII
open Metric Set MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Extract genuine competitors from the uniform distance-to-subspace estimate. -/
theorem exists_uniform_subspace_competitor (S : Submodule ℝ C(X, ℝ))
    (ε : ℝ) (hε : (⨆ x : X, infDist (distanceProfile x) (S : Set C(X, ℝ))) < ε)
    (x : X) : ∃ g ∈ S, ‖distanceProfile x - g‖ < ε := by
  have hb : BddAbove (range (fun x : X ↦ infDist (distanceProfile x) (S : Set C(X, ℝ)))) := by
    refine ⟨diam (univ : Set X), ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := infDist_le_dist_of_mem (x := distanceProfile y) S.zero_mem
    simp only [dist_zero_right] at h
    exact h.trans (distanceProfile_norm_le y)
  have h := (le_ciSup hb x).trans_lt hε
  obtain ⟨g, hg, hd⟩ := (infDist_lt_iff (show (S : Set C(X, ℝ)).Nonempty from ⟨0, S.zero_mem⟩)).mp h
  exact ⟨g, hg, by simpa only [dist_eq_norm] using hd⟩

end PaperN.PartII

namespace PaperN.PartII
open MeasureTheory
universe u

theorem exists_spectral_competitors
    (hd : DistanceKernelSpectralInput.{u}) (hf : CompactEigenvalueFinitenessInput.{u})
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ (η : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      ((-η : ℝ) : ℂ) ∉ complexifiedSpectrum (distanceOperator μ) ∧
      FiniteDimensional ℝ (spectralCutoff μ η) ∧
      (∀ x : X, ∃ g ∈ spectralCutoff μ η, ‖distanceProfile x - g‖ < ε) ∧
      (Nontrivial X → 0 < Module.finrank ℝ (spectralCutoff μ η)) := by
  obtain ⟨η, hη, hp, hn, hfin, he, hdim⟩ := spectralDensity_spec hd hf X μ ε hε
  exact ⟨η, hη, hp, hn, hfin,
    fun x ↦ exists_uniform_subspace_competitor (spectralCutoff μ η) ε he x, hdim⟩

end PaperN.PartII
