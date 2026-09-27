import PaperN.PartII.FiniteSpectralApproximation

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The full algebraic cutoff span of continuous eigenfunctions. -/
noncomputable def spectralCutoff (η : ℝ) : Submodule ℝ C(X, ℝ) :=
  Submodule.span ℝ {g | ∃ a : ℝ, η < |a| ∧
    distanceOperator μ (continuousToL2 μ g) = a • continuousToL2 μ g}

theorem spectralCutoff_antitone {η θ : ℝ} (h : η ≤ θ) :
    spectralCutoff μ θ ≤ spectralCutoff μ η := by
  apply Submodule.span_mono
  rintro g ⟨a,ha,hg⟩
  exact ⟨a,h.trans_lt ha,hg⟩

/-- A finite eigenfunction family lies in all sufficiently small cutoffs. -/
theorem finite_eigenfunctions_le_cutoff (S : Finset C(X, ℝ))
    (hS : (S : Set C(X, ℝ)) ⊆ continuousEigenvectors μ) :
    ∃ δ > 0, ∀ η : ℝ, η < δ →
      Submodule.span ℝ (S : Set C(X, ℝ)) ≤ spectralCutoff μ η := by
  classical
  suffices ∃ δ > 0, ∀ g ∈ S, ∃ a : ℝ, δ ≤ |a| ∧
      distanceOperator μ (continuousToL2 μ g) = a • continuousToL2 μ g by
    obtain ⟨δ,hδ,h⟩ := this
    refine ⟨δ,hδ,fun η hη ↦ Submodule.span_le.mpr ?_⟩
    intro g hg
    obtain ⟨a,ha,he⟩ := h g hg
    exact Submodule.subset_span ⟨a,hη.trans_le ha,he⟩
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert g S hg ih =>
    obtain ⟨a,ha,he⟩ := hS (show g ∈ (↑(insert g S) : Set C(X, ℝ)) by simp)
    obtain ⟨δ,hδ,h⟩ := ih (fun f hf ↦ hS (by simp [hf]))
    refine ⟨min |a| δ,lt_min (abs_pos.mpr ha) hδ,?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact ⟨a,min_le_left _ _,he⟩
    · obtain ⟨b,hb,hbe⟩ := h f hf
      exact ⟨b,(min_le_right _ _).trans hb,hbe⟩

/-- Strict uniform approximation in every sufficiently small full cutoff space.
Spectrum avoidance and finite-dimensionality are separate conclusions. -/
theorem spectralCutoff_uniform_approximation [Nonempty X] [μ.IsOpenPosMeasure]
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ η : ℝ, η < δ →
      (⨆ x : X, infDist (distanceProfile x) (spectralCutoff μ η)) < ε := by
  obtain ⟨S,hS,happrox⟩ := finite_eigenfunction_approximation μ hc ha (ε/2) (by positivity)
  obtain ⟨δ,hδ,hcut⟩ := finite_eigenfunctions_le_cutoff μ S hS
  refine ⟨δ,hδ,fun η hη ↦ lt_of_le_of_lt (ciSup_le ?_) (show ε/2 < ε by linarith)⟩
  intro x
  obtain ⟨g,hg,hd⟩ := happrox x
  exact (infDist_le_dist_of_mem (hcut η hη hg)).trans (by simpa [dist_eq_norm] using hd.le)

/-- On a non-singleton space every sufficiently small cutoff contains a nonzero function.
No finite-dimensionality of the cutoff is assumed or claimed here. -/
theorem spectralCutoff_nonzero [Nontrivial X] [μ.IsOpenPosMeasure]
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ)) :
    ∃ δ > 0, ∀ η : ℝ, η < δ → ∃ g ∈ spectralCutoff μ η, g ≠ 0 := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨S,hS,happrox⟩ := finite_eigenfunction_approximation μ hc ha (dist x y / 2)
    (by positivity)
  obtain ⟨δ,hδ,hcut⟩ := finite_eigenfunctions_le_cutoff μ S hS
  obtain ⟨g,hg,hclose⟩ := happrox x
  refine ⟨δ,hδ,fun η hη ↦ ⟨g,hcut η hη hg,?_⟩⟩
  intro hz
  rw [hz,sub_zero] at hclose
  have hn := (distanceProfile x).norm_coe_le_norm y
  change |dist x y| ≤ ‖distanceProfile x‖ at hn
  rw [abs_of_pos hd] at hn
  linarith

end PaperN.PartII
