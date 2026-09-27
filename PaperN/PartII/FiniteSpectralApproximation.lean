import PaperN.PartII.SpectralSpan

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

/-- A single finite family of genuine nonzero-eigenvalue eigenfunctions approximates every profile. -/
theorem finite_eigenfunction_approximation
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset C(X, ℝ), (↑S : Set C(X, ℝ)) ⊆ continuousEigenvectors μ ∧
      ∀ x : X, ∃ g ∈ Submodule.span ℝ (S : Set C(X, ℝ)), ‖distanceProfile x - g‖ < ε := by
  classical
  obtain ⟨T,hT,hcover⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ : IsCompact (univ : Set X)).totallyBounded (ε/3) (by positivity)
  have hg (x : T) : ∃ g ∈ Submodule.span ℝ (continuousEigenvectors μ),
      dist (distanceProfile x.val) g < ε/3 := by
    have h := distanceProfile_mem_uniformSpectralSpan μ hc ha x.val
    exact Metric.mem_closure_iff.mp h (ε/3) (by positivity)
  choose g hgmem hgdist using hg
  letI := hT.to_subtype
  let F : Finset C(X, ℝ) := (Set.finite_range g).toFinset
  have hF : (F : Set C(X, ℝ)) ⊆ Submodule.span ℝ (continuousEigenvectors μ) := by
    intro f hf
    have hf' : f ∈ range g := by
      simpa [F] using hf
    obtain ⟨x,rfl⟩ := hf'
    exact hgmem x
  obtain ⟨S,hS,hFS⟩ := Submodule.subset_span_finite_of_subset_span hF
  refine ⟨S,hS,?_⟩
  intro x
  have hx := hcover (mem_univ x)
  simp only [mem_iUnion,mem_ball] at hx
  obtain ⟨y,hy,hd⟩ := hx
  refine ⟨g ⟨y,hy⟩, hFS ?_, ?_⟩
  · simpa [F] using (mem_range_self (f := g) ⟨y,hy⟩)
  · have ht := dist_triangle (distanceProfile x) (distanceProfile y) (g ⟨y,hy⟩)
    rw [distanceProfile_isometry.dist_eq] at ht
    have hg' := hgdist ⟨y,hy⟩
    rw [← dist_eq_norm]
    linarith

/-- The strict supremum-of-infima estimate, on one finite-dimensional eigenfunction span. -/
theorem finite_uniform_spectral_approximation [Nonempty X]
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset C(X, ℝ), (↑S : Set C(X, ℝ)) ⊆ continuousEigenvectors μ ∧
      (⨆ x : X, infDist (distanceProfile x) (Submodule.span ℝ (S : Set C(X, ℝ)))) < ε := by
  obtain ⟨S,hS,happrox⟩ := finite_eigenfunction_approximation μ hc ha (ε/2) (by positivity)
  refine ⟨S,hS,lt_of_le_of_lt ?_ (show ε/2 < ε by linarith)⟩
  apply ciSup_le
  intro x
  obtain ⟨g,hg,hd⟩ := happrox x
  exact (infDist_le_dist_of_mem hg).trans (by simpa [dist_eq_norm] using hd.le)

/-- On a space with two distinct points the approximating eigenspan can be nonzero. -/
theorem finite_spectral_approximation_positive_dim [Nontrivial X]
    (hc : IsCompactOperator (distanceOperator μ)) (ha : IsSelfAdjoint (distanceOperator μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset C(X, ℝ), (↑S : Set C(X, ℝ)) ⊆ continuousEigenvectors μ ∧
      0 < Module.finrank ℝ (Submodule.span ℝ (S : Set C(X, ℝ))) ∧
      ∀ x : X, ∃ g ∈ Submodule.span ℝ (S : Set C(X, ℝ)), ‖distanceProfile x - g‖ < ε := by
  obtain ⟨x,y,hxy⟩ := exists_pair_ne X
  have hd : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨S,hS,happrox⟩ := finite_eigenfunction_approximation μ hc ha
    (min ε (dist x y / 2)) (lt_min hε (by positivity))
  obtain ⟨g,hg,hclose⟩ := happrox x
  have hgne : g ≠ 0 := by
    intro hz
    rw [hz,sub_zero] at hclose
    have hn := (distanceProfile x).norm_coe_le_norm y
    change |dist x y| ≤ ‖distanceProfile x‖ at hn
    rw [abs_of_pos hd] at hn
    have hm := min_le_right ε (dist x y/2)
    linarith
  letI : Nontrivial (Submodule.span ℝ (S : Set C(X, ℝ))) :=
    nontrivial_of_ne (⟨g,hg⟩ : Submodule.span ℝ (S : Set C(X, ℝ))) 0
      (fun h ↦ hgne (congrArg Subtype.val h))
  refine ⟨S,hS,Module.finrank_pos_iff.mpr inferInstance,?_⟩
  intro z
  obtain ⟨g,hg,hgclose⟩ := happrox z
  exact ⟨g,hg,hgclose.trans_le (min_le_left _ _)⟩

theorem uniformSpectralSpan_spec : UniformSpectralSpanStatement.{u} := by
  intro X _ _ _ _ μ _ _ hc ha x
  exact distanceProfile_mem_uniformSpectralSpan μ hc ha x

theorem finiteEigenfunctionApproximation_spec : FiniteEigenfunctionApproximationStatement.{u} := by
  intro X _ _ _ _ _ μ _ _ hc ha ε hε
  exact finite_uniform_spectral_approximation μ hc ha ε hε
end PaperN.PartII
