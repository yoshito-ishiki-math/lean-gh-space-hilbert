import PaperN.PartII.MinimizerContinuity

namespace PaperN.PartII
open Filter Topology

/-- Compactness upgrades convergence along every related subsequence to uniform
comparison over a relation, even when the source types vary. -/
theorem uniform_relation_of_sequential
    {Y E : Type*} [MetricSpace Y] [CompactSpace Y] [MetricSpace E]
    (A : ℕ → Type*) (R : ∀ n, A n → Y → Prop)
    (fs : ∀ n, A n → E) (f : Y → E) (hf : Continuous f)
    (hseq : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ (xs : ∀ n, A (φ n)) (ys : ℕ → Y) (y : Y),
        (∀ n, R (φ n) (xs n) (ys n)) → Tendsto ys atTop (𝓝 y) →
        Tendsto (fun n ↦ fs (φ n) (xs n)) atTop (𝓝 (f y))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x y, R n x y → dist (fs n x) (f y) < ε := by
  classical
  intro ε hε
  by_contra hn
  have hbad : ∃ᶠ n in atTop, ∃ x y, R n x y ∧ ε ≤ dist (fs n x) (f y) := by
    apply (not_eventually.mp hn).mono
    intro n h
    push Not at h
    exact h
  obtain ⟨φ, hφ, hbadφ⟩ := extraction_of_frequently_atTop hbad
  choose xs ys hr hd using hbadφ
  obtain ⟨y, ψ, hψ, hy⟩ := CompactSpace.tendsto_subseq ys
  have ht := hseq (φ ∘ ψ) (hφ.tendsto_atTop.comp hψ.tendsto_atTop)
    (fun n ↦ xs (ψ n)) (ys ∘ ψ) y (fun n ↦ hr (ψ n)) hy
  have hz : Tendsto (fun n ↦ dist (fs (φ (ψ n)) (xs (ψ n))) (f (ys (ψ n))))
      atTop (𝓝 0) := by
    simpa using ht.dist (hf.continuousAt.tendsto.comp hy)
  have hle : ε ≤ (0 : ℝ) := le_of_tendsto_of_tendsto tendsto_const_nhds hz (Eventually.of_forall (fun n ↦ hd (ψ n)))
  exact (not_le_of_gt hε) hle

/-- Sequential convergence in a common ambient space gives uniform comparison
of all pairs whose ambient separation is bounded by a vanishing radius. -/
theorem uniform_nearby_of_sequential
    {Y Z E : Type*} [MetricSpace Y] [CompactSpace Y] [MetricSpace Z] [MetricSpace E]
    (A : ℕ → Type*) (es : ∀ n, A n → Z) (e : Y → Z) (he : Continuous e)
    (fs : ∀ n, A n → E) (f : Y → E) (hf : Continuous f)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (hseq : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ (xs : ∀ n, A (φ n)) (y : Y),
        Tendsto (fun n ↦ es (φ n) (xs n)) atTop (𝓝 (e y)) →
        Tendsto (fun n ↦ fs (φ n) (xs n)) atTop (𝓝 (f y))) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x y,
      dist (es n x) (e y) ≤ r n → dist (fs n x) (f y) < ε := by
  apply uniform_relation_of_sequential A (fun n x y ↦ dist (es n x) (e y) ≤ r n) fs f hf
  intro φ hφ xs ys y hrel hy
  apply hseq φ hφ xs y
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist := (he.continuousAt.tendsto.comp hy).dist (tendsto_const_nhds (x := e y))
  apply squeeze_zero (fun n ↦ dist_nonneg) _ (by simpa using (hr.comp hφ).add hdist)
  intro n
  exact (dist_triangle _ (e (ys n)) _).trans (add_le_add (hrel n) le_rfl)

end PaperN.PartII
