import PaperN.PartI.ParameterIntegrals

namespace PaperN.PartII
open Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z]

theorem uniform_function_nearby_convergence (fs : ℕ → C(Z, ℝ)) (f : C(Z, ℝ))
    (hf : Tendsto fs atTop (𝓝 f)) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x y : Z, dist x y ≤ δ n → |fs n x - f y| < ε := by
  intro ε hε
  obtain ⟨r, hr, hcont⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous f.continuous)
    (ε / 2) (half_pos hε)
  filter_upwards [Metric.tendsto_nhds.mp hf (ε / 2) (half_pos hε),
    hδ.eventually (gt_mem_nhds hr)] with n hn hd
  intro x y hxy
  have ha : dist (fs n x) (f x) < ε / 2 :=
    (ContinuousMap.dist_apply_le_dist x).trans_lt hn
  have hb : dist (f x) (f y) < ε / 2 := hcont (hxy.trans_lt hd)
  have ht := (dist_triangle (fs n x) (f x) (f y)).trans_lt (add_lt_add ha hb)
  simpa only [Real.dist_eq, add_halves] using ht

theorem finite_family_nearby_convergence {ι : Type*} [Finite ι]
    (fs : ℕ → ι → C(Z, ℝ)) (f : ι → C(Z, ℝ))
    (hf : ∀ i, Tendsto (fun n ↦ fs n i) atTop (𝓝 (f i)))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i, ∀ x y : Z,
      dist x y ≤ δ n → |fs n i x - f i y| < ε := by
  intro ε hε
  exact Filter.eventually_all.mpr fun i ↦ uniform_function_nearby_convergence
    (fun n ↦ fs n i) (f i) (hf i) δ hδ ε hε

theorem nearby_family_sup_tendsto {ι : Type*} [Finite ι] [Nonempty ι]
    {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    (fs : ℕ → ι → C(Z, ℝ)) (f : ι → C(Z, ℝ))
    (hf : ∀ i, Tendsto (fun n ↦ fs n i) atTop (𝓝 (f i)))
    (x y : ∀ n, A n → Z) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hxy : ∀ n a, dist (x n a) (y n a) ≤ δ n) :
    Tendsto (fun n ↦ ⨆ p : ι × A n, |fs n p.1 (x n p.2) - f p.1 (y n p.2)|)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [finite_family_nearby_convergence fs f hf δ hδ (ε / 2) (half_pos hε)] with n hn
  have hb : BddAbove (Set.range (fun p : ι × A n ↦ |fs n p.1 (x n p.2) - f p.1 (y n p.2)|)) := by
    refine ⟨ε / 2, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact (hn p.1 _ _ (hxy n p.2)).le
  have hlo : 0 ≤ ⨆ p : ι × A n, |fs n p.1 (x n p.2) - f p.1 (y n p.2)| :=
    (abs_nonneg _).trans (le_ciSup hb (Classical.choice inferInstance))
  have hhi : (⨆ p : ι × A n, |fs n p.1 (x n p.2) - f p.1 (y n p.2)|) ≤ ε / 2 :=
    ciSup_le fun p ↦ (hn p.1 _ _ (hxy n p.2)).le
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hlo] using hhi.trans_lt (half_lt_self hε)

end PaperN.PartII
