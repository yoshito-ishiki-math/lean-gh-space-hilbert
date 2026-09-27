import PaperN.PartII.EmbeddedCoefficientConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology

/-- A finite initial segment cannot destroy boundedness of a norm-bounded tail. -/
theorem isBounded_range_of_eventually_norm_le {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (C : ℝ) (h : ∀ᶠ n in atTop, ‖u n‖ ≤ C) :
    Bornology.IsBounded (Set.range u) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max C (∑ k ∈ Finset.range N, ‖u k‖), ?_⟩
  rintro _ ⟨n, rfl⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    exact Finset.single_le_sum (fun k _ ↦ norm_nonneg (u k))
      (Finset.mem_range.mpr (Nat.lt_of_not_ge hn))

variable {Z X ι : Type*} (Xs : ℕ → Type*)
  [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
  [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)] [Fintype ι]

theorem embedded_eventually_orthonormal_coordinateLpMinimizer_tendsto
    (μs : ∀ n, ProbabilityMeasure (Xs n)) (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (es : ∀ n, Xs n → Z) (hes : ∀ n, Isometry (es n))
    (e : X → Z) (he : Isometry e)
    (hμ : Tendsto (fun n ↦ (μs n).map (es n))
      atTop (𝓝 (μ.map e)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (hli : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩))
    (xs : ∀ n, Xs n) (x : X) (hx : Tendsto (fun n ↦ es n (xs n)) atTop (𝓝 (e x)))
    (hp2 : 2 ≤ p)
    (hbasis : ∀ᶠ n in atTop, ∃ (S : Submodule ℝ (Lp ℝ 2 (μs n : Measure (Xs n))))
      (b : OrthonormalBasis ι ℝ S), ∀ i,
        ContinuousMap.toLp 2 (μs n : Measure (Xs n)) ℝ
          ((vs n i).comp ⟨es n, (hes n).continuous⟩) =
            (b i : Lp ℝ 2 (μs n : Measure (Xs n)))) :
    Tendsto (fun n ↦ coordinateLpMinimizer (μs n : Measure (Xs n)) p
      (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
      (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n)))) atTop
      (𝓝 (coordinateLpMinimizer (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)))) := by
  apply distanceObjective_minimizers_tendsto _ _ hμ p.toReal ENNReal.toReal_nonneg
    vs v hv _ _ hx _ _
    (by
      apply isBounded_range_of_eventually_norm_le _ (2 * Metric.diam (Set.univ : Set Z))
      filter_upwards [hbasis] with n hn
      obtain ⟨S, b, hb⟩ := hn
      apply (coordinateLpMinimizer_coefficient_norm_le_two_diam
        (μs n : Measure (Xs n)) p hp2 S b _ hb (xs n)).trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
      intro y _ z _
      rw [← (hes n).dist_eq]
      exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded
        (Set.mem_univ _) (Set.mem_univ _))
  · intro n b
    exact coordinateLpMinimizer_mapped_objective_minimal (μs n) (es n) (hes n) p hp
      (vs n) (xs n) b
  · intro a ha
    exact mapped_distanceObjective_minimizer_eq μ e he p hp v hli x a ha

end PaperN.PartII
