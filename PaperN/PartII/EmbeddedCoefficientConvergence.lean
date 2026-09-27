import PaperN.PartII.ObjectiveTransport

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {Z X ι : Type*} (Xs : ℕ → Type*)
  [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
  [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)] [Fintype ι]

/-- Intrinsic selected coefficients converge through a common ambient realization.
Only the limiting intrinsic Lp space needs strict convexity. -/
theorem embedded_coordinateLpMinimizer_tendsto
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
    (hb : Bornology.IsBounded (Set.range (fun n ↦
      coordinateLpMinimizer (μs n : Measure (Xs n)) p
        (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
        (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n)))))) :
    Tendsto (fun n ↦ coordinateLpMinimizer (μs n : Measure (Xs n)) p
      (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
      (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n)))) atTop
      (𝓝 (coordinateLpMinimizer (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)))) := by
  apply distanceObjective_minimizers_tendsto _ _ hμ p.toReal ENNReal.toReal_nonneg
    vs v hv _ _ hx _ _ hb
  · intro n b
    exact coordinateLpMinimizer_mapped_objective_minimal (μs n) (es n) (hes n) p hp
      (vs n) (xs n) b
  · intro a ha
    exact mapped_distanceObjective_minimizer_eq μ e he p hp v hli x a ha

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- Orthonormal coordinates on embedded carriers are uniformly bounded by the
common compact ambient diameter, even though the carriers and measures vary. -/
theorem embedded_coordinateLpMinimizer_bounded
    (μs : ∀ n, ProbabilityMeasure (Xs n))
    (es : ∀ n, Xs n → Z) (hes : ∀ n, Isometry (es n))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (vs : ℕ → ι → C(Z, ℝ))
    (S : ∀ n, Submodule ℝ (Lp ℝ 2 (μs n : Measure (Xs n))))
    (b : ∀ n, OrthonormalBasis ι ℝ (S n))
    (hv : ∀ n i, ContinuousMap.toLp 2 (μs n : Measure (Xs n)) ℝ
      ((vs n i).comp ⟨es n, (hes n).continuous⟩) =
        (b n i : Lp ℝ 2 (μs n : Measure (Xs n))))
    (xs : ∀ n, Xs n) :
    Bornology.IsBounded (Set.range (fun n ↦
      coordinateLpMinimizer (μs n : Measure (Xs n)) p
        (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
        (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n))))) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨2 * Metric.diam (Set.univ : Set Z), ?_⟩
  rintro _ ⟨n, rfl⟩
  apply (coordinateLpMinimizer_coefficient_norm_le_two_diam
    (μs n : Measure (Xs n)) p hp (S n) (b n) _ (hv n) (xs n)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Metric.diam_le_of_forall_dist_le Metric.diam_nonneg
  intro y _ z _
  rw [← (hes n).dist_eq]
  exact Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _)

theorem embedded_orthonormal_coordinateLpMinimizer_tendsto
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
    (S : ∀ n, Submodule ℝ (Lp ℝ 2 (μs n : Measure (Xs n))))
    (b : ∀ n, OrthonormalBasis ι ℝ (S n))
    (hbasis : ∀ n i, ContinuousMap.toLp 2 (μs n : Measure (Xs n)) ℝ
      ((vs n i).comp ⟨es n, (hes n).continuous⟩) =
        (b n i : Lp ℝ 2 (μs n : Measure (Xs n)))) :
    Tendsto (fun n ↦ coordinateLpMinimizer (μs n : Measure (Xs n)) p
      (fun i ↦ (vs n i).comp ⟨es n, (hes n).continuous⟩)
      (ContinuousMap.toLp p (μs n : Measure (Xs n)) ℝ (distanceProfile (xs n)))) atTop
      (𝓝 (coordinateLpMinimizer (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)))) := by
  apply distanceObjective_minimizers_tendsto _ _ hμ p.toReal ENNReal.toReal_nonneg
    vs v hv _ _ hx _ _
    (embedded_coordinateLpMinimizer_bounded Xs μs es hes p hp2 vs S b hbasis xs)
  · intro n b
    exact coordinateLpMinimizer_mapped_objective_minimal (μs n) (es n) (hes n) p hp
      (vs n) (xs n) b
  · intro a ha
    exact mapped_distanceObjective_minimizer_eq μ e he p hp v hli x a ha

end PaperN.PartII
