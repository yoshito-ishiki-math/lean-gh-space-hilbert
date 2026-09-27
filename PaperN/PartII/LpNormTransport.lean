import PaperN.PartII.UniformLpNormConvergence

namespace PaperN.PartII
open MeasureTheory Filter Topology
variable {X Z ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

/-- Coordinate norms are preserved by continuous pushforward and restriction. -/
theorem coordinateLpNorm_map (μ : ProbabilityMeasure X) (e : C(X, Z))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : ι → C(Z, ℝ)) (a : EuclideanSpace ℝ ι) :
    coordinateLpNorm (μ.map e : Measure Z) p v a =
      coordinateLpNorm (μ : Measure X) p (fun i ↦ (v i).comp e) a := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  apply (Real.rpow_left_inj (norm_nonneg (coordinateLpMap _ p v a))
    (norm_nonneg (coordinateLpMap _ p (fun i ↦ (v i).comp e) a)) hp0.ne').mp
  change ‖ContinuousMap.toLp p _ ℝ (coordinateSynthesis v a)‖ ^ p.toReal =
    ‖ContinuousMap.toLp p _ ℝ (coordinateSynthesis (fun i ↦ (v i).comp e) a)‖ ^ p.toReal
  rw [continuous_toLp_norm_rpow _ p hp, continuous_toLp_norm_rpow _ p hp]
  change (∫ z, |coordinateSynthesis v a z| ^ p.toReal ∂(Measure.map e (μ : Measure X))) = _
  rw [integral_map e.continuous.measurable.aemeasurable]
  · simp [coordinateSynthesis, Fintype.linearCombination_apply]
  · exact ((coordinateSynthesis v a).continuous.abs.rpow_const
      (fun _ ↦ Or.inr ENNReal.toReal_nonneg)).aestronglyMeasurable

theorem intrinsic_coordinateLpNorm_uniform_on_compact
    (Xs : ℕ → Type*) [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)]
    [∀ n, MeasurableSpace (Xs n)] [∀ n, BorelSpace (Xs n)]
    (μs : ∀ n, ProbabilityMeasure (Xs n)) (μ : ProbabilityMeasure X)
    (es : ∀ n, C(Xs n, Z)) (e : C(X, Z))
    (hμ : Tendsto (fun n ↦ (μs n).map (es n))
      atTop (𝓝 (μ.map e)))
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) :
    TendstoUniformly
      (fun n (a : K) ↦ coordinateLpNorm (μs n : Measure (Xs n)) p
        (fun i ↦ (vs n i).comp (es n)) a)
      (fun a : K ↦ coordinateLpNorm (μ : Measure X) p
        (fun i ↦ (v i).comp e) a) atTop := by
  have h := coordinateLpNorm_uniform_on_compact _ _ hμ p hp vs v hv K hK
  simpa only [coordinateLpNorm_map _ _ p hp] using h

end PaperN.PartII
