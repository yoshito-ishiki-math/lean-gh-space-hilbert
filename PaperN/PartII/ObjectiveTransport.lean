import PaperN.PartII.ObjectiveLpNorm

namespace PaperN.PartII
open MeasureTheory
variable {X Z ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [MetricSpace Z] [CompactSpace Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype ι]

omit [CompactSpace X] [CompactSpace Z] in
/-- Isometric embedding and pushforward preserve the actual distance objective. -/
theorem distanceObjective_map_isometry (μ : ProbabilityMeasure X)
    (e : X → Z) (he : Isometry e) (q : ℝ) (hq : 0 ≤ q)
    (v : ι → C(Z, ℝ)) (x : X) (a : EuclideanSpace ℝ ι) :
    distanceObjective (μ.map e) q v (e x) a =
      distanceObjective μ q (fun i ↦ (v i).comp ⟨e, he.continuous⟩) x a := by
  unfold distanceObjective
  change (∫ z, |dist (e x) z - ∑ i, a i * v i z| ^ q ∂(Measure.map e (μ : Measure X))) = _
  rw [integral_map he.continuous.measurable.aemeasurable]
  · simp only [he.dist_eq, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  · apply Continuous.aestronglyMeasurable
    apply Continuous.rpow_const _ (fun _ ↦ Or.inr hq)
    exact ((continuous_const.dist continuous_id).sub
      (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (v i).continuous)).abs

omit [CompactSpace Z] in
/-- The intrinsic selected coefficient minimizes the ambient pushforward objective. -/
theorem coordinateLpMinimizer_mapped_objective_minimal (μ : ProbabilityMeasure X)
    (e : X → Z) (he : Isometry e) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : ι → C(Z, ℝ)) (x : X) (b : EuclideanSpace ℝ ι) :
    distanceObjective (μ.map e) p.toReal v (e x)
      (coordinateLpMinimizer (μ : Measure X) p
        (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x))) ≤
      distanceObjective (μ.map e) p.toReal v (e x) b := by
  rw [distanceObjective_map_isometry μ e he p.toReal ENNReal.toReal_nonneg,
    distanceObjective_map_isometry μ e he p.toReal ENNReal.toReal_nonneg]
  exact coordinateLpMinimizer_objective_minimal μ p hp _ x b

omit [CompactSpace Z] in
/-- Uniqueness uses full support on the source, not on the larger ambient space. -/
theorem mapped_distanceObjective_minimizer_eq (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (e : X → Z) (he : Isometry e) (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (v : ι → C(Z, ℝ))
    (hv : LinearIndependent ℝ (fun i ↦ (v i).comp ⟨e, he.continuous⟩))
    (x : X) (a : EuclideanSpace ℝ ι)
    (ha : ∀ b, distanceObjective (μ.map e)
      p.toReal v (e x) a ≤ distanceObjective
        (μ.map e) p.toReal v (e x) b) :
    a = coordinateLpMinimizer (μ : Measure X) p
      (fun i ↦ (v i).comp ⟨e, he.continuous⟩)
      (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)) := by
  apply distanceObjective_minimizer_eq μ p hp _ hv x a
  intro b
  simpa only [distanceObjective_map_isometry μ e he p.toReal ENNReal.toReal_nonneg]
    using ha b

end PaperN.PartII
