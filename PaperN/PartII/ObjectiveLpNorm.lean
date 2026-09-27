import PaperN.PartII.MovingDistanceObjective
import PaperN.PartII.CoefficientBound
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]

theorem continuous_toLp_norm_rpow (μ : Measure X) [IsFiniteMeasure μ]
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (f : C(X, ℝ)) :
    ‖ContinuousMap.toLp p μ ℝ f‖ ^ p.toReal = ∫ z, |f z| ^ p.toReal ∂μ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp μ f),
    toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hp f.continuous.aestronglyMeasurable]
  rw [Real.rpow_inv_rpow (integral_nonneg (fun z ↦ Real.rpow_nonneg (norm_nonneg _) _))
    (ENNReal.toReal_pos hp0 hp).ne']
  simp only [Real.norm_eq_abs]

theorem distanceObjective_eq_norm_rpow (μ : ProbabilityMeasure X)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : ι → C(X, ℝ)) (x : X) (a : EuclideanSpace ℝ ι) :
    distanceObjective μ p.toReal v x a =
      ‖ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x) -
        coordinateLpMap (μ : Measure X) p v a‖ ^ p.toReal := by
  change _ = ‖ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x) -
    ContinuousMap.toLp p (μ : Measure X) ℝ (coordinateSynthesis v a)‖ ^ p.toReal
  rw [← map_sub]
  symm
  convert continuous_toLp_norm_rpow (μ : Measure X) p hp
    (distanceProfile x - coordinateSynthesis v a) using 1
  simp [distanceObjective, distanceProfile, coordinateSynthesis, Fintype.linearCombination_apply]

theorem distanceObjective_le_iff_norm_le (μ : ProbabilityMeasure X)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : ι → C(X, ℝ)) (x : X) (a b : EuclideanSpace ℝ ι) :
    distanceObjective μ p.toReal v x a ≤ distanceObjective μ p.toReal v x b ↔
      ‖ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x) -
        coordinateLpMap (μ : Measure X) p v a‖ ≤
      ‖ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x) -
        coordinateLpMap (μ : Measure X) p v b‖ := by
  rw [distanceObjective_eq_norm_rpow μ p hp, distanceObjective_eq_norm_rpow μ p hp]
  exact Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _)
    (ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp)

theorem coordinateLpMinimizer_objective_minimal (μ : ProbabilityMeasure X)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (v : ι → C(X, ℝ)) (x : X) (b : EuclideanSpace ℝ ι) :
    distanceObjective μ p.toReal v x
      (coordinateLpMinimizer (μ : Measure X) p v
        (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x))) ≤
      distanceObjective μ p.toReal v x b :=
  (distanceObjective_le_iff_norm_le μ p hp v x _ b).mpr
    (coordinateLpMinimizer_spec (μ : Measure X) p v _ b)

theorem distanceObjective_minimizer_eq (μ : ProbabilityMeasure X)
    [(μ : Measure X).IsOpenPosMeasure]
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    [StrictConvexSpace ℝ (Lp ℝ p (μ : Measure X))]
    (v : ι → C(X, ℝ)) (hv : LinearIndependent ℝ v) (x : X)
    (a : EuclideanSpace ℝ ι)
    (ha : ∀ b, distanceObjective μ p.toReal v x a ≤ distanceObjective μ p.toReal v x b) :
    a = coordinateLpMinimizer (μ : Measure X) p v
      (ContinuousMap.toLp p (μ : Measure X) ℝ (distanceProfile x)) :=
  coordinateLp_minimizer_unique (μ : Measure X) p v hv _ a _
    (fun b ↦ (distanceObjective_le_iff_norm_le μ p hp v x a b).mp (ha b))
    (coordinateLpMinimizer_spec (μ : Measure X) p v _)

end PaperN.PartII
