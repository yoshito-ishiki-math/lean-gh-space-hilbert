import PaperN.PartII.OrthonormalCoordinateChange
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

namespace PaperN.PartII
open MeasureTheory
variable {X ι : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Fintype ι]
  (μ : Measure X) [IsProbabilityMeasure μ]

theorem continuous_toLp_norm_mono (p q : ENNReal) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (f : C(X, ℝ)) :
    ‖ContinuousMap.toLp p μ ℝ f‖ ≤ ‖ContinuousMap.toLp q μ ℝ f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
  rw [eLpNorm_congr_ae (ContinuousMap.coeFn_toLp μ f),
    eLpNorm_congr_ae (ContinuousMap.coeFn_toLp μ f)]
  exact eLpNorm_le_eLpNorm_of_exponent_le hpq

theorem coefficient_norm_le_coordinateLpNorm (p : ENNReal) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (S : Submodule ℝ (Lp ℝ 2 μ)) (b : OrthonormalBasis ι ℝ S)
    (v : ι → C(X, ℝ))
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ))
    (a : EuclideanSpace ℝ ι) : ‖a‖ ≤ coordinateLpNorm μ p v a := by
  have h := continuous_toLp_norm_mono μ 2 p hp (coordinateSynthesis v a)
  change ‖coordinateLpMap μ 2 v a‖ ≤ coordinateLpNorm μ p v a at h
  rw [synthesis_toLp_basis μ S b v hv] at h
  change ‖b.repr.symm a‖ ≤ _ at h
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem coordinateLpMinimizer_coefficient_norm_le_two_diam
    (p : ENNReal) [Fact (1 ≤ p)] (hp : 2 ≤ p)
    (S : Submodule ℝ (Lp ℝ 2 μ)) (b : OrthonormalBasis ι ℝ S)
    (v : ι → C(X, ℝ))
    (hv : ∀ i, ContinuousMap.toLp 2 μ ℝ (v i) = (b i : Lp ℝ 2 μ)) (x : X) :
    ‖coordinateLpMinimizer μ p v (ContinuousMap.toLp p μ ℝ (distanceProfile x))‖ ≤
      2 * Metric.diam (Set.univ : Set X) :=
  (coefficient_norm_le_coordinateLpNorm μ p hp S b v hv _).trans
    (coordinateLpMinimizer_norm_le_two_diam μ p v x)

end PaperN.PartII
