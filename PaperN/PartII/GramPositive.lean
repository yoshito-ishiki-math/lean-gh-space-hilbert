import PaperN.PartII.BasisTransform
import Mathlib.Analysis.Matrix.Order

namespace PaperN.PartII
open MeasureTheory Matrix
open scoped BigOperators
variable {Z ι : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
variable [Fintype ι]

omit [CompactSpace Z] [BorelSpace Z] [Fintype ι] in
theorem continuousGram_isHermitian (μ : ProbabilityMeasure Z) (v : ι → C(Z, ℝ)) :
    (continuousGram μ v).IsHermitian := by
  ext i j
  simp [continuousGram, mul_comm]

theorem continuousGram_quadratic (μ : ProbabilityMeasure Z) (v : ι → C(Z, ℝ))
    (x : ι → ℝ) :
    star x ⬝ᵥ (continuousGram μ v *ᵥ x) = ∫ z, (∑ i, x i * v i z) ^ 2 ∂(μ : Measure Z) := by
  classical
  have hi (i j : ι) : Integrable (fun z ↦ v i z * v j z) (μ : Measure Z) :=
    (BoundedContinuousFunction.mkOfCompact (v i * v j)).integrable _
  simp only [dotProduct, mulVec, continuousGram, Pi.star_apply, star_trivial,
    Finset.mul_sum, ← integral_const_mul, ← integral_mul_const]
  simp_rw [← integral_finsetSum _ (fun j _ ↦ ((hi _ j).mul_const (x j)).const_mul _)]
  rw [← integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦
    ((hi i j).mul_const (x j)).const_mul (x i)))]
  congr 1
  funext z
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem continuousGram_posSemidef (μ : ProbabilityMeasure Z) (v : ι → C(Z, ℝ)) :
    (continuousGram μ v).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (continuousGram_isHermitian μ v)
  intro x
  rw [continuousGram_quadratic μ v x]
  exact integral_nonneg fun z ↦ sq_nonneg _

open Filter
open scoped Topology

theorem continuousGram_eventually_posDef [DecidableEq ι]
    (μs : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μs atTop (𝓝 μ)) (vs : ℕ → ι → C(Z, ℝ)) (v : ι → C(Z, ℝ))
    (hv : ∀ i, Tendsto (fun n ↦ vs n i) atTop (𝓝 (v i)))
    (horth : continuousGram μ v = 1) :
    ∀ᶠ n in atTop, (continuousGram (μs n) (vs n)).PosDef := by
  filter_upwards [continuousGram_eventually_isUnit μs μ hμ vs v hv horth] with n hn
  exact (continuousGram_posSemidef (μs n) (vs n)).posDef_iff_isUnit.mpr hn

end PaperN.PartII
