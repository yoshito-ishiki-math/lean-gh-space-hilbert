import PaperN.PartI.FullSupportProbability
import PaperN.PartI.Barycenter

namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The manuscript's `(1-t) μ + t ν`, with both coefficients explicitly nonnegative. -/
noncomputable def probabilityMixture (μ ν : ProbabilityMeasure Y) (t : ℝ≥0) (ht : t ≤ 1) :
    ProbabilityMeasure Y :=
  ⟨(1 - t) • (μ : Measure Y) + t • (ν : Measure Y), by
    constructor
    simp only [Measure.add_apply, Measure.coe_nnreal_smul_apply, measure_univ, mul_one]
    rw [← ENNReal.coe_add, tsub_add_cancel_of_le ht]
    rfl⟩

omit [BorelSpace Y] in
theorem probabilityMixture_fullSupport (μ ν : ProbabilityMeasure Y)
    [IsOpenPosMeasure (ν : Measure Y)] (t : ℝ≥0) (ht : t ≤ 1) (hpos : 0 < t) :
    IsOpenPosMeasure (probabilityMixture μ ν t ht : Measure Y) := by
  constructor
  intro U hU hne
  have hν := (hU.measure_ne_zero (ν : Measure Y) hne)
  change ((1 - t) • (μ : Measure Y) + t • (ν : Measure Y)) U ≠ 0
  simp only [Measure.add_apply, Measure.coe_nnreal_smul_apply, ne_eq, add_eq_zero,
    mul_eq_zero]
  exact fun h ↦ h.2.elim (fun h ↦ (ne_of_gt hpos) (ENNReal.coe_eq_zero.mp h)) hν

theorem integral_probabilityMixture (μ ν : ProbabilityMeasure Y) (t : ℝ≥0) (ht : t ≤ 1)
    (f : Y →ᵇ ℝ) :
    (∫ x, f x ∂(probabilityMixture μ ν t ht : Measure Y)) =
      (1 - (t : ℝ)) * (∫ x, f x ∂(μ : Measure Y)) +
        (t : ℝ) * (∫ x, f x ∂(ν : Measure Y)) := by
  change (∫ x, f x ∂((1 - t) • (μ : Measure Y) + t • (ν : Measure Y))) = _
  rw [integral_add_measure (f.integrable _) (f.integrable _)]
  simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, NNReal.coe_sub ht, NNReal.coe_one]

theorem norm_integral_probabilityMixture_sub_le (μ ν : ProbabilityMeasure Y)
    (t : ℝ≥0) (ht : t ≤ 1) (f : Y →ᵇ ℝ) :
    ‖(∫ x, f x ∂(probabilityMixture μ ν t ht : Measure Y)) -
      ∫ x, f x ∂(μ : Measure Y)‖ ≤ 2 * (t : ℝ) * ‖f‖ := by
  rw [integral_probabilityMixture]
  have he : (1 - (t : ℝ)) * (∫ x, f x ∂(μ : Measure Y)) +
      (t : ℝ) * (∫ x, f x ∂(ν : Measure Y)) - (∫ x, f x ∂(μ : Measure Y)) =
      (t : ℝ) * ((∫ x, f x ∂(ν : Measure Y)) - (∫ x, f x ∂(μ : Measure Y))) := by ring
  rw [he, norm_mul, Real.norm_of_nonneg t.coe_nonneg]
  calc
    _ ≤ (t : ℝ) * (‖∫ x, f x ∂(ν : Measure Y)‖ + ‖∫ x, f x ∂(μ : Measure Y)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) t.coe_nonneg
    _ ≤ (t : ℝ) * (‖f‖ + ‖f‖) := mul_le_mul_of_nonneg_left
      (add_le_add (f.norm_integral_le_norm _) (f.norm_integral_le_norm _)) t.coe_nonneg
    _ = _ := by ring
end PaperN.PartI
