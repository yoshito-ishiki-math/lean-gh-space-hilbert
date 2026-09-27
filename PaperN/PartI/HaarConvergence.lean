import PaperN.PartI.HaarConvergenceStatements
import PaperN.PartI.UniformOrbit

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartI
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Real integration against the concrete normalized Haar average. -/
theorem integral_haarAverage (μ : ProbabilityMeasure Y) (f : Y →ᵇ ℝ) :
    (∫ x, f x ∂(haarAverage μ : Measure Y)) =
      ∫ g : Y ≃ᵢ Y, ∫ x, f (g x) ∂(μ : Measure Y) ∂isometryHaar := by
  rw [haarAverage, integral_barycenter _ (f.integrable _)]
  rw [ProbabilityMeasure.toMeasure_map]
  rw [integral_map (measurable_orbitProbability μ).aemeasurable
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with g
  exact integral_map g.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable

universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

theorem integral_averagedProbability (C : CommonRealization Xs X) (n : ℕ) (f : C →ᵇ ℝ) :
    (∫ z, f z ∂(C.averagedProbability n : Measure C)) =
      ∫ g : Xs n ≃ᵢ Xs n, ∫ z, f z ∂(C.orbitProbabilityAt n g : Measure C) ∂isometryHaar := by
  rw [averagedProbability]
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (C.seq_isometry n).continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  let F : Xs n →ᵇ ℝ := f.compContinuous ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
  change (∫ x, F x ∂(haarAverage (Xs n).probability : Measure (Xs n))) = _
  rw [integral_haarAverage]
  apply integral_congr_ae
  filter_upwards [] with g
  exact (C.integral_orbitProbabilityAt n g f).symm

/-- Haar averaging on varying carriers preserves convergence to an invariant limit. -/
theorem haarConvergence_spec (C : CommonRealization Xs X) : C.HaarConvergenceStatement := by
  intro hH hW hi
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [C.eventually_orbitError_lt hH hW hi f (half_pos hε)] with n hn
  rw [C.integral_averagedProbability]
  let F : Xs n →ᵇ ℝ := f.compContinuous ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
  have hm : AEStronglyMeasurable
      (fun g : Xs n ≃ᵢ Xs n ↦ ∫ z, f z ∂(C.orbitProbabilityAt n g : Measure C))
      (isometryHaar (X := Xs n)) := by
    have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction F).measurable.comp
      (measurable_orbitProbability (Xs n).probability)
    convert h.aestronglyMeasurable using 1
    ext g
    rw [C.integral_orbitProbabilityAt]
    exact (integral_map g.continuous.measurable.aemeasurable F.continuous.aestronglyMeasurable).symm
  have hInt := Integrable.of_bound hm ‖f‖ (Filter.Eventually.of_forall fun g ↦
    f.norm_integral_le_norm (C.orbitProbabilityAt n g : Measure C))
  have hc : (∫ _ : Xs n ≃ᵢ Xs n,
      (∫ z, f z ∂(C.limitProbability : Measure C)) ∂isometryHaar) =
      ∫ z, f z ∂(C.limitProbability : Measure C) := by simp
  rw [dist_eq_norm, ← hc, ← integral_sub hInt (integrable_const _)]
  have hb := norm_integral_le_of_norm_le_const
    (μ := isometryHaar (X := Xs n)) (Filter.Eventually.of_forall fun g ↦ (hn g).le)
  have hb' : ‖∫ g : Xs n ≃ᵢ Xs n,
      ((∫ z, f z ∂(C.orbitProbabilityAt n g : Measure C)) -
        ∫ z, f z ∂(C.limitProbability : Measure C)) ∂isometryHaar‖ ≤ ε / 2 := by
    simpa only [probReal_univ, mul_one] using hb
  exact hb'.trans_lt (half_lt_self hε)
end CommonRealization
end PaperN.PartI
