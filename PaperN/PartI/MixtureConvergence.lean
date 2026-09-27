import PaperN.PartI.ProbabilityMixture
import PaperN.PartI.Remeasure

namespace PaperN.PartI
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- Small positive mixtures preserve weak convergence even on varying carriers. -/
theorem mixture_weakConverges (C : CommonRealization Xs X) (hW : C.WeakConverges)
    (ν : ∀ n, ProbabilityMeasure (Xs n)) (t : ℕ → ℝ≥0) (ht : ∀ n, t n ≤ 1)
    (hzero : Tendsto (fun n ↦ (t n : ℝ)) atTop (𝓝 0)) :
    (C.withProbabilities (fun n ↦ probabilityMixture (Xs n).probability (ν n) (t n) (ht n))).WeakConverges := by
  change Tendsto (fun n ↦ (show ProbabilityMeasure C from (probabilityMixture (Xs n).probability (ν n) (t n) (ht n)).map
    (C.seqMap n))) atTop (𝓝 C.limitProbability)
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto (Ω := C)).mpr
  intro f
  let F (n : ℕ) : Xs n →ᵇ ℝ :=
    f.compContinuous ⟨C.seqMap n, (C.seq_isometry n).continuous⟩
  have hbound (n : ℕ) :
      ‖(∫ x, F n x ∂(probabilityMixture (Xs n).probability (ν n) (t n) (ht n) : Measure (Xs n))) -
        ∫ x, F n x ∂((Xs n).probability : Measure (Xs n))‖ ≤ 2 * (t n : ℝ) * ‖f‖ :=
    (norm_integral_probabilityMixture_sub_le _ _ _ _ _).trans
      (mul_le_mul_of_nonneg_left (f.norm_compContinuous_le _) (by positivity))
  have he := squeeze_zero (fun n ↦ norm_nonneg _) hbound
    (by simpa using (tendsto_const_nhds.mul hzero).mul_const ‖f‖)
  have he' := tendsto_zero_iff_norm_tendsto_zero.mpr he
  have hbase := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hW f
  have hsum := he'.add hbase
  simp only [zero_add] at hsum
  convert hsum using 1
  · funext n
    change (∫ z, f z ∂Measure.map (C.seqMap n)
      (probabilityMixture (Xs n).probability (ν n) (t n) (ht n) : Measure (Xs n))) = _
    rw [integral_map (C.seq_isometry n).continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    have hi : (∫ z, f z ∂(C.seqProbability n : Measure C)) =
        ∫ x, F n x ∂((Xs n).probability : Measure (Xs n)) :=
      integral_map (C.seq_isometry n).continuous.measurable.aemeasurable
        f.continuous.aestronglyMeasurable
    rw [hi]
    dsimp [F]
    ring
end CommonRealization
end PaperN.PartI
