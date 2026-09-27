import PaperN.PartI.LimitSupportStatements
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace PaperN.PartI
open MeasureTheory Metric Filter
open scoped Topology BoundedContinuousFunction

/-- Full mass cannot escape the Hausdorff limit, even though the carriers vary. -/
theorem limitSupport_spec : LimitSupportStatement := by
  intro Z _ _ _ _ Ks K hKs hne hK hKne hH μs μ hW hm
  let f : Z →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨fun z ↦ infDist z K, continuous_infDist_pt K⟩
  have hn (n : ℕ) : 0 ≤ ∫ z, f z ∂(μs n : Measure Z) :=
    integral_nonneg (fun z ↦ infDist_nonneg)
  have hb (n : ℕ) : (∫ z, f z ∂(μs n : Measure Z)) ≤ hausdorffDist (Ks n) K := by
    calc
      _ ≤ ∫ _, hausdorffDist (Ks n) K ∂(μs n : Measure Z) := by
        apply integral_mono_ae (f.integrable _) (integrable_const _)
        filter_upwards [(mem_ae_iff_prob_eq_one (hKs n).measurableSet).mpr (hm n)] with z hz
        exact infDist_le_hausdorffDist_of_mem hz
          (hausdorffEDist_ne_top_of_nonempty_of_bounded (hne n) hKne
            (hKs n).isBounded hK.isBounded)
      _ = _ := by simp
  have hi : (∫ z, f z ∂(μ : Measure Z)) = 0 :=
    tendsto_nhds_unique (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hW f)
      (squeeze_zero hn hb hH)
  have ha := (integral_eq_zero_iff_of_nonneg (fun z ↦ show 0 ≤ f z from infDist_nonneg)
    (f.integrable _)).mp hi
  apply (mem_ae_iff_prob_eq_one hK.measurableSet).mp
  filter_upwards [ha] with z hz
  exact (hK.isClosed.mem_iff_infDist_zero hKne).mpr hz
end PaperN.PartI
