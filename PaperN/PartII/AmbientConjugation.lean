import PaperN.PartII.AmbientRieszRange
import PaperN.PartII.ContinuousCutoffProjection
import Mathlib.Topology.ContinuousMap.Star

namespace PaperN.PartII.AmbientKernel
open MeasureTheory
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem ambientOperator_star (f : C(Z, ℂ)) :
    ambientOperator e μ (star f) = star (ambientOperator e μ f) := by
  ext z
  simp only [ambientOperator_integral, ContinuousMap.star_apply]
  change _ = (starRingEnd ℂ) (∫ y, (dist z (e y) : ℂ) * f (e y) ∂μ)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp

theorem restriction_star (f : C(Z, ℂ)) :
    restriction e μ (star f) = star (restriction e μ f) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 2) ((star f).comp e),
    Lp.coeFn_star (restriction e μ f),
    ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 2) (f.comp e)] with x hs hl hf
  exact hs.trans (by rw [hl]; exact congrArg star hf.symm)

theorem star_mem_ambientCutoff (η : ℝ) (f : C(Z, ℂ))
    (hf : f ∈ ambientAlgebraicCutoff e μ η) : star f ∈ ambientAlgebraicCutoff e μ η := by
  refine Submodule.iSup_induction _ (motive := fun g ↦ star g ∈ ambientAlgebraicCutoff e μ η) hf ?_ ?_ ?_
  · intro a f hf
    refine Submodule.iSup_induction _ (motive := fun g ↦ star g ∈ ambientAlgebraicCutoff e μ η) hf ?_ ?_ ?_
    · intro ha f hf
      have hv := Module.End.mem_eigenspace_iff.mp hf
      change ambientOperator e μ f = a • f at hv
      have hs : star f ∈ Module.End.eigenspace (ambientOperator e μ).toLinearMap (star a) := by
        apply Module.End.mem_eigenspace_iff.mpr
        change ambientOperator e μ (star f) = star a • star f
        rw [ambientOperator_star, hv, star_smul]
      have hb : η < ‖star a‖ := by simpa using ha
      have hle : Module.End.eigenspace (ambientOperator e μ).toLinearMap (star a) ≤
          ambientAlgebraicCutoff e μ η := le_iSup_of_le (star a) (le_iSup_of_le hb le_rfl)
      exact hle hs
    · simp
    · intro f g hf hg
      simpa only [star_add] using (ambientAlgebraicCutoff e μ η).add_mem hf hg
  · simp
  · intro f g hf hg
    simpa only [star_add] using (ambientAlgebraicCutoff e μ η).add_mem hf hg

theorem ambientCutoff_real_of_restriction_real (η : ℝ) (hη : 0 < η)
    (f : C(Z, ℂ)) (hf : f ∈ ambientAlgebraicCutoff e μ η)
    (hr : star (restriction e μ f) = restriction e μ f) : star f = f := by
  apply sub_eq_zero.mp
  apply restriction_selected_zero e μ {a | η < ‖a‖} (by simp [not_lt.mpr hη.le])
  · exact (ambientAlgebraicCutoff e μ η).sub_mem (star_mem_ambientCutoff e μ η f hf) hf
  · rw [map_sub, restriction_star, hr, sub_self]

end PaperN.PartII.AmbientKernel
