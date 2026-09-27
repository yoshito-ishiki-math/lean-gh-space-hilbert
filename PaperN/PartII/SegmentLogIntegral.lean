import PaperN.PartII.ContourEigenvector
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace PaperN.PartII
open MeasureTheory Set

/-- A rotated logarithm is a primitive of the scalar resolvent along a segment,
provided the rotated segment avoids the principal logarithm's branch cut. -/
theorem scalarSegment_eq_rotated_log (a p q c : ℂ) (hc : c ≠ 0)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, c * (segmentParameter p q t-a) ∈ Complex.slitPlane) :
    scalarSegment a p q = Complex.log (c*(q-a)) - Complex.log (c*(p-a)) := by
  have hn : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter p q t-a ≠ 0 := by
    intro t ht he
    have h := Complex.slitPlane_ne_zero (hs t ht)
    exact h (by rw [he, mul_zero])
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ ↦ Complex.log (c*(segmentParameter p q t-a)))
        ((q-p)*(segmentParameter p q t-a)⁻¹) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hf : HasDerivAt (fun z : ℂ ↦ c*(p+z*(q-p)-a)) (c*(q-p)) (t : ℂ) := by
      simpa using (((hasDerivAt_id (t : ℂ)).mul_const (q-p)).const_add p |>.sub_const a).const_mul c
    have hlog := (hf.clog (hs t ht')).comp_ofReal
    convert hlog using 1
    · dsimp [segmentParameter]
    · dsimp [segmentParameter]
      field_simp
  have hi : IntervalIntegrable (fun t : ℝ ↦ (q-p)*(segmentParameter p q t-a)⁻¹) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_const.mul
    have htcont : ContinuousAt (fun s : ℝ ↦ segmentParameter p q s-a) t := by
      unfold segmentParameter
      fun_prop
    exact htcont.inv₀ (hn t ht)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simpa [scalarSegment, segmentParameter] using he
end PaperN.PartII
