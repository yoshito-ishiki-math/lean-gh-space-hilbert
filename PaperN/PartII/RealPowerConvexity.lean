import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace PaperN.PartII

/-- Convexity of the scalar power energy at midpoints. -/
theorem abs_midpoint_rpow_le (q : ℝ) (hq : 1 ≤ q) (x y : ℝ) :
    |(x + y) / 2| ^ q ≤ (|x| ^ q + |y| ^ q) / 2 := by
  have hnorm : |(x + y) / 2| ≤ (|x| + |y|) / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le x y) (by norm_num)
  have hc := (convexOn_rpow hq).2 (abs_nonneg x) (abs_nonneg y)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hc
  have hp := Real.rpow_le_rpow (abs_nonneg ((x+y)/2)) hnorm (by linarith : 0 ≤ q)
  have hc' : ((|x| + |y|) / 2) ^ q ≤ (|x| ^ q + |y| ^ q) / 2 := by
    convert hc using 1 <;> congr 1 <;> ring
  exact hp.trans hc'

/-- Distinct real values have strictly smaller midpoint power energy for q > 1. -/
theorem abs_midpoint_rpow_lt (q : ℝ) (hq : 1 < q) (x y : ℝ) (hxy : x ≠ y) :
    |(x + y) / 2| ^ q < (|x| ^ q + |y| ^ q) / 2 := by
  by_cases he : |x| = |y|
  · have hop : x = -y := (abs_eq_abs.mp he).resolve_left hxy
    have hy : y ≠ 0 := by
      intro h
      apply hxy
      simp_all
    have hp : 0 < |y| ^ q := Real.rpow_pos_of_pos (abs_pos.mpr hy) q
    rw [hop]
    simp only [neg_add_cancel, zero_div, Real.zero_rpow (by linarith : q ≠ 0), abs_zero, abs_neg]
    linarith
  · have hnorm : |(x + y) / 2| ≤ (|x| + |y|) / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right (abs_add_le x y) (by norm_num)
    have hc := (strictConvexOn_rpow hq).2 (abs_nonneg x) (abs_nonneg y) he
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
    simp only [smul_eq_mul] at hc
    have hp := Real.rpow_le_rpow (abs_nonneg ((x+y)/2)) hnorm (by linarith : 0 ≤ q)
    have hc' : ((|x| + |y|) / 2) ^ q < (|x| ^ q + |y| ^ q) / 2 := by
      convert hc using 1 <;> congr 1 <;> ring
    exact hp.trans_lt hc'

/-- Equality of midpoint energy forces equality of the real inputs. -/
theorem abs_midpoint_rpow_eq_iff (q : ℝ) (hq : 1 < q) (x y : ℝ) :
    |(x + y) / 2| ^ q = (|x| ^ q + |y| ^ q) / 2 ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_lt (abs_midpoint_rpow_lt q hq x y hne)) h
  · intro h
    subst y
    rw [show (x + x) / 2 = x by ring]
    ring

open MeasureTheory Filter

/-- Equality in the integrated midpoint inequality is precisely almost-everywhere equality. -/
theorem integral_abs_midpoint_rpow_eq_iff
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (q : ℝ) (hq : 1 < q)
    (f g : X → ℝ)
    (hf : Integrable (fun x ↦ |f x| ^ q) μ)
    (hg : Integrable (fun x ↦ |g x| ^ q) μ)
    (hm : Integrable (fun x ↦ |(f x + g x) / 2| ^ q) μ) :
    (∫ x, |(f x + g x) / 2| ^ q ∂μ) =
      ((∫ x, |f x| ^ q ∂μ) + ∫ x, |g x| ^ q ∂μ) / 2 ↔ f =ᵐ[μ] g := by
  have hav : Integrable (fun x ↦ (|f x| ^ q + |g x| ^ q) / 2) μ :=
    (hf.add hg).div_const 2
  have hle : (fun x ↦ |(f x + g x) / 2| ^ q) ≤ᵐ[μ]
      (fun x ↦ (|f x| ^ q + |g x| ^ q) / 2) :=
    Eventually.of_forall (fun x ↦ abs_midpoint_rpow_le q hq.le (f x) (g x))
  have he := integral_eq_iff_of_ae_le hm hav hle
  rw [integral_div, integral_add hf hg] at he
  rw [he]
  exact eventually_congr (Eventually.of_forall (fun x ↦ abs_midpoint_rpow_eq_iff q hq (f x) (g x)))

end PaperN.PartII
