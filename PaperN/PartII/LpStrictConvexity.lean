import PaperN.PartII.RealPowerConvexity
import Mathlib.Analysis.Convex.StrictConvexSpace

namespace PaperN.PartII
open MeasureTheory Filter

/-- The real-valued Lp norm power is the integral power energy. -/
theorem lp_norm_rpow_eq_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ENNReal) [Fact (1 ≤ p)] (hp0 : p ≠ 0) (hpfin : p ≠ ⊤)
    (f : Lp ℝ p μ) : ‖f‖ ^ p.toReal = ∫ x, |f x| ^ p.toReal ∂μ := by
  have hn : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂μ := integral_nonneg (fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm hp0 hpfin,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hn _), ← Real.rpow_mul hn,
    inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpfin⟩), Real.rpow_one]
  rfl

/-- Real-valued Lp is strictly convex at every finite exponent above one. -/
theorem lp_strictConvexSpace {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (p : ENNReal) [Fact (1 ≤ p)] (hp : 1 < p.toReal) (hpfin : p ≠ ⊤) :
    StrictConvexSpace ℝ (Lp ℝ p μ) := by
  have hp0 : p ≠ 0 := by intro h; rw [h, ENNReal.toReal_zero] at hp; norm_num at hp
  apply StrictConvexSpace.of_norm_combo_ne_one
  intro f g hf hg hfg
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  intro hm
  let m : Lp ℝ p μ := (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g
  have hmae : (fun x ↦ m x) =ᵐ[μ] (fun x ↦ (f x + g x) / 2) := by
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℝ) • f) ((1 / 2 : ℝ) • g),
      Lp.coeFn_smul (1 / 2 : ℝ) f, Lp.coeFn_smul (1 / 2 : ℝ) g] with x ha hb hc
    change (((1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g) : Lp ℝ p μ) x = _
    rw [ha]
    change ((1 / 2 : ℝ) • f : Lp ℝ p μ) x + ((1 / 2 : ℝ) • g : Lp ℝ p μ) x = _
    rw [hb, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hpow : (fun x ↦ |m x| ^ p.toReal) =ᵐ[μ] (fun x ↦ |(f x + g x) / 2| ^ p.toReal) := by
    filter_upwards [hmae] with x hx
    rw [hx]
  have hfi : Integrable (fun x ↦ |f x| ^ p.toReal) μ := (Lp.memLp f).integrable_norm_rpow hp0 hpfin
  have hgi : Integrable (fun x ↦ |g x| ^ p.toReal) μ := (Lp.memLp g).integrable_norm_rpow hp0 hpfin
  have hmi : Integrable (fun x ↦ |(f x + g x) / 2| ^ p.toReal) μ :=
    ((Lp.memLp m).integrable_norm_rpow hp0 hpfin).congr hpow
  have he : (∫ x, |(f x + g x) / 2| ^ p.toReal ∂μ) =
      ((∫ x, |f x| ^ p.toReal ∂μ) + ∫ x, |g x| ^ p.toReal ∂μ) / 2 := by
    rw [← integral_congr_ae hpow,
      ← lp_norm_rpow_eq_integral μ p hp0 hpfin m,
      ← lp_norm_rpow_eq_integral μ p hp0 hpfin f,
      ← lp_norm_rpow_eq_integral μ p hp0 hpfin g]
    change ‖(1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g‖ ^ p.toReal = _
    rw [hm, hf, hg, Real.one_rpow]
    norm_num
  exact hfg (Lp.ext ((integral_abs_midpoint_rpow_eq_iff μ p.toReal hp f g hfi hgi hmi).mp he))

end PaperN.PartII
