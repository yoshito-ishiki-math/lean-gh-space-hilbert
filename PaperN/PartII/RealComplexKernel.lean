import PaperN.PartII.ComplexSymmetry
import PaperN.PartII.CutoffIdentification

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MeasurableSpace X]
variable (μ : Measure X)

noncomputable def realPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ
noncomputable def imagPart : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ
noncomputable def realEmbed : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

theorem realPart_ae (f : Lp ℂ 2 μ) : (realPart μ f : X → ℝ) =ᵐ[μ] fun x ↦ (f x).re :=
  Complex.reCLM.coeFn_compLpL f

theorem imagPart_ae (f : Lp ℂ 2 μ) : (imagPart μ f : X → ℝ) =ᵐ[μ] fun x ↦ (f x).im :=
  Complex.imCLM.coeFn_compLpL f

theorem realEmbed_ae (f : Lp ℝ 2 μ) : (realEmbed μ f : X → ℂ) =ᵐ[μ] fun x ↦ (f x : ℂ) :=
  Complex.ofRealCLM.coeFn_compLpL f

theorem realEmbed_parts (f : Lp ℂ 2 μ) :
    realEmbed μ (realPart μ f) + Complex.I • realEmbed μ (imagPart μ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (realEmbed μ (realPart μ f)) (Complex.I • realEmbed μ (imagPart μ f)),
    Lp.coeFn_smul Complex.I (realEmbed μ (imagPart μ f)), realEmbed_ae μ (realPart μ f),
    realEmbed_ae μ (imagPart μ f), realPart_ae μ f, imagPart_ae μ f] with x ha hs hr hi hfr hfi
  simp only [ha, hs, hr, hi, hfr, hfi, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa [mul_comm] using Complex.re_add_im (f x)

theorem realPart_realEmbed (f : Lp ℝ 2 μ) : realPart μ (realEmbed μ f) = f := by
  apply Lp.ext
  filter_upwards [realPart_ae μ (realEmbed μ f), realEmbed_ae μ f] with x hr he
  simp [hr,he]

theorem realEmbed_injective : Function.Injective (realEmbed μ) := by
  intro f g h
  have hh := congrArg (realPart μ) h
  simpa only [realPart_realEmbed] using hh

theorem imagPart_realEmbed (f : Lp ℝ 2 μ) : imagPart μ (realEmbed μ f) = 0 := by
  apply Lp.ext
  filter_upwards [imagPart_ae μ (realEmbed μ f), realEmbed_ae μ f, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hi he hz
  simp only [hi, he, hz, Pi.zero_apply, Complex.ofReal_im]

theorem realPart_complex_smul (a : ℂ) (f : Lp ℂ 2 μ) :
    realPart μ (a • f) = a.re • realPart μ f - a.im • imagPart μ f := by
  apply Lp.ext
  filter_upwards [realPart_ae μ (a • f), Lp.coeFn_smul a f,
    Lp.coeFn_sub (a.re • realPart μ f) (a.im • imagPart μ f),
    Lp.coeFn_smul a.re (realPart μ f), Lp.coeFn_smul a.im (imagPart μ f),
    realPart_ae μ f, imagPart_ae μ f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [h₁, h₂, h₃, Pi.sub_apply, h₄, h₅, Pi.smul_apply, h₆, h₇, smul_eq_mul, Complex.mul_re]

theorem imagPart_complex_smul (a : ℂ) (f : Lp ℂ 2 μ) :
    imagPart μ (a • f) = a.re • imagPart μ f + a.im • realPart μ f := by
  apply Lp.ext
  filter_upwards [imagPart_ae μ (a • f), Lp.coeFn_smul a f,
    Lp.coeFn_add (a.re • imagPart μ f) (a.im • realPart μ f),
    Lp.coeFn_smul a.re (imagPart μ f), Lp.coeFn_smul a.im (realPart μ f),
    realPart_ae μ f, imagPart_ae μ f] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [h₁, h₂, h₃, Pi.add_apply, h₄, h₅, Pi.smul_apply, h₆, h₇, smul_eq_mul, Complex.mul_im]

variable [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ]

theorem distanceOperator_realPart (f : Lp ℂ 2 μ) :
    realPart μ (distanceOperator μ f) = PaperN.PartII.distanceOperator μ (realPart μ f) := by
  apply Lp.ext
  filter_upwards [realPart_ae μ (distanceOperator μ f), distanceOperator_ae μ f,
    PaperN.PartII.distanceOperator_ae μ (realPart μ f)] with x hr hc ht
  rw [hr,hc,ht]
  have hh : (∫ y, (dist x y : ℂ) * f y ∂μ).re =
      ∫ y, ((dist x y : ℂ) * f y).re ∂μ :=
    (integral_re (distanceIntegrand_integrable μ f x)).symm
  rw [hh]
  apply integral_congr_ae
  filter_upwards [realPart_ae μ f] with y hy
  simp [hy, Complex.mul_re]

theorem distanceOperator_imagPart (f : Lp ℂ 2 μ) :
    imagPart μ (distanceOperator μ f) = PaperN.PartII.distanceOperator μ (imagPart μ f) := by
  apply Lp.ext
  filter_upwards [imagPart_ae μ (distanceOperator μ f), distanceOperator_ae μ f,
    PaperN.PartII.distanceOperator_ae μ (imagPart μ f)] with x hr hc ht
  rw [hr,hc,ht]
  have hh : (∫ y, (dist x y : ℂ) * f y ∂μ).im =
      ∫ y, ((dist x y : ℂ) * f y).im ∂μ :=
    (integral_im (distanceIntegrand_integrable μ f x)).symm
  rw [hh]
  apply integral_congr_ae
  filter_upwards [imagPart_ae μ f] with y hy
  simp [hy, Complex.mul_im]

theorem distanceOperator_realEmbed (f : Lp ℝ 2 μ) :
    distanceOperator μ (realEmbed μ f) = realEmbed μ (PaperN.PartII.distanceOperator μ f) := by
  apply Lp.ext
  filter_upwards [distanceOperator_ae μ (realEmbed μ f),
    realEmbed_ae μ (PaperN.PartII.distanceOperator μ f), PaperN.PartII.distanceOperator_ae μ f]
    with x hc he hr
  rw [hc,he,hr, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [realEmbed_ae μ f] with y hy
  simp [hy]
theorem realPart_eigenvector (a : ℝ) (f : Lp ℂ 2 μ)
    (hf : distanceOperator μ f = (a : ℂ) • f) :
    PaperN.PartII.distanceOperator μ (realPart μ f) = a • realPart μ f := by
  rw [← distanceOperator_realPart, hf]
  change realPart μ (a • f) = _
  exact map_smul _ _ _

theorem imagPart_eigenvector (a : ℝ) (f : Lp ℂ 2 μ)
    (hf : distanceOperator μ f = (a : ℂ) • f) :
    PaperN.PartII.distanceOperator μ (imagPart μ f) = a • imagPart μ f := by
  rw [← distanceOperator_imagPart, hf]
  change imagPart μ (a • f) = _
  exact map_smul _ _ _

theorem realEmbed_eigenvector (a : ℝ) (f : Lp ℝ 2 μ)
    (hf : PaperN.PartII.distanceOperator μ f = a • f) :
    distanceOperator μ (realEmbed μ f) = (a : ℂ) • realEmbed μ f := by
  rw [distanceOperator_realEmbed, hf, map_smul]
  rfl
end PaperN.PartII.ComplexKernel
