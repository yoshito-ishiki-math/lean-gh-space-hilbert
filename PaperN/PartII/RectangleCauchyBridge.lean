import PaperN.PartII.RectangleResolvent
import Mathlib.Analysis.Complex.CauchyIntegral

namespace PaperN.PartII
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Reparameterize a horizontal segment by its real coordinate. -/
theorem horizontal_segment_integral (f : ℂ → E) (a b y : ℝ) :
    (∫ t in (0 : ℝ)..1, ((⟨b,y⟩ : ℂ)-⟨a,y⟩) •
      f (segmentParameter ⟨a,y⟩ ⟨b,y⟩ t)) =
      ∫ x in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have he : ∀ t : ℝ, segmentParameter ⟨a,y⟩ ⟨b,y⟩ t =
      ((a + (b-a)*t : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    intro t
    apply Complex.ext <;> simp [segmentParameter, Complex.mul_re, Complex.mul_im] <;> ring
  have hd : (⟨b,y⟩ : ℂ)-⟨a,y⟩ = ((b-a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  simp_rw [he, hd]
  rw [intervalIntegral.integral_smul]
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using intervalIntegral.smul_integral_comp_add_mul
    (fun x : ℝ ↦ f ((x : ℂ) + (y : ℂ) * Complex.I)) (a := 0) (b := 1) (b-a) a

omit [CompleteSpace E] in
/-- Reparameterize a vertical segment by its imaginary coordinate. -/
theorem vertical_segment_integral (f : ℂ → E) (x a b : ℝ) :
    (∫ t in (0 : ℝ)..1, ((⟨x,b⟩ : ℂ)-⟨x,a⟩) •
      f (segmentParameter ⟨x,a⟩ ⟨x,b⟩ t)) =
      Complex.I • ∫ y in a..b, f ((x : ℂ) + (y : ℂ) * Complex.I) := by
  have he : ∀ t : ℝ, segmentParameter ⟨x,a⟩ ⟨x,b⟩ t =
      (x : ℂ) + ((a + (b-a)*t : ℝ) : ℂ) * Complex.I := by
    intro t
    apply Complex.ext <;> simp [segmentParameter, Complex.mul_re, Complex.mul_im] <;> ring
  have hd : (⟨x,b⟩ : ℂ)-⟨x,a⟩ = Complex.I * ((b-a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  simp_rw [he, hd, mul_smul]
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_smul]
  congr 1
  simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using intervalIntegral.smul_integral_comp_add_mul
    (fun y : ℝ ↦ f ((x : ℂ) + (y : ℂ) * Complex.I)) (a := 0) (b := 1) (b-a) a
/-- The implemented rectangle integral vanishes when its whole closed rectangle
is in the resolvent set. -/
theorem rectangleResolvent_eq_zero_of_closed_rectangle
    (U : E →L[ℂ] E) (l r h : ℝ)
    (hz : ∀ z ∈ Set.uIcc l r ×ℂ Set.uIcc (-h) h, z ∈ resolventSet ℂ U) :
    rectangleResolvent U l r h = 0 := by
  have hd : DifferentiableOn ℂ (resolvent U) (Set.uIcc l r ×ℂ Set.uIcc (-h) h) := by
    intro z hzs
    exact (spectrum.hasDerivAt_resolvent_const_left (hz z hzs)).differentiableAt.differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (resolvent U) (⟨l,-h⟩ : ℂ) (⟨r,h⟩ : ℂ) hd
  unfold rectangleResolvent quadrilateralResolvent segmentResolvent
  rw [horizontal_segment_integral, vertical_segment_integral,
    horizontal_segment_integral, vertical_segment_integral]
  rw [intervalIntegral.integral_symm l r, intervalIntegral.integral_symm (-h) h]
  rw [smul_neg]
  have he : (∫ x in l..r, resolvent U ((x : ℂ) + ((-h : ℝ) : ℂ) * Complex.I)) +
      Complex.I • (∫ y in (-h)..h, resolvent U ((r : ℂ) + (y : ℂ) * Complex.I)) +
      -(∫ x in l..r, resolvent U ((x : ℂ) + (h : ℂ) * Complex.I)) +
      -(Complex.I • (∫ y in (-h)..h, resolvent U ((l : ℂ) + (y : ℂ) * Complex.I))) = 0 := by
    convert hc using 1 <;> dsimp <;> abel
  rw [he, smul_zero]
end PaperN.PartII
