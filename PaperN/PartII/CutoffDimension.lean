import PaperN.PartII.RealComplexProjection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def cutoffRealPairEquiv (η : ℝ) :
    complexAlgebraicCutoff (distanceOperator μ) η ≃ₗ[ℝ]
      (l2SpectralCutoff μ η × l2SpectralCutoff μ η) := by
  let L : complexAlgebraicCutoff (distanceOperator μ) η →ₗ[ℝ]
      (l2SpectralCutoff μ η × l2SpectralCutoff μ η) :=
    { toFun := fun f ↦
        let h := parts_mem_of_mem_complexification μ η f
          ((complexCutoff_eq_complexification μ η) ▸ f.property)
        (⟨realPart μ f, h.1⟩, ⟨imagPart μ f, h.2⟩)
      map_add' := by intro f g; ext <;> simp
      map_smul' := by intro a f; ext <;> simp }
  apply LinearEquiv.ofBijective L
  constructor
  · intro f g h
    have hr : realPart μ f = realPart μ g := congrArg (fun p ↦ (p.1 : Lp ℝ 2 μ)) h
    have hi : imagPart μ f = imagPart μ g := congrArg (fun p ↦ (p.2 : Lp ℝ 2 μ)) h
    apply Subtype.ext
    rw [← realEmbed_parts μ f, ← realEmbed_parts μ g, hr, hi]
  · intro p
    let f := realEmbed μ p.1 + Complex.I • realEmbed μ p.2
    have hf : f ∈ complexAlgebraicCutoff (distanceOperator μ) η :=
      (mem_complexCutoff_iff_real_imag μ η f).mpr ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · change realPart μ f = p.1
      simp [f, realPart_complex_smul, realPart_realEmbed, imagPart_realEmbed]
    · change imagPart μ f = p.2
      simp [f, imagPart_complex_smul, realPart_realEmbed, imagPart_realEmbed]

theorem complexCutoff_finrank_eq_real (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) :
    Module.finrank ℂ (complexAlgebraicCutoff (distanceOperator μ) η) =
      Module.finrank ℝ (l2SpectralCutoff μ η) := by
  letI realFinite := realCutoff_finiteDimensional μ hf η hη
  letI complexFinite := distance_complexAlgebraicCutoff_finiteDimensional μ hf η hη
  letI restrictedFinite : FiniteDimensional ℝ (complexAlgebraicCutoff (distanceOperator μ) η) :=
    FiniteDimensional.trans ℝ ℂ _
  have h := (cutoffRealPairEquiv μ η).finrank_eq
  rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℝ ℂ,
    Complex.finrank_real_complex] at h
  omega

theorem complexCutoff_finrank_eq_continuous_real [μ.IsOpenPosMeasure]
    (hf : CompactEigenvalueFinitenessInput.{u}) (η : ℝ) (hη : 0 < η) :
    Module.finrank ℂ (complexAlgebraicCutoff (distanceOperator μ) η) =
      Module.finrank ℝ (spectralCutoff μ η) := by
  rw [complexCutoff_finrank_eq_real μ hf η hη]
  exact (spectralCutoff_finrank_eq μ hη).symm

end PaperN.PartII.ComplexKernel
