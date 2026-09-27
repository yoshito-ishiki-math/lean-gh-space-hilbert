import PaperN.PartII.RestrictionRealProjection

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

def continuousRealEmbed (g : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩

theorem continuousToL2_realEmbed (g : C(X, ℝ)) :
    continuousToL2 μ (continuousRealEmbed g) = realEmbed μ (PaperN.PartII.continuousToL2 μ g) := by
  apply Lp.ext
  filter_upwards [ContinuousMap.coeFn_toLp μ (𝕜 := ℂ) (p := 2) (continuousRealEmbed g),
    realEmbed_ae μ (PaperN.PartII.continuousToL2 μ g),
    ContinuousMap.coeFn_toLp μ (𝕜 := ℝ) (p := 2) g] with x hc he hr
  exact hc.trans (by rw [he]; exact congrArg Complex.ofReal hr.symm)

variable [μ.IsOpenPosMeasure]

noncomputable def realProjectionRepresentative (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) (f : Lp ℝ 2 μ) : spectralCutoff μ η :=
  (spectralCutoffEquiv μ hη).symm ⟨realCutoffProjection μ hf η hη f, by
    letI finiteCutoff := realCutoff_finiteDimensional μ hf η hη
    exact Submodule.starProjection_apply_mem _ _⟩

theorem realProjectionRepresentative_toL2 (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) (f : Lp ℝ 2 μ) :
    PaperN.PartII.continuousToL2 μ (realProjectionRepresentative μ hf η hη f) =
      realCutoffProjection μ hf η hη f := by
  exact congrArg Subtype.val ((spectralCutoffEquiv μ hη).apply_symm_apply _)

noncomputable def continuousCutoffProjection (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) (f : Lp ℂ 2 μ) : C(X, ℂ) :=
  continuousRealEmbed (realProjectionRepresentative μ hf η hη (realPart μ f)) +
    Complex.I • continuousRealEmbed (realProjectionRepresentative μ hf η hη (imagPart μ f))

theorem continuousCutoffProjection_toL2 (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) (f : Lp ℂ 2 μ) :
    continuousToL2 μ (continuousCutoffProjection μ hf η hη f) =
      realEmbed μ (realCutoffProjection μ hf η hη (realPart μ f)) +
      Complex.I • realEmbed μ (realCutoffProjection μ hf η hη (imagPart μ f)) := by
  simp only [continuousCutoffProjection, map_add, map_smul, continuousToL2_realEmbed,
    realProjectionRepresentative_toL2]

end PaperN.PartII.ComplexKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem restriction_cutoffCircle_continuous (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : C(Z, ℂ)) :
    (cutoffCircleOperator (ambientOperator e μ) η B f).comp e =
      continuousCutoffProjection μ hf η hη (restriction e μ f) := by
  apply ComplexKernel.continuousToL2_injective μ
  rw [continuousCutoffProjection_toL2]
  exact restriction_cutoffCircle_real_imag e μ hf he η B hη hB hd hp hn f

theorem restriction_cutoffCircle_pointwise (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : C(Z, ℂ)) (x : X) :
    cutoffCircleOperator (ambientOperator e μ) η B f (e x) =
      continuousCutoffProjection μ hf η hη (restriction e μ f) x :=
  DFunLike.congr_fun (restriction_cutoffCircle_continuous e μ hf he η B hη hB hd hp hn f) x

end PaperN.PartII.AmbientKernel
