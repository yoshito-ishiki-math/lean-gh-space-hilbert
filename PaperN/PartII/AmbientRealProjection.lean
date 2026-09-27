import PaperN.PartII.AmbientConjugation

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

theorem star_realEmbed (f : Lp ℝ 2 μ) : star (realEmbed μ f) = realEmbed μ f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (realEmbed μ f), realEmbed_ae μ f] with x hs he
  simp only [hs, Pi.star_apply, he, Complex.star_def, Complex.conj_ofReal]
end PaperN.PartII.ComplexKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_continuousRealEmbed (f : C(Z, ℝ)) :
    restriction e μ (continuousRealEmbed f) =
      realEmbed μ (PaperN.PartII.continuousToL2 μ (f.comp e)) :=
  continuousToL2_realEmbed μ (f.comp e)

theorem ambient_cutoffCircle_preserves_real
    (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : C(Z, ℝ)) :
    star (cutoffCircleOperator (ambientOperator e μ) η B (continuousRealEmbed f)) =
      cutoffCircleOperator (ambientOperator e μ) η B (continuousRealEmbed f) := by
  apply ambientCutoff_real_of_restriction_real e μ η hη
  · rw [← ambient_cutoffCircle_range e μ  he η B hη hB hd hp hn]
    exact ⟨continuousRealEmbed f, rfl⟩
  · have h := restriction_cutoffCircle e μ he η B hη hB hd hp hn
    rw [← distance_cutoffCircle_eq_starProjection μ η B hη hB hd hp hn] at h
    have hh := DFunLike.congr_fun h (continuousRealEmbed f)
    change restriction e μ (cutoffCircleOperator (ambientOperator e μ) η B (continuousRealEmbed f)) =
      cutoffCircleOperator (ComplexKernel.distanceOperator μ) η B
        (restriction e μ (continuousRealEmbed f)) at hh
    rw [hh, restriction_continuousRealEmbed,
      distance_cutoffCircle_realEmbed μ hf η B hη hB hd hp hn, star_realEmbed]

theorem ambient_cutoffCircle_real_pointwise
    (hf : CompactEigenvalueFinitenessInput.{u})
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : C(Z, ℝ)) (z : Z) :
    (cutoffCircleOperator (ambientOperator e μ) η B (continuousRealEmbed f) z).im = 0 := by
  have h := congrArg (fun g : C(Z, ℂ) ↦ (g z).im)
    (ambient_cutoffCircle_preserves_real e μ hf  he η B hη hB hd hp hn f)
  simp only [ContinuousMap.star_apply, Complex.star_def, Complex.conj_im] at h
  linarith

end PaperN.PartII.AmbientKernel
