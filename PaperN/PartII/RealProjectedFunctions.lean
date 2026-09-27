import PaperN.PartII.SpectralProjectionProperties

namespace PaperN.PartII.ComplexKernel
open MeasureTheory Filter
open scoped Topology
variable {Z : Type*} [MetricSpace Z]

noncomputable def continuousRealPart : C(Z, ℂ) →L[ℝ] C(Z, ℝ) :=
  Complex.reCLM.compLeftContinuous ℝ Z

@[simp] theorem continuousRealPart_apply (f : C(Z, ℂ)) (z : Z) :
    continuousRealPart f z = (f z).re := rfl

@[simp] theorem continuousRealPart_embed (f : C(Z, ℝ)) :
    continuousRealPart (continuousRealEmbed f) = f := by
  ext z
  rfl

theorem continuousRealEmbed_realPart (f : C(Z, ℂ)) (hf : ∀ z, (f z).im = 0) :
    continuousRealEmbed (continuousRealPart f) = f := by
  ext z
  exact Complex.ext rfl (by change 0 = (f z).im; exact (hf z).symm)

noncomputable def realProjectedFunction (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ)) (f : C(Z, ℝ)) : C(Z, ℝ) :=
  continuousRealPart (P (continuousRealEmbed f))

theorem realProjectedFunction_tendsto
    (Ps : ℕ → C(Z, ℂ) →L[ℂ] C(Z, ℂ)) (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ))
    (hP : ∀ g, Tendsto (fun n ↦ Ps n g) atTop (𝓝 (P g))) (f : C(Z, ℝ)) :
    Tendsto (fun n ↦ realProjectedFunction (Ps n) f) atTop (𝓝 (realProjectedFunction P f)) :=
  continuousRealPart.continuous.continuousAt.tendsto.comp (hP (continuousRealEmbed f))

variable [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]

theorem continuousRealPart_mem_cutoff (μ : Measure Z) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] {η : ℝ} (hη : 0 < η) (f : C(Z, ℂ))
    (hf : f ∈ continuousComplexCutoff μ η) :
    continuousRealPart f ∈ spectralCutoff μ η := by
  obtain ⟨u, hu, v, hv, he⟩ := (mem_continuousComplexCutoff_iff μ hη f).mp hf
  have hr : continuousRealPart f = u := by
    ext z
    rw [continuousRealPart_apply, he]
    simp [continuousRealEmbed]
  rw [hr]
  exact hu

end PaperN.PartII.ComplexKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem realPart_restrict_mem_cutoff (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (g : C(Z, ℂ)) (hg : g ∈ ambientAlgebraicCutoff e μ η) :
    (continuousRealPart g).comp e ∈ spectralCutoff μ η := by
  have h := (restrictionCutoffEquiv e μ he η hη ⟨g, hg⟩).property
  have hc : g.comp e ∈ continuousComplexCutoff μ η := h
  exact continuousRealPart_mem_cutoff μ hη (g.comp e) hc

theorem realProjectedFunction_mem_cutoff (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ))
    (hP : SpectralProjectionProperties (ambientOperator e μ) P η) (f : C(Z, ℝ)) :
    (realProjectedFunction P f).comp e ∈ spectralCutoff μ η := by
  apply realPart_restrict_mem_cutoff e μ he η hη
  have hg : P (continuousRealEmbed f) ∈ LinearMap.range P.toLinearMap := ⟨_, rfl⟩
  rw [hP.2.2.1, ← ambient_cutoff_spectrum_iSup e μ he η hη,
    ambient_cutoff_generalized_eq e μ he η hη] at hg
  exact hg

end PaperN.PartII.AmbientKernel
