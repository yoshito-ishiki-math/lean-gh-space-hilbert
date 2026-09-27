import PaperN.PartII.RealProjectedFunctions

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

theorem exists_real_cutoff_extension (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (f : C(X, ℝ)) (hf : f ∈ spectralCutoff μ η) :
    ∃ g : C(Z, ℝ), g.comp e = f ∧ continuousRealEmbed g ∈ ambientAlgebraicCutoff e μ η := by
  have hc : continuousRealEmbed f ∈ continuousComplexCutoff μ η :=
    (mem_continuousComplexCutoff_iff μ hη _).mpr ⟨f, hf, 0, (spectralCutoff μ η).zero_mem, by ext x; simp [continuousRealEmbed]⟩
  let h := (restrictionCutoffEquiv e μ he η hη).symm
    ⟨ComplexKernel.continuousToL2 μ (continuousRealEmbed f), hc⟩
  have hr : restriction e μ (h : C(Z, ℂ)) =
      ComplexKernel.continuousToL2 μ (continuousRealEmbed f) :=
    congrArg Subtype.val ((restrictionCutoffEquiv e μ he η hη).apply_symm_apply _)
  have heq : (h : C(Z, ℂ)).comp e = continuousRealEmbed f :=
    ComplexKernel.continuousToL2_injective μ hr
  have hs : star (h : C(Z, ℂ)) = h := by
    apply ambientCutoff_real_of_restriction_real e μ η hη h h.property
    rw [hr, continuousToL2_realEmbed, star_realEmbed]
  have him : ∀ z, ((h : C(Z, ℂ)) z).im = 0 := by
    intro z
    have hz := congrArg (fun g : C(Z, ℂ) ↦ (g z).im) hs
    simp only [ContinuousMap.star_apply, Complex.star_def, Complex.conj_im] at hz
    linarith
  refine ⟨continuousRealPart h, ?_, ?_⟩
  · have hp := congrArg continuousRealPart heq
    change continuousRealPart ((h : C(Z, ℂ)).comp e) = _ at hp
    rw [continuousRealPart_embed] at hp
    exact hp
  · rw [continuousRealEmbed_realPart (h : C(Z, ℂ)) him]
    exact h.property

omit [μ.IsOpenPosMeasure] in
theorem realProjectedFunction_eq_of_mem (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ))
    (hP : SpectralProjectionProperties (ambientOperator e μ) P η)
    (g : C(Z, ℝ)) (hg : continuousRealEmbed g ∈ ambientAlgebraicCutoff e μ η) :
    realProjectedFunction P g = g := by
  have hr : continuousRealEmbed g ∈ LinearMap.range P.toLinearMap := by
    rw [hP.2.2.1, ← ambient_cutoff_spectrum_iSup e μ he η hη,
      ambient_cutoff_generalized_eq e μ he η hη]
    exact hg
  obtain ⟨v, hv⟩ := hr
  have hi := DFunLike.congr_fun hP.1 v
  change P (P v) = P v at hi
  change P v = continuousRealEmbed g at hv
  rw [hv] at hi
  unfold realProjectedFunction
  rw [hi, continuousRealPart_embed]

theorem exists_real_projected_extension (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ))
    (hP : SpectralProjectionProperties (ambientOperator e μ) P η)
    (f : C(X, ℝ)) (hf : f ∈ spectralCutoff μ η) :
    ∃ g : C(Z, ℝ), g.comp e = f ∧ realProjectedFunction P g = g := by
  obtain ⟨g, hg, hm⟩ := exists_real_cutoff_extension e μ he η hη f hf
  exact ⟨g, hg, realProjectedFunction_eq_of_mem e μ he η hη P hP g hm⟩

open Filter
open scoped Topology

theorem exists_convergent_projected_extensions {ι : Type*}
    (he : Isometry e) (η : ℝ) (hη : 0 < η)
    (Ps : ℕ → C(Z, ℂ) →L[ℂ] C(Z, ℂ)) (P : C(Z, ℂ) →L[ℂ] C(Z, ℂ))
    (hP : SpectralProjectionProperties (ambientOperator e μ) P η)
    (hconv : ∀ f, Tendsto (fun n ↦ Ps n f) atTop (𝓝 (P f)))
    (v : ι → C(X, ℝ)) (hv : ∀ i, v i ∈ spectralCutoff μ η) :
    ∃ g : ι → C(Z, ℝ), (∀ i, (g i).comp e = v i) ∧
      (∀ i, realProjectedFunction P (g i) = g i) ∧
      ∀ i, Tendsto (fun n ↦ realProjectedFunction (Ps n) (g i)) atTop (𝓝 (g i)) := by
  choose g hext hfix using fun i ↦ exists_real_projected_extension e μ he η hη P hP (v i) (hv i)
  refine ⟨g, hext, hfix, ?_⟩
  intro i
  simpa only [hfix i] using realProjectedFunction_tendsto Ps P hconv (g i)

end PaperN.PartII.AmbientKernel
