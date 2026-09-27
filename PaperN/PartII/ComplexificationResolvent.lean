import PaperN.PartII.RealComplexKernel
import PaperN.PartII.ComplexifiedSpectrum

namespace PaperN.PartII

/-- The inverse in the block definition in particular makes the block injective. -/
theorem complexResolventBlock_injective_of_not_mem
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (T : H →L[ℝ] H) (z : ℂ) (hz : z ∉ complexifiedSpectrum T) :
    Function.Injective (complexResolventBlock T z) := by
  obtain ⟨S, hl, _, _⟩ := (not_mem_complexifiedSpectrum_iff T z).mp hz
  intro x y h
  have hx := congrArg (fun A : (H × H) →L[ℝ] (H × H) ↦ A x) hl
  have hy := congrArg (fun A : (H × H) →L[ℝ] (H × H) ↦ A y) hl
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using
    hx.symm.trans ((congrArg S h).trans hy)

namespace ComplexKernel
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

/-- At a nonzero real parameter, a real-block complexification gap is a genuine
resolvent point of the complex L2 distance operator. No spectral input is added. -/
theorem ofReal_mem_resolventSet_of_not_mem_complexifiedSpectrum
    (a : ℝ) (ha : a ≠ 0)
    (hgap : (a : ℂ) ∉ complexifiedSpectrum (PaperN.PartII.distanceOperator μ)) :
    (a : ℂ) ∈ resolventSet ℂ (distanceOperator μ) := by
  by_contra h
  have hc := AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id
  have hs : (a : ℂ) ∈ spectrum ℂ (distanceOperator μ) := h
  have he := (hc.hasEigenvalue_iff_mem_spectrum (by exact_mod_cast ha)).mpr hs
  obtain ⟨f, hf, hne⟩ := he.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff] at hf
  have hf' : distanceOperator μ f = (a : ℂ) • f := hf
  have hr := realPart_eigenvector μ a f hf'
  have hi := imagPart_eigenvector μ a f hf'
  have hz : complexResolventBlock (PaperN.PartII.distanceOperator μ) (a : ℂ)
      (realPart μ f, imagPart μ f) = 0 := by
    ext <;> simp [complexResolventBlock, hr, hi]
  have hp : (realPart μ f, imagPart μ f) = 0 :=
    complexResolventBlock_injective_of_not_mem _ _ hgap (hz.trans (map_zero _).symm)
  have hr0 : realPart μ f = 0 := congrArg Prod.fst hp
  have hi0 : imagPart μ f = 0 := congrArg Prod.snd hp
  apply hne
  have hh := realEmbed_parts μ f
  simpa only [hr0, hi0, map_zero, smul_zero, add_zero] using hh.symm

end ComplexKernel
end PaperN.PartII
