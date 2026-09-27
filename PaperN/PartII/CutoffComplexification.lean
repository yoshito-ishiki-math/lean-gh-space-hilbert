import PaperN.PartII.RealComplexKernel
import PaperN.PartII.ComplexCutoffFinite

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def complexifiedRealCutoff (η : ℝ) : Submodule ℂ (Lp ℂ 2 μ) :=
  Submodule.span ℂ ((realEmbed μ) '' (l2SpectralCutoff μ η : Set (Lp ℝ 2 μ)))

theorem realEmbed_mem_complexCutoff (η : ℝ) (f : Lp ℝ 2 μ) (hf : f ∈ l2SpectralCutoff μ η) :
    realEmbed μ f ∈ complexAlgebraicCutoff (distanceOperator μ) η := by
  have hle : l2SpectralCutoff μ η ≤
      ((complexAlgebraicCutoff (distanceOperator μ) η).restrictScalars ℝ).comap
        (realEmbed μ).toLinearMap := by
    apply iSup_le
    intro a
    apply iSup_le
    intro ha g hg
    have he := Module.End.mem_eigenspace_iff.mp hg
    change PaperN.PartII.distanceOperator μ g = a • g at he
    have hv : realEmbed μ g ∈ Module.End.eigenspace (distanceOperator μ).toLinearMap (a : ℂ) :=
      Module.End.mem_eigenspace_iff.mpr (realEmbed_eigenvector μ a g he)
    have hb : η < ‖(a : ℂ)‖ := by simpa using ha
    have hi : Module.End.eigenspace (distanceOperator μ).toLinearMap (a : ℂ) ≤
        complexAlgebraicCutoff (distanceOperator μ) η :=
      le_iSup_of_le (a : ℂ) (le_iSup_of_le hb le_rfl)
    exact hi hv
  exact hle hf

theorem complexCutoff_eq_complexification (η : ℝ) :
    complexAlgebraicCutoff (distanceOperator μ) η = complexifiedRealCutoff μ η := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha f hf
    by_cases hzero : f = 0
    · simp [hzero]
    have heig : Module.End.HasEigenvalue (distanceOperator μ).toLinearMap a :=
      Module.End.hasEigenvalue_of_hasEigenvector ⟨hf,hzero⟩
    have hc := (distanceOperator_symmetric μ).conj_eigenvalue_eq_self heig
    have hre : a.im = 0 := by
      have hi := congrArg Complex.im hc
      simp only [Complex.conj_im] at hi
      linarith
    have he : a = (a.re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hre
    have hanorm : ‖a‖ = |a.re| := by
      calc ‖a‖ = ‖(a.re : ℂ)‖ := congrArg norm he
           _ = |a.re| := by simp
    have hv := Module.End.mem_eigenspace_iff.mp hf
    change distanceOperator μ f = a • f at hv
    rw [he] at hv
    have hcut : Module.End.eigenspace (PaperN.PartII.distanceOperator μ).toLinearMap a.re ≤
        l2SpectralCutoff μ η :=
      le_iSup_of_le a.re (le_iSup_of_le (show η < |a.re| by rwa [← hanorm]) le_rfl)
    have hr : realPart μ f ∈ l2SpectralCutoff μ η :=
      hcut (Module.End.mem_eigenspace_iff.mpr (realPart_eigenvector μ a.re f hv))
    have hi : imagPart μ f ∈ l2SpectralCutoff μ η :=
      hcut (Module.End.mem_eigenspace_iff.mpr (imagPart_eigenvector μ a.re f hv))
    have h₁ : realEmbed μ (realPart μ f) ∈ complexifiedRealCutoff μ η :=
      Submodule.subset_span ⟨realPart μ f,hr,rfl⟩
    have h₂ : realEmbed μ (imagPart μ f) ∈ complexifiedRealCutoff μ η :=
      Submodule.subset_span ⟨imagPart μ f,hi,rfl⟩
    rw [← realEmbed_parts μ f]
    exact (complexifiedRealCutoff μ η).add_mem h₁ ((complexifiedRealCutoff μ η).smul_mem _ h₂)
  · apply Submodule.span_le.mpr
    rintro f ⟨g,hg,rfl⟩
    exact realEmbed_mem_complexCutoff μ η g hg
theorem parts_mem_of_mem_complexification (η : ℝ) (f : Lp ℂ 2 μ)
    (hf : f ∈ complexifiedRealCutoff μ η) :
    realPart μ f ∈ l2SpectralCutoff μ η ∧ imagPart μ f ∈ l2SpectralCutoff μ η := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨g,hg,rfl⟩ := hf
    rw [realPart_realEmbed, imagPart_realEmbed]
    exact ⟨hg, (l2SpectralCutoff μ η).zero_mem⟩
  | zero => simp
  | add f g _ _ hf hg =>
    simpa only [map_add] using And.intro
      ((l2SpectralCutoff μ η).add_mem hf.1 hg.1)
      ((l2SpectralCutoff μ η).add_mem hf.2 hg.2)
  | smul a f _ hf =>
    rw [realPart_complex_smul, imagPart_complex_smul]
    exact ⟨(l2SpectralCutoff μ η).sub_mem
      ((l2SpectralCutoff μ η).smul_mem _ hf.1) ((l2SpectralCutoff μ η).smul_mem _ hf.2),
      (l2SpectralCutoff μ η).add_mem
      ((l2SpectralCutoff μ η).smul_mem _ hf.2) ((l2SpectralCutoff μ η).smul_mem _ hf.1)⟩

theorem mem_complexCutoff_iff_real_imag (η : ℝ) (f : Lp ℂ 2 μ) :
    f ∈ complexAlgebraicCutoff (distanceOperator μ) η ↔
      ∃ u ∈ l2SpectralCutoff μ η, ∃ v ∈ l2SpectralCutoff μ η,
        f = realEmbed μ u + Complex.I • realEmbed μ v := by
  rw [complexCutoff_eq_complexification]
  constructor
  · intro hf
    obtain ⟨hr,hi⟩ := parts_mem_of_mem_complexification μ η f hf
    exact ⟨realPart μ f,hr,imagPart μ f,hi,(realEmbed_parts μ f).symm⟩
  · rintro ⟨u,hu,v,hv,rfl⟩
    exact (complexifiedRealCutoff μ η).add_mem
      (Submodule.subset_span ⟨u,hu,rfl⟩)
      ((complexifiedRealCutoff μ η).smul_mem _ (Submodule.subset_span ⟨v,hv,rfl⟩))
/-- The real summands can be chosen in the manuscript's continuous cutoff space. -/
theorem mem_complexCutoff_iff_continuous_real_imag [μ.IsOpenPosMeasure]
    {η : ℝ} (hη : 0 < η) (f : Lp ℂ 2 μ) :
    f ∈ complexAlgebraicCutoff (distanceOperator μ) η ↔
      ∃ u ∈ spectralCutoff μ η, ∃ v ∈ spectralCutoff μ η,
        f = realEmbed μ (PaperN.PartII.continuousToL2 μ u) +
          Complex.I • realEmbed μ (PaperN.PartII.continuousToL2 μ v) := by
  rw [mem_complexCutoff_iff_real_imag]
  constructor
  · rintro ⟨u, hu, v, hv, h⟩
    rw [← spectralCutoff_map_eq μ hη] at hu hv
    obtain ⟨u', hu', heu⟩ := hu
    obtain ⟨v', hv', hev⟩ := hv
    change PaperN.PartII.continuousToL2 μ u' = u at heu
    change PaperN.PartII.continuousToL2 μ v' = v at hev
    exact ⟨u', hu', v', hv', by simpa only [heu, hev] using h⟩
  · rintro ⟨u, hu, v, hv, h⟩
    refine ⟨_, ?_, _, ?_, h⟩
    · rw [← spectralCutoff_map_eq μ hη]
      exact ⟨u, hu, rfl⟩
    · rw [← spectralCutoff_map_eq μ hη]
      exact ⟨v, hv, rfl⟩

end PaperN.PartII.ComplexKernel
