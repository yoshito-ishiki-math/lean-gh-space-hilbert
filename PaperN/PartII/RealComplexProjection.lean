import PaperN.PartII.CutoffComplexification

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

theorem inner_realEmbed (f g : Lp ℝ 2 μ) :
    inner ℂ (realEmbed μ f) (realEmbed μ g) = (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [realEmbed_ae μ f, realEmbed_ae μ g] with x hf hg
  simp [hf, hg, RCLike.inner_apply]

variable [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ]

theorem cutoff_starProjection_realEmbed (η : ℝ)
    [(l2SpectralCutoff μ η).HasOrthogonalProjection]
    [(complexAlgebraicCutoff (distanceOperator μ) η).HasOrthogonalProjection]
    (f : Lp ℝ 2 μ) :
    (complexAlgebraicCutoff (distanceOperator μ) η).starProjection (realEmbed μ f) =
      realEmbed μ ((l2SpectralCutoff μ η).starProjection f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact realEmbed_mem_complexCutoff μ η _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := (mem_complexCutoff_iff_real_imag μ η w).mp hw
    rw [← map_sub, inner_add_right, inner_smul_right, inner_realEmbed, inner_realEmbed,
      Submodule.starProjection_inner_eq_zero _ _ hu,
      Submodule.starProjection_inner_eq_zero _ _ hv]
    simp

theorem cutoff_starProjection_real_imag (η : ℝ)
    [(l2SpectralCutoff μ η).HasOrthogonalProjection]
    [(complexAlgebraicCutoff (distanceOperator μ) η).HasOrthogonalProjection]
    (f : Lp ℂ 2 μ) :
    (complexAlgebraicCutoff (distanceOperator μ) η).starProjection f =
      realEmbed μ ((l2SpectralCutoff μ η).starProjection (realPart μ f)) +
      Complex.I • realEmbed μ ((l2SpectralCutoff μ η).starProjection (imagPart μ f)) := by
  conv_lhs => rw [← realEmbed_parts μ f]
  rw [map_add, map_smul, cutoff_starProjection_realEmbed, cutoff_starProjection_realEmbed]

theorem realCutoff_finiteDimensional (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) : FiniteDimensional ℝ (l2SpectralCutoff μ η) := by
  letI complexFinite := distance_complexAlgebraicCutoff_finiteDimensional μ hf η hη
  letI realFinite : FiniteDimensional ℝ (complexAlgebraicCutoff (distanceOperator μ) η) :=
    FiniteDimensional.trans ℝ ℂ _
  let L : l2SpectralCutoff μ η →ₗ[ℝ] complexAlgebraicCutoff (distanceOperator μ) η :=
    ((realEmbed μ).toLinearMap.comp (l2SpectralCutoff μ η).subtype).codRestrict
      ((complexAlgebraicCutoff (distanceOperator μ) η).restrictScalars ℝ)
      (fun f ↦ realEmbed_mem_complexCutoff μ η f f.property)
  apply FiniteDimensional.of_injective L
  intro f g h
  apply Subtype.ext
  exact realEmbed_injective μ (congrArg Subtype.val h)

/-- The manuscript real orthogonal cutoff, constructed from the existing finiteness input. -/
noncomputable def realCutoffProjection (hf : CompactEigenvalueFinitenessInput.{u})
    (η : ℝ) (hη : 0 < η) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := by
  letI finiteCutoff := realCutoff_finiteDimensional μ hf η hη
  exact (l2SpectralCutoff μ η).starProjection

theorem distance_cutoffCircle_realEmbed (hf : CompactEigenvalueFinitenessInput.{u})
    (η B : ℝ) (hη : 0 < η) (hB : η < B) (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) (f : Lp ℝ 2 μ) :
    cutoffCircleOperator (distanceOperator μ) η B (realEmbed μ f) =
      realEmbed μ (realCutoffProjection μ hf η hη f) := by
  letI realFinite := realCutoff_finiteDimensional μ hf η hη
  letI complexFinite := distance_complexAlgebraicCutoff_finiteDimensional μ hf η hη
  rw [distance_cutoffCircle_eq_starProjection μ η B hη hB hd hp hn]
  have he := closedEigenSpan_cutoff_eq_algebraic hf (distanceOperator μ)
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) η hη
  simp only [he]
  exact cutoff_starProjection_realEmbed μ η f

theorem distance_cutoffCircle_real_imag (hf : CompactEigenvalueFinitenessInput.{u})
    (η B : ℝ) (hη : 0 < η) (hB : η < B) (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) (f : Lp ℂ 2 μ) :
    cutoffCircleOperator (distanceOperator μ) η B f =
      realEmbed μ (realCutoffProjection μ hf η hη (realPart μ f)) +
      Complex.I • realEmbed μ (realCutoffProjection μ hf η hη (imagPart μ f)) := by
  conv_lhs => rw [← realEmbed_parts μ f]
  rw [map_add, map_smul, distance_cutoffCircle_realEmbed μ hf η B hη hB hd hp hn,
    distance_cutoffCircle_realEmbed μ hf η B hη hB hd hp hn]

theorem distance_cutoffCircle_preserves_real (hf : CompactEigenvalueFinitenessInput.{u})
    (η B : ℝ) (hη : 0 < η) (hB : η < B) (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (distanceOperator μ)) (f : Lp ℝ 2 μ) :
    imagPart μ (cutoffCircleOperator (distanceOperator μ) η B (realEmbed μ f)) = 0 := by
  rw [distance_cutoffCircle_realEmbed μ hf η B hη hB hd hp hn, imagPart_realEmbed]

end PaperN.PartII.ComplexKernel
