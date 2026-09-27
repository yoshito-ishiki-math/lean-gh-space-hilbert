import PaperN.PartII.AmbientRealProjection

namespace PaperN.PartII.ComplexKernel
open MeasureTheory
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The continuous complex cutoff, with its inherited complex vector space structure. -/
noncomputable def continuousComplexCutoff (η : ℝ) : Submodule ℂ C(X, ℂ) :=
  (complexAlgebraicCutoff (distanceOperator μ) η).comap (continuousToL2 μ).toLinearMap

variable [μ.IsOpenPosMeasure]

theorem mem_continuousComplexCutoff_iff {η : ℝ} (hη : 0 < η) (f : C(X, ℂ)) :
    f ∈ continuousComplexCutoff μ η ↔
      ∃ u ∈ spectralCutoff μ η, ∃ v ∈ spectralCutoff μ η,
        f = continuousRealEmbed u + Complex.I • continuousRealEmbed v := by
  change continuousToL2 μ f ∈ complexAlgebraicCutoff (distanceOperator μ) η ↔ _
  rw [mem_complexCutoff_iff_continuous_real_imag μ hη]
  constructor
  · rintro ⟨u, hu, v, hv, he⟩
    refine ⟨u, hu, v, hv, continuousToL2_injective μ ?_⟩
    simpa only [map_add, map_smul, continuousToL2_realEmbed] using he
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨u, hu, v, hv, by simp only [map_add, map_smul, continuousToL2_realEmbed]⟩

noncomputable def continuousCutoffEquiv {η : ℝ} (hη : 0 < η) :
    continuousComplexCutoff μ η ≃ₗ[ℂ] complexAlgebraicCutoff (distanceOperator μ) η := by
  let L : continuousComplexCutoff μ η →ₗ[ℂ] complexAlgebraicCutoff (distanceOperator μ) η :=
    ((continuousToL2 μ).toLinearMap.comp (continuousComplexCutoff μ η).subtype).codRestrict _
      (fun f ↦ f.property)
  apply LinearEquiv.ofBijective L
  constructor
  · intro f g h
    exact Subtype.ext (continuousToL2_injective μ (congrArg Subtype.val h))
  · intro f
    obtain ⟨u, hu, v, hv, he⟩ :=
      (mem_complexCutoff_iff_continuous_real_imag μ hη f).mp f.property
    let g := continuousRealEmbed u + Complex.I • continuousRealEmbed v
    have hg : continuousToL2 μ g = f := by
      simpa only [g, map_add, map_smul, continuousToL2_realEmbed] using he.symm
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change continuousToL2 μ g ∈ complexAlgebraicCutoff (distanceOperator μ) η
    rw [hg]
    exact f.property

theorem continuousCutoffEquiv_apply {η : ℝ} (hη : 0 < η)
    (f : continuousComplexCutoff μ η) :
    (continuousCutoffEquiv μ hη f : Lp ℂ 2 μ) = continuousToL2 μ f := rfl

theorem continuousCutoffEquiv_symm_toL2 {η : ℝ} (hη : 0 < η)
    (f : complexAlgebraicCutoff (distanceOperator μ) η) :
    continuousToL2 μ ((continuousCutoffEquiv μ hη).symm f) = f :=
  congrArg Subtype.val ((continuousCutoffEquiv μ hη).apply_symm_apply f)

end PaperN.PartII.ComplexKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory ComplexKernel
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]

noncomputable def restrictionContinuousCircleRangeEquiv
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ)) :
    LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap ≃ₗ[ℂ]
      continuousComplexCutoff μ η :=
  (restrictionCircleRangeEquiv e μ  he η B hη hB hd hp hn).trans
    (continuousCutoffEquiv μ hη).symm

theorem restrictionContinuousCircleRangeEquiv_apply
    (he : Isometry e) (η B : ℝ) (hη : 0 < η) (hB : η < B)
    (hd : Metric.diam (Set.univ : Set X) < B)
    (hp : (η : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (hn : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ (ComplexKernel.distanceOperator μ))
    (f : LinearMap.range (cutoffCircleOperator (ambientOperator e μ) η B).toLinearMap) :
    (restrictionContinuousCircleRangeEquiv e μ  he η B hη hB hd hp hn f : C(X, ℂ)) =
      (f : C(Z, ℂ)).comp e := by
  apply ComplexKernel.continuousToL2_injective μ
  exact continuousCutoffEquiv_symm_toL2 μ hη _

end PaperN.PartII.AmbientKernel
