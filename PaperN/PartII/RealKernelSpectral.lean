import PaperN.PartII.RealComplexKernel
import PaperN.PartII.DistanceOperatorStatements

namespace PaperN.PartII
open MeasureTheory
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- The real kernel operator is a continuous real-part factor of the complex one. -/
theorem distanceOperator_real_factorization :
    distanceOperator μ = (ComplexKernel.realPart μ).comp
      (((ComplexKernel.distanceOperator μ).restrictScalars ℝ).comp (ComplexKernel.realEmbed μ)) := by
  apply ContinuousLinearMap.ext
  intro f
  change distanceOperator μ f = ComplexKernel.realPart μ
    (ComplexKernel.distanceOperator μ (ComplexKernel.realEmbed μ f))
  rw [ComplexKernel.distanceOperator_realPart, ComplexKernel.realPart_realEmbed]

/-- Compactness of the real operator is proved from the already-proved complex operator. -/
theorem distanceOperator_compact_proved : IsCompactOperator (distanceOperator μ) := by
  rw [distanceOperator_real_factorization]
  have hc : IsCompactOperator ((ComplexKernel.distanceOperator μ).restrictScalars ℝ) :=
    AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id
  exact (hc.comp_clm (ComplexKernel.realEmbed μ)).clm_comp (ComplexKernel.realPart μ)

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsProbabilityMeasure μ] in
/-- Real embedding preserves the L2 inner product. -/
theorem realEmbed_inner (f g : Lp ℝ 2 μ) :
    inner ℂ (ComplexKernel.realEmbed μ f) (ComplexKernel.realEmbed μ g) =
      (inner ℝ f g : ℂ) := by
  rw [L2.inner_def, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ComplexKernel.realEmbed_ae μ f, ComplexKernel.realEmbed_ae μ g] with x hf hg
  simp [hf, hg, RCLike.inner_apply]

/-- Self-adjointness descends along the real embedding. -/
theorem distanceOperator_selfAdjoint_proved : IsSelfAdjoint (distanceOperator μ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have h := ComplexKernel.distanceOperator_symmetric μ
    (ComplexKernel.realEmbed μ f) (ComplexKernel.realEmbed μ g)
  change inner ℂ (ComplexKernel.distanceOperator μ (ComplexKernel.realEmbed μ f))
      (ComplexKernel.realEmbed μ g) = inner ℂ (ComplexKernel.realEmbed μ f)
      (ComplexKernel.distanceOperator μ (ComplexKernel.realEmbed μ g)) at h
  rw [ComplexKernel.distanceOperator_realEmbed, ComplexKernel.distanceOperator_realEmbed,
    realEmbed_inner, realEmbed_inner] at h
  exact Complex.ofReal_injective h

/-- The formerly external real-kernel input now has a proof, in every universe. -/
theorem distanceKernelSpectralInput_proved : DistanceKernelSpectralInput := by
  intro X _ _ _ _ _ μ _
  exact ⟨distanceOperator_compact_proved μ, distanceOperator_selfAdjoint_proved μ⟩

end PaperN.PartII
