import PaperN.PartII.AmbientCompact
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace PaperN.PartII.ComplexKernel
open MeasureTheory Metric Set
open scoped ComplexConjugate
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem distancePair_integrable (f g : Lp ℂ 2 μ) :
    Integrable (fun p : X × X ↦ (dist p.1 p.2 : ℂ) * (star (f p.1) * g p.2)) (μ.prod μ) := by
  have hf : Integrable (fun x ↦ star (f x)) μ := by
    simpa [RCLike.inner_apply] using
      (MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp f)).inner_const (𝕜 := ℂ) 1
  have hg : Integrable g μ := MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (Lp.memLp g)
  apply (hf.mul_prod hg).bdd_mul (c := diam (univ : Set X))
  · exact (Complex.continuous_ofReal.comp (continuous_fst.dist continuous_snd)).aestronglyMeasurable
  · filter_upwards [] with p
    simpa using dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ p.1) (mem_univ p.2)

theorem distanceOperator_symmetric : (distanceOperator μ).toLinearMap.IsSymmetric := by
  intro f g
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ x, inner ℂ ((distanceOperator μ) f x) (g x) ∂μ) =
        ∫ x, ∫ y, (dist x y : ℂ) * (star (f y) * g x) ∂μ ∂μ := by
      apply integral_congr_ae
      filter_upwards [distanceOperator_ae μ f] with x hx
      rw [hx]
      simp only [RCLike.inner_apply, ← integral_conj, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp [mul_comm, mul_left_comm]
    _ = ∫ y, ∫ x, (dist x y : ℂ) * (star (f y) * g x) ∂μ ∂μ := by
      apply integral_integral_swap
      have h := (distancePair_integrable μ f g).swap
      convert h using 1
      funext p
      simp only [Function.uncurry, Function.comp_apply, Prod.swap, dist_comm]
    _ = ∫ y, inner ℂ (f y) ((distanceOperator μ) g y) ∂μ := by
      apply integral_congr_ae
      filter_upwards [distanceOperator_ae μ g] with y hy
      rw [hy]
      simp only [RCLike.inner_apply, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [dist_comm, mul_comm, mul_assoc]

theorem distanceOperator_selfAdjoint : IsSelfAdjoint (distanceOperator μ) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (distanceOperator_symmetric μ)

theorem distanceOperator_opNorm_le : ‖distanceOperator μ‖ ≤ diam (univ : Set X) :=
  ContinuousLinearMap.opNorm_le_bound _ diam_nonneg (distanceOperator_norm_le μ)

theorem distanceOperator_spectrum_bound {a : ℂ} (ha : a ∈ spectrum ℂ (distanceOperator μ)) :
    a.im = 0 ∧ ‖a‖ ≤ diam (univ : Set X) := by
  have hr : a.im = 0 := by
    by_cases hz : a = 0
    · simp [hz]
    · have hc := AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ (by exact isometry_id)
      have he := (hc.hasEigenvalue_iff_mem_spectrum hz).mpr ha
      have h := (distanceOperator_symmetric μ).conj_eigenvalue_eq_self he
      have hi := congrArg Complex.im h
      simp only [Complex.conj_im] at hi
      linarith
  refine ⟨hr, ?_⟩
  have h := spectrum.norm_le_norm_mul_of_mem ha
  have hi : ‖(1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  exact h.trans ((mul_le_of_le_one_right (norm_nonneg _) hi).trans (distanceOperator_opNorm_le μ))

end PaperN.PartII.ComplexKernel

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z)) (μ : Measure X) [IsProbabilityMeasure μ]

theorem restriction_extension_symmetric (he : Isometry e) :
    ((restriction e μ).toLinearMap.comp (distanceToContinuous e μ).toLinearMap).IsSymmetric := by
  change ((restriction e μ).comp (distanceToContinuous e μ)).toLinearMap.IsSymmetric
  rw [restriction_extension e μ he]
  exact ComplexKernel.distanceOperator_symmetric μ

theorem ambient_power_kernel (he : Isometry e) (a : ℂ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    LinearMap.ker (((ambientOperator e μ).toLinearMap - a • 1)^n) =
      LinearMap.ker ((ambientOperator e μ).toLinearMap - a • 1) :=
  factor_symmetric_power_kernel (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap (restriction_extension_symmetric e μ he) a ha n hn

theorem ambient_maxGenEigenspace (he : Isometry e) (a : ℂ) (ha : a ≠ 0) :
    Module.End.maxGenEigenspace (ambientOperator e μ).toLinearMap a =
      Module.End.eigenspace (ambientOperator e μ).toLinearMap a :=
  factor_symmetric_maxGenEigenspace (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap (restriction_extension_symmetric e μ he) a ha

theorem ambient_spectrum_interval (he : Isometry e) {a : ℂ}
    (ha : a ∈ spectrum ℂ (ambientOperator e μ)) :
    a.im = 0 ∧ -(diam (univ : Set Z)) ≤ a.re ∧ a.re ≤ diam (univ : Set Z) := by
  by_cases hz : a = 0
  · simp [hz, diam_nonneg]
  have ht : a ∈ spectrum ℂ (ComplexKernel.distanceOperator μ) := by
    have h : a ∈ spectrum ℂ (ambientOperator e μ) \ {0} := ⟨ha, hz⟩
    rw [ambient_nonzero_spectrum_eq e μ he] at h
    exact h.1
  obtain ⟨hr, hb⟩ := ComplexKernel.distanceOperator_spectrum_bound μ ht
  have hd : diam (univ : Set X) ≤ diam (univ : Set Z) := by
    rw [← he.diam_image (univ : Set X)]
    exact diam_mono (subset_univ _) isCompact_univ.isBounded
  exact ⟨hr, (abs_le.mp (Complex.abs_re_le_norm a |>.trans (hb.trans hd))).1,
    (abs_le.mp (Complex.abs_re_le_norm a |>.trans (hb.trans hd))).2⟩

end PaperN.PartII.AmbientKernel
