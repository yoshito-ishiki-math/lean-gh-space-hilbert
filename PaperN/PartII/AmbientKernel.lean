import PaperN.PartII.ComplexDistanceKernel
import PaperN.PartII.FactorEigenspaces

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Metric Set
open scoped NNReal
universe u v
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {Z : Type v} [MetricSpace Z] [CompactSpace Z]
variable (e : C(X, Z))
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The distance function from one point, as a continuous function. -/
def distanceProfile (x : Z) : C(X, ℂ) := ⟨fun y ↦ (dist x (e y) : ℂ), Complex.continuous_ofReal.comp (continuous_const.dist e.continuous)⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem distanceProfile_norm_le (x : Z) : ‖distanceProfile e x‖ ≤ diam (univ : Set Z) := by
  apply (ContinuousMap.norm_le _ diam_nonneg).mpr
  intro y
  exact (by simpa [distanceProfile, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ (e y)))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace Z] in
theorem distanceProfile_sub_norm_le (x y : Z) :
    ‖distanceProfile e x - distanceProfile e y‖ ≤ dist x y := by
  apply (ContinuousMap.norm_le _ dist_nonneg).mpr
  intro z
  simpa [distanceProfile, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using abs_dist_sub_le x y (e z)

noncomputable def distanceProfileL2 (x : Z) : Lp ℂ 2 μ := ComplexKernel.continuousToL2 μ (distanceProfile e x)

theorem distanceProfileL2_norm_le (x : Z) : ‖distanceProfileL2 e μ x‖ ≤ diam (univ : Set Z) :=
  (ComplexKernel.continuousToL2_norm_le μ _).trans (distanceProfile_norm_le e x)

omit [CompactSpace Z] in
theorem distanceProfileL2_sub_norm_le (x y : Z) :
    ‖distanceProfileL2 e μ x - distanceProfileL2 e μ y‖ ≤ dist x y := by
  change ‖ComplexKernel.continuousToL2 μ (distanceProfile e x) - ComplexKernel.continuousToL2 μ (distanceProfile e y)‖ ≤ _
  rw [← map_sub]
  exact (ComplexKernel.continuousToL2_norm_le μ _).trans (distanceProfile_sub_norm_le e x y)

/-- L² inner products make independence of representatives part of the definition. -/
noncomputable def distanceValue (f : Lp ℂ 2 μ) (x : Z) : ℂ := inner ℂ (distanceProfileL2 e μ x) f

theorem distanceValue_bound (f : Lp ℂ 2 μ) (x : Z) :
    ‖distanceValue e μ f x‖ ≤ diam (univ : Set Z) * ‖f‖ := by
  simpa only [distanceValue, Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℂ) (distanceProfileL2 e μ x) f).trans (mul_le_mul_of_nonneg_right (distanceProfileL2_norm_le e μ x) (norm_nonneg f))

omit [CompactSpace Z] in
theorem distanceValue_sub_bound (f : Lp ℂ 2 μ) (x y : Z) :
    ‖distanceValue e μ f x - distanceValue e μ f y‖ ≤ dist x y * ‖f‖ := by
  unfold distanceValue
  rw [← inner_sub_left]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right (distanceProfileL2_sub_norm_le e μ x y) (norm_nonneg f))

omit [CompactSpace Z] in
theorem distanceValue_lipschitz (f : Lp ℂ 2 μ) : LipschitzWith ‖f‖₊ (distanceValue e μ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm, mul_comm] using distanceValue_sub_bound e μ f x y

noncomputable def distanceContinuous (f : Lp ℂ 2 μ) : C(Z, ℂ) :=
  ⟨distanceValue e μ f, (distanceValue_lipschitz e μ f).continuous⟩

theorem distanceContinuous_norm_le (f : Lp ℂ 2 μ) :
    ‖distanceContinuous e μ f‖ ≤ diam (univ : Set Z) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg diam_nonneg (norm_nonneg f))).mpr
  exact distanceValue_bound e μ f

noncomputable def distanceToContinuous : Lp ℂ 2 μ →L[ℂ] C(Z, ℂ) :=
  LinearMap.mkContinuous {
    toFun := distanceContinuous e μ
    map_add' := by
      intro f g; ext x
      change inner ℂ _ (f+g) = inner ℂ _ f + inner ℂ _ g
      exact inner_add_right _ _ _
    map_smul' := by
      intro a f; ext x
      change inner ℂ _ (a • f) = a * inner ℂ _ f
      exact inner_smul_right _ _ _ }
    (diam (univ : Set Z)) (distanceContinuous_norm_le e μ)


omit [CompactSpace Z] in
theorem distanceValue_integral (f : Lp ℂ 2 μ) (z : Z) :
    distanceValue e μ f z = ∫ y, (dist z (e y) : ℂ) * f y ∂μ := by
  rw [distanceValue, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(distanceProfile e z).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with y hy
  change (distanceProfileL2 e μ z) y = (dist z (e y) : ℂ) at hy
  change inner ℂ ((distanceProfileL2 e μ z) y) (f y) = _
  simp [hy, mul_comm]

omit [CompactSpace Z] in
theorem distanceIntegrand_integrable (f : Lp ℂ 2 μ) (z : Z) :
    Integrable (fun y ↦ (dist z (e y) : ℂ) * f y) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (distanceProfileL2 e μ z) f).congr
  filter_upwards [(distanceProfile e z).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with y hy
  change (distanceProfileL2 e μ z) y = (dist z (e y) : ℂ) at hy
  simp [hy, mul_comm]

omit [CompactSpace Z] in
theorem distanceValue_integral_of_ae (f : Lp ℂ 2 μ) (g : X → ℂ)
    (hg : g =ᵐ[μ] f) (z : Z) :
    distanceValue e μ f z = ∫ y, (dist z (e y) : ℂ) * g y ∂μ := by
  rw [distanceValue_integral]
  apply integral_congr_ae
  filter_upwards [hg] with y hy
  rw [hy]

omit [MeasurableSpace X] [BorelSpace X] in
theorem restrictionContinuous_norm_le (f : C(Z, ℂ)) : ‖f.comp e‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact ContinuousMap.norm_coe_le_norm f (e x)

noncomputable def restrictionContinuous : C(Z, ℂ) →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous {
    toFun := fun f ↦ f.comp e
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
    1 (by intro f; simpa using restrictionContinuous_norm_le e f)

noncomputable def restriction : C(Z, ℂ) →L[ℂ] Lp ℂ 2 μ :=
  (ComplexKernel.continuousToL2 μ).comp (restrictionContinuous e)

theorem restriction_norm_le (f : C(Z, ℂ)) : ‖restriction e μ f‖ ≤ ‖f‖ :=
  (ComplexKernel.continuousToL2_norm_le μ _).trans (restrictionContinuous_norm_le e f)

noncomputable def ambientOperator : C(Z, ℂ) →L[ℂ] C(Z, ℂ) :=
  (distanceToContinuous e μ).comp (restriction e μ)

theorem restriction_extension (he : Isometry e) :
    (restriction e μ).comp (distanceToContinuous e μ) = ComplexKernel.distanceOperator μ := by
  have hp (x : X) : distanceProfile e (e x) = ComplexKernel.distanceProfile x := by
    ext y
    exact congrArg (fun r : ℝ ↦ (r : ℂ)) (he.dist_eq x y)
  apply ContinuousLinearMap.ext
  intro f
  change ComplexKernel.continuousToL2 μ ((distanceContinuous e μ f).comp e) =
    ComplexKernel.continuousToL2 μ (ComplexKernel.distanceContinuous μ f)
  congr 1
  ext x
  change inner ℂ (ComplexKernel.continuousToL2 μ (distanceProfile e (e x))) f =
    inner ℂ (ComplexKernel.continuousToL2 μ (ComplexKernel.distanceProfile x)) f
  rw [hp]

theorem restriction_intertwine (he : Isometry e) (f : C(Z, ℂ)) :
    restriction e μ (ambientOperator e μ f) =
      ComplexKernel.distanceOperator μ (restriction e μ f) := by
  change ((restriction e μ).comp (distanceToContinuous e μ)) (restriction e μ f) = _
  rw [restriction_extension e μ he]

theorem ambientOperator_integral (f : C(Z, ℂ)) (z : Z) :
    ambientOperator e μ f z = ∫ y, (dist z (e y) : ℂ) * f (e y) ∂μ := by
  change distanceValue e μ (restriction e μ f) z = _
  apply distanceValue_integral_of_ae
  exact ((f.comp e).coeFn_toLp (p := 2) (𝕜 := ℂ) μ).symm

theorem ambient_hasEigenvalue_iff (he : Isometry e) (a : ℂ) (ha : a ≠ 0) :
    Module.End.HasEigenvalue (ambientOperator e μ).toLinearMap a ↔
      Module.End.HasEigenvalue (ComplexKernel.distanceOperator μ).toLinearMap a := by
  have h := factor_hasEigenvalue_iff (distanceToContinuous e μ).toLinearMap
    (restriction e μ).toLinearMap a ha
  change Module.End.HasEigenvalue (ambientOperator e μ).toLinearMap a ↔
    Module.End.HasEigenvalue ((restriction e μ).comp (distanceToContinuous e μ)).toLinearMap a at h
  rwa [restriction_extension e μ he] at h

end PaperN.PartII.AmbientKernel
