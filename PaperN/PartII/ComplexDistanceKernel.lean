import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Bounded

namespace PaperN.PartII.ComplexKernel
open MeasureTheory Metric Set
open scoped NNReal
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The distance function from one point, as a continuous function. -/
def distanceProfile (x : X) : C(X, ℂ) := ⟨fun y ↦ (dist x y : ℂ), Complex.continuous_ofReal.comp (continuous_const.dist continuous_id)⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem distanceProfile_norm_le (x : X) : ‖distanceProfile x‖ ≤ diam (univ : Set X) := by
  apply (ContinuousMap.norm_le _ diam_nonneg).mpr
  intro y
  exact (by simpa [distanceProfile, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))

omit [MeasurableSpace X] [BorelSpace X] in
theorem distanceProfile_sub_norm_le (x y : X) :
    ‖distanceProfile x - distanceProfile y‖ ≤ dist x y := by
  apply (ContinuousMap.norm_le _ dist_nonneg).mpr
  intro z
  simpa [distanceProfile, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using abs_dist_sub_le x y z

noncomputable def continuousToL2 : C(X, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ

theorem continuousToL2_norm_le (f : C(X, ℂ)) : ‖continuousToL2 μ f‖ ≤ ‖f‖ := by
  have h : ‖continuousToL2 μ‖ ≤ 1 := by
    simpa [continuousToL2, measureUnivNNReal] using (ContinuousMap.toLp_norm_le (E := ℂ) (𝕜 := ℂ) (p := 2) μ)
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg f])

noncomputable def distanceProfileL2 (x : X) : Lp ℂ 2 μ := continuousToL2 μ (distanceProfile x)

theorem distanceProfileL2_norm_le (x : X) : ‖distanceProfileL2 μ x‖ ≤ diam (univ : Set X) :=
  (continuousToL2_norm_le μ _).trans (distanceProfile_norm_le x)

theorem distanceProfileL2_sub_norm_le (x y : X) :
    ‖distanceProfileL2 μ x - distanceProfileL2 μ y‖ ≤ dist x y := by
  change ‖continuousToL2 μ (distanceProfile x) - continuousToL2 μ (distanceProfile y)‖ ≤ _
  rw [← map_sub]
  exact (continuousToL2_norm_le μ _).trans (distanceProfile_sub_norm_le x y)

/-- L² inner products make independence of representatives part of the definition. -/
noncomputable def distanceValue (f : Lp ℂ 2 μ) (x : X) : ℂ := inner ℂ (distanceProfileL2 μ x) f

theorem distanceValue_bound (f : Lp ℂ 2 μ) (x : X) :
    ‖distanceValue μ f x‖ ≤ diam (univ : Set X) * ‖f‖ := by
  simpa only [distanceValue, Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℂ) (distanceProfileL2 μ x) f).trans (mul_le_mul_of_nonneg_right (distanceProfileL2_norm_le μ x) (norm_nonneg f))

theorem distanceValue_sub_bound (f : Lp ℂ 2 μ) (x y : X) :
    ‖distanceValue μ f x - distanceValue μ f y‖ ≤ dist x y * ‖f‖ := by
  unfold distanceValue
  rw [← inner_sub_left]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans
    (mul_le_mul_of_nonneg_right (distanceProfileL2_sub_norm_le μ x y) (norm_nonneg f))

theorem distanceValue_lipschitz (f : Lp ℂ 2 μ) : LipschitzWith ‖f‖₊ (distanceValue μ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [dist_eq_norm, mul_comm] using distanceValue_sub_bound μ f x y

noncomputable def distanceContinuous (f : Lp ℂ 2 μ) : C(X, ℂ) :=
  ⟨distanceValue μ f, (distanceValue_lipschitz μ f).continuous⟩

theorem distanceContinuous_norm_le (f : Lp ℂ 2 μ) :
    ‖distanceContinuous μ f‖ ≤ diam (univ : Set X) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg diam_nonneg (norm_nonneg f))).mpr
  exact distanceValue_bound μ f

noncomputable def distanceToContinuous : Lp ℂ 2 μ →L[ℂ] C(X, ℂ) :=
  LinearMap.mkContinuous {
    toFun := distanceContinuous μ
    map_add' := by
      intro f g; ext x
      change inner ℂ _ (f+g) = inner ℂ _ f + inner ℂ _ g
      exact inner_add_right _ _ _
    map_smul' := by
      intro a f; ext x
      change inner ℂ _ (a • f) = a * inner ℂ _ f
      exact inner_smul_right _ _ _ }
    (diam (univ : Set X)) (distanceContinuous_norm_le μ)

noncomputable def distanceOperator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (continuousToL2 μ).comp (distanceToContinuous μ)

theorem distanceValue_integral (f : Lp ℂ 2 μ) (x : X) :
    distanceValue μ f x = ∫ y, (dist x y : ℂ) * f y ∂μ := by
  rw [distanceValue, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(distanceProfile x).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with y hy
  change inner ℂ ((distanceProfileL2 μ x) y) (f y) = _
  change (distanceProfileL2 μ x) y = dist x y at hy
  simp [hy, mul_comm]

theorem distanceIntegrand_integrable (f : Lp ℂ 2 μ) (x : X) :
    Integrable (fun y ↦ (dist x y : ℂ) * f y) μ := by
  apply (L2.integrable_inner (𝕜 := ℂ) (distanceProfileL2 μ x) f).congr
  filter_upwards [(distanceProfile x).coeFn_toLp (p := 2) (𝕜 := ℂ) μ] with y hy
  change (distanceProfileL2 μ x) y = dist x y at hy
  simp [hy, mul_comm]

theorem distanceValue_integral_of_ae (f : Lp ℂ 2 μ) (g : X → ℂ)
    (hg : g =ᵐ[μ] f) (x : X) : distanceValue μ f x = ∫ y, (dist x y : ℂ) * g y ∂μ := by
  rw [distanceValue_integral]
  apply integral_congr_ae
  filter_upwards [hg] with y hy
  rw [hy]

theorem distanceOperator_ae (f : Lp ℂ 2 μ) :
    (distanceOperator μ f : X → ℂ) =ᵐ[μ] (fun x ↦ ∫ y, (dist x y : ℂ) * f y ∂μ) := by
  have h := (distanceContinuous μ f).coeFn_toLp (p := 2) (𝕜 := ℂ) μ
  filter_upwards [h] with x hx
  exact hx.trans (distanceValue_integral μ f x)

theorem distanceOperator_norm_le (f : Lp ℂ 2 μ) :
    ‖distanceOperator μ f‖ ≤ diam (univ : Set X) * ‖f‖ :=
  (continuousToL2_norm_le μ _).trans (distanceContinuous_norm_le μ f)

/-- Full support promotes equality in L² to equality of continuous representatives. -/
theorem continuousToL2_injective [μ.IsOpenPosMeasure] : Function.Injective (continuousToL2 μ) :=
  ContinuousMap.toLp_injective μ

/-- Every nonzero eigenvector has a unique continuous representative. -/
theorem eigenfunction_continuousRepresentative [μ.IsOpenPosMeasure]
    (f : Lp ℂ 2 μ) (a : ℂ) (ha : a ≠ 0) (hf : distanceOperator μ f = a • f) :
    ∃! g : C(X, ℂ), continuousToL2 μ g = f := by
  refine ⟨a⁻¹ • distanceToContinuous μ f, ?_, ?_⟩
  · change continuousToL2 μ (a⁻¹ • distanceToContinuous μ f) = f
    rw [map_smul]
    change a⁻¹ • distanceOperator μ f = f
    rw [hf, smul_smul, inv_mul_cancel₀ ha, one_smul]
  · intro g hg
    apply continuousToL2_injective μ
    rw [map_smul]
    change continuousToL2 μ g = a⁻¹ • distanceOperator μ f
    rw [hg, hf, smul_smul, inv_mul_cancel₀ ha, one_smul]
/-- The continuous-function realization on the same compact carrier. -/
noncomputable def continuousDistanceOperator : C(X, ℂ) →L[ℂ] C(X, ℂ) :=
  (distanceToContinuous μ).comp (continuousToL2 μ)

theorem continuousDistanceOperator_integral (f : C(X, ℂ)) (x : X) :
    continuousDistanceOperator μ f x = ∫ y, (dist x y : ℂ) * f y ∂μ := by
  change distanceValue μ (continuousToL2 μ f) x = _
  apply distanceValue_integral_of_ae
  exact (f.coeFn_toLp (p := 2) (𝕜 := ℂ) μ).symm

theorem distanceOperator_intertwine (f : C(X, ℂ)) :
    continuousToL2 μ (continuousDistanceOperator μ f) =
      distanceOperator μ (continuousToL2 μ f) := rfl

end PaperN.PartII.ComplexKernel
