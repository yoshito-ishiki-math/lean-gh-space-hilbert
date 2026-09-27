import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.MetricSpace.Bounded

namespace PaperN.PartII
open MeasureTheory Metric Set
open scoped NNReal
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- The distance function from one point, as a continuous function. -/
def distanceProfile (x : X) : C(X, ℝ) := ⟨fun y ↦ dist x y, continuous_const.dist continuous_id⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem distanceProfile_norm_le (x : X) : ‖distanceProfile x‖ ≤ diam (univ : Set X) := by
  apply (ContinuousMap.norm_le _ diam_nonneg).mpr
  intro y
  exact (by simpa [distanceProfile] using dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y))

omit [MeasurableSpace X] [BorelSpace X] in
theorem distanceProfile_sub_norm_le (x y : X) :
    ‖distanceProfile x - distanceProfile y‖ ≤ dist x y := by
  apply (ContinuousMap.norm_le _ dist_nonneg).mpr
  intro z
  exact abs_dist_sub_le x y z

noncomputable def continuousToL2 : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ := ContinuousMap.toLp 2 μ ℝ

theorem continuousToL2_norm_le (f : C(X, ℝ)) : ‖continuousToL2 μ f‖ ≤ ‖f‖ := by
  have h : ‖continuousToL2 μ‖ ≤ 1 := by
    simpa [continuousToL2, measureUnivNNReal] using (ContinuousMap.toLp_norm_le (E := ℝ) (𝕜 := ℝ) (p := 2) μ)
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg f])

noncomputable def distanceProfileL2 (x : X) : Lp ℝ 2 μ := continuousToL2 μ (distanceProfile x)

theorem distanceProfileL2_norm_le (x : X) : ‖distanceProfileL2 μ x‖ ≤ diam (univ : Set X) :=
  (continuousToL2_norm_le μ _).trans (distanceProfile_norm_le x)

theorem distanceProfileL2_sub_norm_le (x y : X) :
    ‖distanceProfileL2 μ x - distanceProfileL2 μ y‖ ≤ dist x y := by
  change ‖continuousToL2 μ (distanceProfile x) - continuousToL2 μ (distanceProfile y)‖ ≤ _
  rw [← map_sub]
  exact (continuousToL2_norm_le μ _).trans (distanceProfile_sub_norm_le x y)

/-- L² inner products make independence of representatives part of the definition. -/
noncomputable def distanceValue (f : Lp ℝ 2 μ) (x : X) : ℝ := inner ℝ (distanceProfileL2 μ x) f

theorem distanceValue_bound (f : Lp ℝ 2 μ) (x : X) :
    |distanceValue μ f x| ≤ diam (univ : Set X) * ‖f‖ := by
  simpa only [distanceValue, Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) (distanceProfileL2 μ x) f).trans (mul_le_mul_of_nonneg_right (distanceProfileL2_norm_le μ x) (norm_nonneg f))

theorem distanceValue_sub_bound (f : Lp ℝ 2 μ) (x y : X) :
    |distanceValue μ f x - distanceValue μ f y| ≤ dist x y * ‖f‖ := by
  unfold distanceValue
  rw [← inner_sub_left]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul_of_nonneg_right (distanceProfileL2_sub_norm_le μ x y) (norm_nonneg f))

theorem distanceValue_lipschitz (f : Lp ℝ 2 μ) : LipschitzWith ‖f‖₊ (distanceValue μ f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa [Real.dist_eq, mul_comm] using distanceValue_sub_bound μ f x y

noncomputable def distanceContinuous (f : Lp ℝ 2 μ) : C(X, ℝ) :=
  ⟨distanceValue μ f, (distanceValue_lipschitz μ f).continuous⟩

theorem distanceContinuous_norm_le (f : Lp ℝ 2 μ) :
    ‖distanceContinuous μ f‖ ≤ diam (univ : Set X) * ‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg diam_nonneg (norm_nonneg f))).mpr
  exact distanceValue_bound μ f

noncomputable def distanceToContinuous : Lp ℝ 2 μ →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous {
    toFun := distanceContinuous μ
    map_add' := by
      intro f g; ext x
      change inner ℝ _ (f+g) = inner ℝ _ f + inner ℝ _ g
      exact inner_add_right _ _ _
    map_smul' := by
      intro a f; ext x
      change inner ℝ _ (a • f) = a * inner ℝ _ f
      exact inner_smul_right _ _ _ }
    (diam (univ : Set X)) (distanceContinuous_norm_le μ)

noncomputable def distanceOperator : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (continuousToL2 μ).comp (distanceToContinuous μ)

theorem distanceValue_integral (f : Lp ℝ 2 μ) (x : X) :
    distanceValue μ f x = ∫ y, dist x y * f y ∂μ := by
  rw [distanceValue, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(distanceProfile x).coeFn_toLp (p := 2) (𝕜 := ℝ) μ] with y hy
  change inner ℝ ((distanceProfileL2 μ x) y) (f y) = _
  change (distanceProfileL2 μ x) y = dist x y at hy
  simp [hy, mul_comm]

theorem distanceIntegrand_integrable (f : Lp ℝ 2 μ) (x : X) :
    Integrable (fun y ↦ dist x y * f y) μ := by
  apply (L2.integrable_inner (𝕜 := ℝ) (distanceProfileL2 μ x) f).congr
  filter_upwards [(distanceProfile x).coeFn_toLp (p := 2) (𝕜 := ℝ) μ] with y hy
  change (distanceProfileL2 μ x) y = dist x y at hy
  simp [hy, mul_comm]

theorem distanceValue_integral_of_ae (f : Lp ℝ 2 μ) (g : X → ℝ)
    (hg : g =ᵐ[μ] f) (x : X) : distanceValue μ f x = ∫ y, dist x y * g y ∂μ := by
  rw [distanceValue_integral]
  apply integral_congr_ae
  filter_upwards [hg] with y hy
  rw [hy]

theorem distanceOperator_ae (f : Lp ℝ 2 μ) :
    (distanceOperator μ f : X → ℝ) =ᵐ[μ] (fun x ↦ ∫ y, dist x y * f y ∂μ) := by
  have h := (distanceContinuous μ f).coeFn_toLp (p := 2) (𝕜 := ℝ) μ
  filter_upwards [h] with x hx
  exact hx.trans (distanceValue_integral μ f x)

theorem distanceOperator_norm_le (f : Lp ℝ 2 μ) :
    ‖distanceOperator μ f‖ ≤ diam (univ : Set X) * ‖f‖ :=
  (continuousToL2_norm_le μ _).trans (distanceContinuous_norm_le μ f)

/-- Full support promotes equality in L² to equality of continuous representatives. -/
theorem continuousToL2_injective [μ.IsOpenPosMeasure] : Function.Injective (continuousToL2 μ) :=
  ContinuousMap.toLp_injective μ

/-- Every nonzero eigenvector has a unique continuous representative. -/
theorem eigenfunction_continuousRepresentative [μ.IsOpenPosMeasure]
    (f : Lp ℝ 2 μ) (a : ℝ) (ha : a ≠ 0) (hf : distanceOperator μ f = a • f) :
    ∃! g : C(X, ℝ), continuousToL2 μ g = f := by
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
end PaperN.PartII
