import PaperN.PartII.CoordinateDualNorm
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace PaperN.PartII
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Every dual functional for the chosen norm is a Euclidean pairing. -/
theorem coordinateDualFunctional_surjective (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    Function.Surjective (coordinateDualFunctional p hp) := by
  intro g
  obtain ⟨u, hu⟩ := (InnerProductSpace.toDual ℝ E).surjective
    (g.comp (CoordinateNormCarrier.continuousLinearEquiv p hp).toContinuousLinearMap)
  refine ⟨u, ?_⟩
  ext v
  have h := congrArg (fun f : E →L[ℝ] ℝ ↦ f v) hu
  exact h

/-- Hahn--Banach supplies a Euclidean vector attaining the primal norm. -/
theorem exists_coordinateDual_norming (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x : E) (hx : x ≠ 0) : ∃ u : E, coordinateDualNorm p hp u = 1 ∧ ⟪x, u⟫ = p x := by
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector ℝ (CoordinateNormCarrier.linearEquiv p hp x)
    (by change p x ≠ 0; exact fun h ↦ hx (hp x h))
  obtain ⟨u, rfl⟩ := coordinateDualFunctional_surjective p hp g
  refine ⟨u, hg, ?_⟩
  change ⟪u, x⟫ = p x at hgx
  rwa [real_inner_comm] at hgx

/-- The fixed-sphere representation is linear. -/
noncomputable def coordinateDualEmbeddingLinear (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    E →ₗ[ℝ] C(Metric.sphere (0 : E) 1, ℝ) where
  toFun := coordinateDualEmbedding p hp
  map_add' x y := by
    apply ContinuousMap.ext
    intro u
    change ⟪x + y, u.val⟫ / _ = ⟪x, u.val⟫ / _ + ⟪y, u.val⟫ / _
    rw [inner_add_left, add_div]
  map_smul' a x := by
    apply ContinuousMap.ext
    intro u
    change ⟪a • x, u.val⟫ / _ = a * (⟪x, u.val⟫ / _)
    rw [real_inner_smul_left]
    ring

/-- The sphere representation has norm at most the chosen primal norm. -/
theorem coordinateDualEmbedding_norm_le (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x : E) : ‖coordinateDualEmbedding p hp x‖ ≤ p x := by
  apply (ContinuousMap.norm_le _ (apply_nonneg p x)).mpr
  intro u
  have hu : u.val ≠ 0 := by
    intro h
    have hh := mem_sphere_zero_iff_norm.mp u.property
    simp [h] at hh
  have hd := coordinateDualNorm_pos p hp u.val hu
  change |⟪x, u.val⟫ / coordinateDualNorm p hp u.val| ≤ p x
  rw [abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  simpa only [mul_comm] using abs_inner_le_coordinateDualNorm_mul p hp x u.val

/-- The normalized sphere representation preserves the chosen norm exactly. -/
theorem coordinateDualEmbedding_norm_eq (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x : E) : ‖coordinateDualEmbedding p hp x‖ = p x := by
  apply le_antisymm (coordinateDualEmbedding_norm_le p hp x)
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero] using (norm_nonneg (coordinateDualEmbedding p hp 0))
  obtain ⟨u, hd, hu⟩ := exists_coordinateDual_norming p hp x hx
  have hune : u ≠ 0 := by
    intro h
    subst u
    simp [coordinateDualNorm] at hd
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hune
  let t : ℝ := ‖u‖⁻¹
  have ht : 0 < t := inv_pos.mpr hnu
  let θ : Metric.sphere (0 : E) 1 := ⟨t • u, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_of_nonneg ht.le]
    exact inv_mul_cancel₀ hnu.ne'⟩
  have hv : coordinateDualEmbedding p hp x θ = p x := by
    change ⟪x, t • u⟫ / ‖coordinateDualFunctional p hp (t • u)‖ = p x
    rw [real_inner_smul_right, map_smul, norm_smul, Real.norm_of_nonneg ht.le]
    change t * ⟪x, u⟫ / (t * coordinateDualNorm p hp u) = p x
    rw [hu, hd, mul_one]
    exact mul_div_cancel_left₀ (p x) ht.ne'
  have hh := (coordinateDualEmbedding p hp x).norm_coe_le_norm θ
  rw [hv, Real.norm_eq_abs, abs_of_nonneg (apply_nonneg p x)] at hh
  exact hh

/-- The manuscript's linear isometric embedding into a fixed sphere-function space. -/
noncomputable def coordinateDualLinearIsometry (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    CoordinateNormCarrier p hp →ₗᵢ[ℝ] C(Metric.sphere (0 : E) 1, ℝ) where
  toLinearMap := (coordinateDualEmbeddingLinear p hp).comp (CoordinateNormCarrier.linearEquiv p hp).symm.toLinearMap
  norm_map' x := coordinateDualEmbedding_norm_eq p hp x

/-- The explicit pairwise distance identity in the manuscript. -/
theorem coordinateDualEmbedding_norm_sub (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x y : E) : ‖coordinateDualEmbedding p hp x - coordinateDualEmbedding p hp y‖ = p (x - y) := by
  change ‖coordinateDualEmbeddingLinear p hp x - coordinateDualEmbeddingLinear p hp y‖ = _
  rw [← map_sub]
  exact coordinateDualEmbedding_norm_eq p hp (x - y)

end PaperN.PartII
