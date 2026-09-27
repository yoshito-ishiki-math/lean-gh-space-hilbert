import PaperN.PartII.DualRepresentation

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartII
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A comparison of primal norms reverses the dual comparison. -/
theorem coordinateDualNorm_le_mul_of_le
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ x, p x ≤ c * q x) (u : E) :
    coordinateDualNorm q hq u ≤ c * coordinateDualNorm p hp u := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc (norm_nonneg _))
  intro x
  change |⟪u, x⟫| ≤ c * coordinateDualNorm p hp u * q x
  rw [real_inner_comm]
  have hpair := abs_inner_le_coordinateDualNorm_mul p hp (show E from x) u
  have hmul := mul_le_mul_of_nonneg_left (h x) (show 0 ≤ coordinateDualNorm p hp u from norm_nonneg _)
  exact hpair.trans (hmul.trans_eq (by ring))

/-- Relative primal bounds give the corresponding reciprocal dual bounds. -/
theorem coordinateDualNorm_inv_bounds
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hl : ∀ x, (1 - δ) * p x ≤ q x) (hu : ∀ x, q x ≤ (1 + δ) * p x)
    (u : E) (hne : u ≠ 0) :
    (1 - δ) / coordinateDualNorm p hp u ≤ (coordinateDualNorm q hq u)⁻¹ ∧
    (coordinateDualNorm q hq u)⁻¹ ≤ (1 + δ) / coordinateDualNorm p hp u := by
  have hp0 := coordinateDualNorm_pos p hp u hne
  have hq0 := coordinateDualNorm_pos q hq u hne
  have hlow := coordinateDualNorm_le_mul_of_le q p hq hp (1 + δ) (by positivity) hu u
  have hhigh := coordinateDualNorm_le_mul_of_le p q hp hq (1 - δ)⁻¹ (by positivity)
    (fun x ↦ by
      rw [inv_mul_eq_div, le_div_iff₀ (show 0 < 1 - δ by linarith)]
      simpa only [mul_comm] using hl x) u
  constructor
  · rw [inv_eq_one_div, div_le_div_iff₀ hp0 hq0]
    have hd : (1 - δ) * coordinateDualNorm q hq u ≤ coordinateDualNorm p hp u := by
      have := (le_div_iff₀ (show 0 < 1 - δ by linarith)).mp
        (show coordinateDualNorm q hq u ≤ coordinateDualNorm p hp u / (1 - δ) by
          simpa only [div_eq_mul_inv, mul_comm] using hhigh)
      nlinarith
    nlinarith
  · rw [inv_eq_one_div, div_le_div_iff₀ hq0 hp0]
    nlinarith

/-- Relative primal error controls the reciprocal dual norm pointwise. -/
theorem coordinateDualNorm_inv_error
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hl : ∀ x, (1 - δ) * p x ≤ q x) (hu : ∀ x, q x ≤ (1 + δ) * p x)
    (u : E) (hne : u ≠ 0) :
    |(coordinateDualNorm q hq u)⁻¹ - (coordinateDualNorm p hp u)⁻¹| ≤
      δ / coordinateDualNorm p hp u := by
  obtain ⟨hlow, hhigh⟩ := coordinateDualNorm_inv_bounds p q hp hq δ hδ hδ1 hl hu u hne
  rw [abs_le]
  constructor <;> simp only [sub_div, add_div, one_div] at * <;> linarith

/-- A relative error in the primal norm controls the normalized representation. -/
theorem coordinateDualEmbedding_sub_norm_le
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hl : ∀ x, (1 - δ) * p x ≤ q x) (hu : ∀ x, q x ≤ (1 + δ) * p x)
    (x : E) :
    ‖coordinateDualEmbedding q hq x - coordinateDualEmbedding p hp x‖ ≤ δ * p x := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hδ (apply_nonneg p x))).mpr
  intro u
  have hne : u.val ≠ 0 := by
    intro h
    have hs := mem_sphere_zero_iff_norm.mp u.property
    simp [h] at hs
  have hp0 := coordinateDualNorm_pos p hp u.val hne
  change |⟪x, u.val⟫ / coordinateDualNorm q hq u.val -
    ⟪x, u.val⟫ / coordinateDualNorm p hp u.val| ≤ δ * p x
  rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
  calc
    _ ≤ (coordinateDualNorm p hp u.val * p x) * (δ / coordinateDualNorm p hp u.val) :=
      mul_le_mul (abs_inner_le_coordinateDualNorm_mul p hp x u.val)
        (coordinateDualNorm_inv_error p q hp hq δ hδ hδ1 hl hu u.val hne)
        (abs_nonneg _) (mul_nonneg hp0.le (apply_nonneg p x))
    _ = _ := by field_simp

end PaperN.PartII
