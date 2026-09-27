import PaperN.PartII.CoordinateNormCarrier
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.NNNorm

namespace PaperN.PartII
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Euclidean pairings regarded as functionals on the chosen coordinate norm. -/
noncomputable def coordinateDualFunctional (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    E →L[ℝ] (CoordinateNormCarrier p hp →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (CoordinateNormCarrier p hp) E ℝ).flip
    (CoordinateNormCarrier.continuousLinearEquiv p hp).symm.toContinuousLinearMap).comp (innerSL ℝ)

@[simp] theorem coordinateDualFunctional_apply (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (u : E) (v : CoordinateNormCarrier p hp) : coordinateDualFunctional p hp u v = ⟪u, v⟫ := rfl

/-- The dual norm is the operator norm for the chosen primal norm. -/
noncomputable def coordinateDualNorm (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (u : E) : ℝ :=
  ‖coordinateDualFunctional p hp u‖

theorem continuous_coordinateDualNorm (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) :
    Continuous (coordinateDualNorm p hp) := (coordinateDualFunctional p hp).continuous.norm

/-- Nonzero Euclidean vectors give strictly positive dual norm. -/
theorem coordinateDualNorm_pos (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (u : E) (hu : u ≠ 0) : 0 < coordinateDualNorm p hp u := by
  apply norm_pos_iff.mpr
  intro h
  have he := congrArg (fun f : CoordinateNormCarrier p hp →L[ℝ] ℝ ↦
    f (CoordinateNormCarrier.linearEquiv p hp u)) h
  change ⟪u, u⟫ = 0 at he
  exact hu (inner_self_eq_zero.mp he)

/-- The defining dual pairing estimate, with the actual coordinate norm on vectors. -/
theorem abs_inner_le_coordinateDualNorm_mul (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x u : E) : |⟪x, u⟫| ≤ coordinateDualNorm p hp u * p x := by
  have h := (coordinateDualFunctional p hp u).le_opNorm (CoordinateNormCarrier.linearEquiv p hp x)
  change |⟪u, x⟫| ≤ coordinateDualNorm p hp u * p x at h
  rwa [real_inner_comm] at h

/-- The operator-norm definition equals the manuscript's primal-unit-ball supremum. -/
theorem coordinateDualNorm_eq_sSup (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (u : E) : coordinateDualNorm p hp u =
      sSup ((fun x : E ↦ |⟪x, u⟫|) '' {x | p x ≤ 1}) := by
  rw [coordinateDualNorm, ← (coordinateDualFunctional p hp u).sSup_unitClosedBall_eq_norm]
  congr 1
  ext r
  simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right,
    CoordinateNormCarrier.norm_eq, coordinateDualFunctional_apply, Real.norm_eq_abs]
  constructor
  · rintro ⟨x, hx, hxr⟩
    exact ⟨x, hx, by simpa only [real_inner_comm u x] using hxr⟩
  · rintro ⟨x, hx, hxr⟩
    exact ⟨CoordinateNormCarrier.linearEquiv p hp x, hx,
      by change |⟪u, x⟫| = r; rwa [real_inner_comm]⟩

/-- The normalized pairing is a continuous function on the fixed Euclidean sphere. -/
noncomputable def coordinateDualEmbedding (p : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0)
    (x : E) : C(Metric.sphere (0 : E) 1, ℝ) where
  toFun u := ⟪x, u.val⟫ / coordinateDualNorm p hp u.val
  continuous_toFun := (continuous_const.inner continuous_subtype_val).div
    ((continuous_coordinateDualNorm p hp).comp continuous_subtype_val) (fun u ↦ by
      apply ne_of_gt (coordinateDualNorm_pos p hp u.val _)
      intro h
      have hu := mem_sphere_zero_iff_norm.mp u.property
      simp [h] at hu)

end PaperN.PartII
