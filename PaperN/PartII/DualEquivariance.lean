import PaperN.PartII.DualRepresentation

namespace PaperN.PartII
open scoped RealInnerProductSpace
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Dual norms transform by the same orthogonal change as primal norms. -/
theorem coordinateDualNorm_orthogonal
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (U : E ≃ₗᵢ[ℝ] E) (h : ∀ x, q (U x) = p x) (u : E) :
    coordinateDualNorm q hq (U u) = coordinateDualNorm p hp u := by
  rw [coordinateDualNorm_eq_sSup, coordinateDualNorm_eq_sSup]
  congr 1
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.symm x, ?_, ?_⟩
    · simpa only [Set.mem_setOf_eq, ← h, U.apply_symm_apply] using hx
    · change |⟪U.symm x, u⟫| = |⟪x, U u⟫|
      rw [← U.inner_map_map, U.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨U x, by simpa only [Set.mem_setOf_eq, h] using hx, by change |⟪U x, U u⟫| = |⟪x, u⟫|; rw [U.inner_map_map]⟩

/-- Orthogonal maps permute the fixed Euclidean unit sphere. -/
def orthogonalSphereEquiv (U : E ≃ₗᵢ[ℝ] E) : Metric.sphere (0 : E) 1 ≃ Metric.sphere (0 : E) 1 where
  toFun u := ⟨U u.val, by simpa only [mem_sphere_zero_iff_norm, U.norm_map] using u.property⟩
  invFun u := ⟨U.symm u.val, by simpa only [mem_sphere_zero_iff_norm, U.symm.norm_map] using u.property⟩
  left_inv u := by apply Subtype.ext; exact U.symm_apply_apply u.val
  right_inv u := by apply Subtype.ext; exact U.apply_symm_apply u.val

/-- The inverse sphere map used by the function-space action. -/
def orthogonalSpherePullback (U : E ≃ₗᵢ[ℝ] E) : C(Metric.sphere (0 : E) 1, Metric.sphere (0 : E) 1) where
  toFun := (orthogonalSphereEquiv U).symm
  continuous_toFun := (U.symm.continuous.comp continuous_subtype_val).subtype_mk _

/-- Pullback by the inverse orthogonal map is a linear isometry of sphere functions. -/
noncomputable def orthogonalSphereAction (U : E ≃ₗᵢ[ℝ] E) :
    C(Metric.sphere (0 : E) 1, ℝ) →ₗᵢ[ℝ] C(Metric.sphere (0 : E) 1, ℝ) where
  toFun f := f.comp (orthogonalSpherePullback U)
  map_add' f g := rfl
  map_smul' a f := rfl
  norm_map' f := by
    rw [ContinuousMap.norm_eq_iSup_norm, ContinuousMap.norm_eq_iSup_norm]
    exact (orthogonalSphereEquiv U).symm.iSup_comp (g := fun u ↦ ‖f u‖)

/-- The normalized sphere formula intertwines orthogonal changes of coordinates. -/
theorem coordinateDualEmbedding_equivariant
    (p q : Seminorm ℝ E) (hp : ∀ v, p v = 0 → v = 0) (hq : ∀ v, q v = 0 → v = 0)
    (U : E ≃ₗᵢ[ℝ] E) (h : ∀ x, q (U x) = p x) (x : E) :
    coordinateDualEmbedding q hq (U x) = orthogonalSphereAction U (coordinateDualEmbedding p hp x) := by
  apply ContinuousMap.ext
  intro u
  change ⟪U x, u.val⟫ / coordinateDualNorm q hq u.val =
    ⟪x, U.symm u.val⟫ / coordinateDualNorm p hp (U.symm u.val)
  have hd := coordinateDualNorm_orthogonal p q hp hq U h (U.symm u.val)
  rw [U.apply_symm_apply] at hd
  rw [hd, U.inner_map_eq_flip]

@[simp] theorem orthogonalSphereAction_refl (f : C(Metric.sphere (0 : E) 1, ℝ)) :
    orthogonalSphereAction (LinearIsometryEquiv.refl ℝ E) f = f := by
  apply ContinuousMap.ext
  intro u
  rfl

theorem orthogonalSphereAction_trans (U V : E ≃ₗᵢ[ℝ] E)
    (f : C(Metric.sphere (0 : E) 1, ℝ)) :
    orthogonalSphereAction (U.trans V) f = orthogonalSphereAction V (orthogonalSphereAction U f) := by
  apply ContinuousMap.ext
  intro u
  rfl

theorem orthogonalSphereAction_surjective (U : E ≃ₗᵢ[ℝ] E) :
    Function.Surjective (orthogonalSphereAction U) := by
  intro f
  refine ⟨orthogonalSphereAction U.symm f, ?_⟩
  apply ContinuousMap.ext
  intro u
  change f ⟨U (U.symm u.val), _⟩ = f u
  congr 1
  apply Subtype.ext
  exact U.apply_symm_apply u.val

/-- Each orthogonal transformation acts by a surjective linear isometry. -/
noncomputable def orthogonalSphereActionEquiv (U : E ≃ₗᵢ[ℝ] E) :
    C(Metric.sphere (0 : E) 1, ℝ) ≃ₗᵢ[ℝ] C(Metric.sphere (0 : E) 1, ℝ) :=
  LinearIsometryEquiv.ofSurjective (orthogonalSphereAction U) (orthogonalSphereAction_surjective U)

end PaperN.PartII
