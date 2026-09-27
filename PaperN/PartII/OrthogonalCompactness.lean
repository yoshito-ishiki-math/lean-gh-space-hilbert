import PaperN.PartII.BlockActionContinuity

namespace PaperN.PartII
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Norm-preserving operators form a compact subset of finite-dimensional operator space. -/
theorem isCompact_normPreservingOperators :
    IsCompact {A : E →L[ℝ] E | ∀ x, ‖A x‖ = ‖x‖} := by
  have hc : IsClosed {A : E →L[ℝ] E | ∀ x, ‖A x‖ = ‖x‖} := by
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro x
    exact isClosed_eq (continuous_id.clm_apply (continuous_const (y := x))).norm continuous_const
  apply (isCompact_closedBall (0 : E →L[ℝ] E) 1).of_isClosed_subset hc
  intro A hA
  rw [Metric.mem_closedBall, dist_zero_right]
  apply A.opNorm_le_bound zero_le_one
  intro x
  simp only [hA x, one_mul, le_refl]

/-- Every norm-preserving endomorphism in finite dimension is an orthogonal equivalence. -/
theorem range_orthogonalOperators :
    Set.range (fun U : E ≃ₗᵢ[ℝ] E ↦ U.toContinuousLinearEquiv.toContinuousLinearMap) =
      {A : E →L[ℝ] E | ∀ x, ‖A x‖ = ‖x‖} := by
  ext A
  constructor
  · rintro ⟨U, rfl⟩
    exact U.norm_map
  · intro hA
    let L : E →ₗᵢ[ℝ] E := ⟨A.toLinearMap, hA⟩
    let U := LinearIsometryEquiv.ofSurjective L
      (LinearMap.surjective_of_injective L.injective)
    exact ⟨U, rfl⟩

/-- The orthogonal group is compact in the same operator topology used by the action. -/
theorem orthogonalOperator_compactSpace :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    CompactSpace (E ≃ₗᵢ[ℝ] E) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  have hi : Topology.IsInducing (fun U : E ≃ₗᵢ[ℝ] E ↦
      U.toContinuousLinearEquiv.toContinuousLinearMap) := ⟨rfl⟩
  constructor
  apply hi.isCompact_iff.mpr
  rw [Set.image_univ, range_orthogonalOperators]
  exact isCompact_normPreservingOperators

/-- The countable product acting on the Banach block sum is compact. -/
theorem orthogonalProduct_compactSpace (n : ℕ → ℕ) :
    letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
    CompactSpace (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i))) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  letI : ∀ i, CompactSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperator_compactSpace
  infer_instance

end PaperN.PartII
