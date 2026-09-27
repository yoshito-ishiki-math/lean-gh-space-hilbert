import PaperN.PartII.OrthogonalCompactness

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Multiplication is continuous for the induced orthogonal operator topology. -/
theorem continuous_orthogonal_mul :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    Continuous (fun z : (E ≃ₗᵢ[ℝ] E) × (E ≃ₗᵢ[ℝ] E) ↦ z.1 * z.2) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  have hi : Topology.IsInducing (fun U : E ≃ₗᵢ[ℝ] E ↦
    U.toContinuousLinearEquiv.toContinuousLinearMap) := ⟨rfl⟩
  apply hi.continuous_iff.mpr
  exact (hi.continuous.comp continuous_fst).clm_comp (hi.continuous.comp continuous_snd)

/-- Inversion is continuous because an orthogonal inverse is its adjoint. -/
theorem continuous_orthogonal_inv :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    Continuous (fun U : E ≃ₗᵢ[ℝ] E ↦ U⁻¹) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  have hi : Topology.IsInducing (fun U : E ≃ₗᵢ[ℝ] E ↦
    U.toContinuousLinearEquiv.toContinuousLinearMap) := ⟨rfl⟩
  apply hi.continuous_iff.mpr
  exact continuous_orthogonal_inverse id hi.continuous

/-- The same topology makes the orthogonal group a topological group. -/
theorem orthogonalOperator_isTopologicalGroup :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    IsTopologicalGroup (E ≃ₗᵢ[ℝ] E) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  exact { continuous_mul := continuous_orthogonal_mul, continuous_inv := continuous_orthogonal_inv }

/-- The product acting on the Banach block space is a topological group. -/
theorem orthogonalProduct_isTopologicalGroup (n : ℕ → ℕ) :
    letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
    IsTopologicalGroup (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i))) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  letI : ∀ i, IsTopologicalGroup (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperator_isTopologicalGroup
  infer_instance

end PaperN.PartII
