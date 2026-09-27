import PaperN.PartII.OrthogonalTopologicalGroup

namespace PaperN.PartII

/-- The orthogonal operator topology has a countable basis in finite dimension. -/
theorem orthogonalOperator_secondCountable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    SecondCountableTopology (E ≃ₗᵢ[ℝ] E) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  have hi : Topology.IsInducing (fun U : E ≃ₗᵢ[ℝ] E ↦
    U.toContinuousLinearEquiv.toContinuousLinearMap) := ⟨rfl⟩
  exact hi.secondCountableTopology

/-- The actual countable product group satisfies the orbit-AR countability hypothesis. -/
theorem orthogonalProduct_secondCountable (n : ℕ → ℕ) :
    letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
    SecondCountableTopology (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  letI : ∀ i, SecondCountableTopology (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperator_secondCountable
  infer_instance

end PaperN.PartII
