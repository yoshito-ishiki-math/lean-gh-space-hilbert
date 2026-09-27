import PaperN.PartII.EquivariantARInputs

namespace PaperN.PartII
open TopologicalSpace

/-- The operator topology on the orthogonal group is Hausdorff. -/
theorem orthogonalOperator_t2Space {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
    T2Space (E ≃ₗᵢ[ℝ] E) := by
  letI : TopologicalSpace (E ≃ₗᵢ[ℝ] E) := orthogonalOperatorTopology
  have hi : Topology.IsEmbedding (fun U : E ≃ₗᵢ[ℝ] E ↦
      U.toContinuousLinearEquiv.toContinuousLinearMap) := by
    refine ⟨⟨rfl⟩, ?_⟩
    intro U V h
    ext x
    exact congrArg (fun A : E →L[ℝ] E ↦ A x) h
  exact hi.t2Space

namespace SphereOrbit
variable (n : ℕ → ℕ)
noncomputable local instance arFactorTopology : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
local instance arFactorT2 : ∀ i, T2Space (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperator_t2Space
local instance arGroupCompact : CompactSpace (GroupType n) := orthogonalProduct_compactSpace n
local instance arGroupTopological : IsTopologicalGroup (GroupType n) := orthogonalProduct_isTopologicalGroup n
local instance arGroupSecondCountable : SecondCountableTopology (GroupType n) := orthogonalProduct_secondCountable n

noncomputable local instance arVectorAction : MulAction (GroupType n) (SphereBlockSum n) where
  smul a x := sphereBlockSumAction n a x
  one_smul := sphereBlockSumAction_one n
  mul_smul := sphereBlockSumAction_mul n

local instance arVectorContinuousSMul : ContinuousSMul (GroupType n) (SphereBlockSum n) :=
  ⟨continuous_sphereBlockSumAction_product n⟩

noncomputable local instance arCompactAction : MulAction (GroupType n) (NonemptyCompacts (SphereBlockSum n)) :=
  sphereCompactMulAction n

/-- The concrete compact hyperspace is an equivariant AR under the registered input. -/
theorem hyperspace_equivariantAR (hH : EquivariantHyperspaceARInput) :
    IsEquivariantAbsoluteRetract.{0,0,0} (GroupType n)
      (NonemptyCompacts (SphereBlockSum n)) := by
  apply hH (GroupType n) (SphereBlockSum n)
  · intro a K
    rfl
  · exact normedSpace_connected
  · exact normedSpace_continuumConnectedBasis _

/-- The actual orbit metric space is an AR, conditional only on the two general citations. -/
theorem absoluteRetract (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput) :
    IsAbsoluteRetract.{0,0} (Space n) := by
  apply hO (GroupType n) (NonemptyCompacts (SphereBlockSum n)) (Space n)
    (hyperspace_equivariantAR n hH) (projection n) (projection_isQuotientMap n)
  exact projection_eq_iff n

end SphereOrbit
end PaperN.PartII
