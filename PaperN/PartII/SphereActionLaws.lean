import PaperN.PartII.CompactOrbitTopology

namespace PaperN.PartII
open TopologicalSpace

/-- The identity orthogonal family fixes every sphere-block vector. -/
theorem sphereBlockSumAction_one (n : ℕ → ℕ) (f : SphereBlockSum n) :
    sphereBlockSumAction n 1 f = f := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro u
  rfl

/-- Multiplication of orthogonal families agrees with composition of their block actions. -/
theorem sphereBlockSumAction_mul (n : ℕ → ℕ)
    (U V : ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i)))
    (f : SphereBlockSum n) :
    sphereBlockSumAction n (U * V) f = sphereBlockSumAction n U (sphereBlockSumAction n V f) := by
  apply Subtype.ext
  funext i
  apply ContinuousMap.ext
  intro u
  rfl

/-- The compact-set action respects identity. -/
theorem compactSetIsometry_refl {E : Type*} [MetricSpace E] (K : NonemptyCompacts E) :
    compactSetIsometry (IsometryEquiv.refl E) K = K := by
  apply NonemptyCompacts.ext
  change id '' (K : Set E) = K
  exact Set.image_id _

/-- The compact-set action respects composition. -/
theorem compactSetIsometry_trans {E : Type*} [MetricSpace E]
    (U V : E ≃ᵢ E) (K : NonemptyCompacts E) :
    compactSetIsometry (U.trans V) K = compactSetIsometry V (compactSetIsometry U K) := by
  apply NonemptyCompacts.ext
  change (V ∘ U) '' (K : Set E) = V '' (U '' (K : Set E))
  exact (Set.image_image V U (K : Set E)).symm

/-- The sphere-block linear isometries form a representation of the product group. -/
noncomputable def sphereBlockRepresentation (n : ℕ → ℕ) :
    (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i))) →*
      (SphereBlockSum n ≃ₗᵢ[ℝ] SphereBlockSum n) where
  toFun := sphereBlockSumAction n
  map_one' := by ext f : 1; exact sphereBlockSumAction_one n f
  map_mul' U V := by ext f : 1; exact sphereBlockSumAction_mul n U V f

/-- The actual group action on the sphere-block compact hyperspace. -/
noncomputable abbrev sphereCompactMulAction (n : ℕ → ℕ) :
    MulAction (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i)))
      (NonemptyCompacts (SphereBlockSum n)) where
  smul U K := compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv K
  one_smul K := by
    apply NonemptyCompacts.ext
    change (fun f ↦ sphereBlockSumAction n 1 f) '' (K : Set (SphereBlockSum n)) = K
    simp only [sphereBlockSumAction_one]
    exact Set.image_id _
  mul_smul U V K := by
    apply NonemptyCompacts.ext
    change (fun f ↦ sphereBlockSumAction n (U * V) f) '' (K : Set (SphereBlockSum n)) =
      (fun f ↦ sphereBlockSumAction n U f) '' ((fun f ↦ sphereBlockSumAction n V f) '' (K : Set (SphereBlockSum n)))
    rw [Set.image_image]
    exact congrArg (fun f : SphereBlockSum n → SphereBlockSum n ↦ f '' (K : Set (SphereBlockSum n)))
      (funext (sphereBlockSumAction_mul n U V))

end PaperN.PartII
