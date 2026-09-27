import PaperN.PartII.OrthogonalTopologicalGroup
import Mathlib.Topology.MetricSpace.Closeds

namespace PaperN.PartII
open TopologicalSpace
variable {E : Type*} [MetricSpace E]

/-- A surjective isometry induces a surjective isometry of nonempty compact sets. -/
noncomputable def compactSetIsometry (U : E ≃ᵢ E) : NonemptyCompacts E ≃ᵢ NonemptyCompacts E where
  toFun K := K.map U U.continuous
  invFun K := K.map U.symm U.symm.continuous
  left_inv K := by
    apply NonemptyCompacts.ext
    simp only [NonemptyCompacts.coe_map, Set.image_image]
    simp
  right_inv K := by
    apply NonemptyCompacts.ext
    simp only [NonemptyCompacts.coe_map, Set.image_image]
    simp
  isometry_toFun K L := Metric.hausdorffEDist_image U.isometry

/-- The induced hyperspace map preserves Hausdorff distance. -/
theorem compactSetIsometry_dist (U : E ≃ᵢ E) (K L : NonemptyCompacts E) :
    dist (compactSetIsometry U K) (compactSetIsometry U L) = dist K L :=
  (compactSetIsometry U).isometry.dist_eq K L

/-- Jointly continuous families act jointly continuously on nonempty compact sets. -/
theorem continuous_compactSetIsometry {T : Type*} [TopologicalSpace T]
    (U : T → E ≃ᵢ E) (hU : Continuous (fun z : T × E ↦ U z.1 z.2)) :
    Continuous (fun z : T × NonemptyCompacts E ↦ compactSetIsometry (U z.1) z.2) := by
  apply Continuous.nonemptyCompacts_map' continuous_snd
  exact hU.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)

/-- The sphere-block action extends continuously to its nonempty compact hyperspace. -/
theorem continuous_sphereCompactAction (n : ℕ → ℕ) :
    letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
    Continuous (fun z : (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) × NonemptyCompacts (SphereBlockSum n) ↦
      compactSetIsometry (sphereBlockSumAction n z.1).toIsometryEquiv z.2) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  exact continuous_compactSetIsometry (fun U ↦ (sphereBlockSumAction n U).toIsometryEquiv)
    (continuous_sphereBlockSumAction_product n)

/-- Every orbit in the sphere-block hyperspace is compact. -/
theorem isCompact_sphereCompactOrbit (n : ℕ → ℕ) (K : NonemptyCompacts (SphereBlockSum n)) :
    IsCompact (Set.range (fun U : ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i)) ↦ compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv K)) := by
  letI : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
  letI : CompactSpace (∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i))) := orthogonalProduct_compactSpace n
  have h : Continuous (fun U : ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n i)) ↦ compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv K) :=
    Continuous.nonemptyCompacts_map' (continuous_const (y := K))
      (continuous_sphereBlockSumAction_product n)
  exact isCompact_range h

end PaperN.PartII
