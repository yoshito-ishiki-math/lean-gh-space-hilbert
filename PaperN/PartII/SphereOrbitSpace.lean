import PaperN.PartII.SphereActionLaws

namespace PaperN.PartII.SphereOrbit
open TopologicalSpace

abbrev GroupType (n : ℕ → ℕ) :=
  ∀ i, EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n i))

variable (n : ℕ → ℕ)
noncomputable local instance : ∀ i, TopologicalSpace (EuclideanSpace ℝ (Fin (n i)) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (n i))) := fun _ ↦ orthogonalOperatorTopology
local instance : CompactSpace (GroupType n) := orthogonalProduct_compactSpace n
noncomputable local instance : MulAction (GroupType n) (NonemptyCompacts (SphereBlockSum n)) :=
  sphereCompactMulAction n

/-- The concrete compact-hyperspace action is jointly continuous. -/
theorem continuousSMul : ContinuousSMul (GroupType n) (NonemptyCompacts (SphereBlockSum n)) :=
  ⟨continuous_sphereCompactAction n⟩

/-- Each concrete action map is a Hausdorff isometry. -/
theorem isIsometricSMul : IsIsometricSMul (GroupType n) (NonemptyCompacts (SphereBlockSum n)) :=
  ⟨fun U ↦ (compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv).isometry⟩

attribute [local instance] continuousSMul isIsometricSMul

/-- The concrete compact-hyperspace orbit space for the global construction. -/
def Space := CompactOrbitQuotient (GroupType n) (NonemptyCompacts (SphereBlockSum n))

noncomputable instance metricSpace : MetricSpace (Space n) :=
  compactOrbitQuotientMetric

/-- Projection from the compact hyperspace to its orbit space. -/
noncomputable def projection (K : NonemptyCompacts (SphereBlockSum n)) : Space n :=
  Quotient.mk _ K

theorem projection_lipschitz : LipschitzWith 1 (projection n) := compactOrbitQuotient_lipschitz

theorem projection_isQuotientMap : Topology.IsQuotientMap (projection n) :=
  compactOrbitQuotient_isQuotientMap

theorem projection_eq_iff (K L : NonemptyCompacts (SphereBlockSum n)) :
    projection n K = projection n L ↔ ∃ U : GroupType n,
      K = compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv L :=
  compactOrbitQuotient_eq_iff K L

theorem dist_projection (K L : NonemptyCompacts (SphereBlockSum n)) :
    dist (projection n K) (projection n L) =
      Metric.infDist K (Set.range (fun U : GroupType n ↦
        compactSetIsometry (sphereBlockSumAction n U).toIsometryEquiv L)) := rfl

/-- The concrete orbit space is separable and metrizable. -/
theorem separableSpace : SeparableSpace (Space n) := by
  letI : SeparableSpace (SphereBlockSum n) := sphereBlockSum_separable n
  have hs : Function.Surjective (projection n) := fun q ↦ Quotient.exists_rep q
  exact hs.denseRange.separableSpace (projection_lipschitz n).continuous

end PaperN.PartII.SphereOrbit
