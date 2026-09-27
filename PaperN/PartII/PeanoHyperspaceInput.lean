import PaperN.PartIV.HilbertCubeApproximation
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.MetricSpace.Closeds

namespace PaperN.PartIII
open TopologicalSpace
universe u

/-- Curtis--Schori, Theorem 3.2: a general cited input, not an asserted inhabitant.
The hyperspace contains all nonempty compact subsets, not just subcontinua,
and it is not a group-orbit quotient. -/
def CurtisSchoriHyperspaceInput : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] [Nontrivial X],
    Nonempty (NonemptyCompacts X ≃ₜ PaperN.PartIV.HilbertCube)

/-- On the compact metric carriers of the source, closed and compact subsets agree. -/
theorem peano_closed_iff_compact {X : Type*} [MetricSpace X] [CompactSpace X]
    (S : Set X) : IsClosed S ↔ IsCompact S :=
  ⟨fun h ↦ h.isCompact, fun h ↦ h.isClosed⟩

/-- The topology used in the input is that of the stated Hausdorff distance. -/
theorem peano_hyperspace_dist {X : Type*} [MetricSpace X]
    (A B : NonemptyCompacts X) :
    dist A B = Metric.hausdorffDist (A : Set X) (B : Set X) := rfl

/-- Exact application of the cited result in rem:peano-hyperspace. -/
theorem peano_hyperspace_homeomorphic_cube (hCS : CurtisSchoriHyperspaceInput.{u})
    (X : Type u) [MetricSpace X] [CompactSpace X] [ConnectedSpace X]
    [LocallyConnectedSpace X] [Nontrivial X] :
    Nonempty (NonemptyCompacts X ≃ₜ PaperN.PartIV.HilbertCube) := hCS X

end PaperN.PartIII
