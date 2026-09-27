import PaperN.PartII.AbsoluteRetract
import PaperN.PartII.BanachContinua
import PaperN.PartII.SphereOrbitSpace
import PaperN.PartII.OrthogonalCountability

namespace PaperN.PartII
open Set TopologicalSpace
open scoped Topology

/-- The open-basis form of local continuum-connectedness. -/
def HasContinuumConnectedBasis (X : Type) [TopologicalSpace X] : Prop :=
  ∀ a : X, ∀ U ∈ nhds a, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
    ∀ x ∈ V, ∀ y ∈ V, ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ K ⊆ V

/-- Open balls supply a continuum-connected basis without finite-dimensionality. -/
theorem normedSpace_continuumConnectedBasis (E : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : HasContinuumConnectedBasis E := by
  intro a U hU
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨Metric.ball a r, Metric.isOpen_ball, Metric.mem_ball_self hr, hsub,
    fun _ hx _ hy ↦ ball_contains_continuum a r hx hy⟩

/-- Registered general hyperspace theorem: Antonyan 2003, Proposition 3.1,
with its 2006 correction. The hyperspace action is explicitly the image action.
This is an input proposition, not a global axiom or an implementation of the citation. -/
def EquivariantHyperspaceARInput : Prop :=
  ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [MetricSpace X] [Nonempty X]
    [MulAction G X] [ContinuousSMul G X]
    [MulAction G (NonemptyCompacts X)],
    (∀ (a : G) (K : NonemptyCompacts X),
      ((a • K : NonemptyCompacts X) : Set X) = (fun x ↦ a • x) '' (K : Set X)) →
    IsConnected (Set.univ : Set X) → HasContinuumConnectedBasis X →
    IsEquivariantAbsoluteRetract.{0,0,0} G (NonemptyCompacts X)

/-- Registered orbit-AR theorem: Antonyan 1990, Theorem 8 and Corollary 1.
The quotient is specified by its topology and exact orbit fibers, so arbitrary
homeomorphic presentations of the orbit space are allowed. All spaces are Type 0. -/
def OrbitARInput : Prop :=
  ∀ (G X Q : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [MulAction G X] [TopologicalSpace Q],
    IsEquivariantAbsoluteRetract.{0,0,0} G X →
    ∀ q : X → Q, Topology.IsQuotientMap q →
      (∀ x y, q x = q y ↔ ∃ a : G, x = a • y) →
      IsAbsoluteRetract.{0,0} Q

end PaperN.PartII
