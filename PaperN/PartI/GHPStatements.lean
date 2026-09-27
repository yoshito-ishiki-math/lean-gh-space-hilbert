import PaperN.PartI.GHPDefinitions
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-! Reviewable statements; this module imports no proofs of these target results. -/
namespace PaperN.PartI
open MeasureTheory Set Metric GromovHausdorff
open scoped ENNReal Topology
universe u

def GHPBasicStatement : Prop :=
  (∀ X Y : MeasuredCompact.{u}, ghpEDist X Y ≠ ⊤) ∧
  (∀ X : MeasuredCompact.{u}, ghpEDist X X = 0) ∧
  (∀ X Y : MeasuredCompact.{u}, ghpEDist X Y = ghpEDist Y X) ∧
  (∀ X X' Y Y' : MeasuredCompact.{u}, X.Isomorphic X' → Y.Isomorphic Y' →
    ghpEDist X Y = ghpEDist X' Y') ∧
  (∀ X Y : MeasuredCompact.{u}, ghpDist X Y = ⨅ C : CompactCoupling X Y,
    max (hausdorffDist (range C.left) (range C.right))
      (levyProkhorovDist C.leftMeasure C.rightMeasure))

def GHProjectionBoundStatement : Prop :=
  ∀ X Y : MeasuredCompact.{u}, ghDist X Y ≤ ghpDist X Y

def InvariantProjectionSurjectivityStatement : Prop :=
  ∀ q : GHSpace, ∃ M : MeasuredCompact.{0}, M.InvariantFullSupport ∧ toGHSpace M = q
/-- Analytic step only: no common ambient space is supplied by this statement. -/
def WeakProkhorovStatement {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {ι : Type*} (l : Filter ι) (μ : ι → ProbabilityMeasure Z) (ν : ProbabilityMeasure Z) : Prop :=
  Filter.Tendsto μ l (𝓝 ν) ↔
    Filter.Tendsto (fun i ↦ levyProkhorovDist (μ i : Measure Z) (ν : Measure Z)) l (𝓝 0)
end PaperN.PartI
