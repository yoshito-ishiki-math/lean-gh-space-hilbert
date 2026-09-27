import PaperN.PartI.MeasuredCompact
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Definitions for the max-convention GHP infimum; no metric-space axioms are asserted. -/
namespace PaperN.PartI
open MeasureTheory Set Metric
open scoped ENNReal
universe u

/-- A common compact ambient space and isometric embeddings of the entire carriers. -/
structure CompactCoupling (X Y : MeasuredCompact.{u}) where
  Carrier : Type u
  metric : MetricSpace Carrier
  compact : @CompactSpace Carrier metric.toUniformSpace.toTopologicalSpace
  left : X → Carrier
  right : Y → Carrier
  left_isometry : Isometry left
  right_isometry : Isometry right

instance {X Y : MeasuredCompact.{u}} : CoeSort (CompactCoupling X Y) (Type u) :=
  ⟨CompactCoupling.Carrier⟩
attribute [instance] CompactCoupling.metric CompactCoupling.compact
instance {X Y : MeasuredCompact.{u}} (C : CompactCoupling X Y) : MeasurableSpace C := borel C
instance {X Y : MeasuredCompact.{u}} (C : CompactCoupling X Y) : BorelSpace C := ⟨rfl⟩

namespace CompactCoupling
variable {X Y : MeasuredCompact.{u}}
noncomputable def leftMeasure (C : CompactCoupling X Y) : Measure C :=
  Measure.map C.left X.measure
noncomputable def rightMeasure (C : CompactCoupling X Y) : Measure C :=
  Measure.map C.right Y.measure
instance (C : CompactCoupling X Y) : IsProbabilityMeasure C.leftMeasure := by
  unfold leftMeasure
  infer_instance
instance (C : CompactCoupling X Y) : IsProbabilityMeasure C.rightMeasure := by
  unfold rightMeasure
  infer_instance

/-- Both distances are nonnegative extended reals; the cost is their maximum. -/
noncomputable def cost (C : CompactCoupling X Y) : ℝ≥0∞ :=
  max (hausdorffEDist (range C.left) (range C.right))
    (levyProkhorovEDist C.leftMeasure C.rightMeasure)

end CompactCoupling

/-- Representative-level extended GHP distance, with max rather than sum convention. -/
noncomputable def ghpEDist (X Y : MeasuredCompact.{u}) : ℝ≥0∞ :=
  ⨅ C : CompactCoupling X Y, C.cost

/-- Real-valued version. `GHPDistance` proves finiteness and the real infimum formula. -/
noncomputable def ghpDist (X Y : MeasuredCompact.{u}) : ℝ := (ghpEDist X Y).toReal

end PaperN.PartI
