import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.MetricSpace.Polish

namespace PaperN.PartI
open MeasureTheory Filter TopologicalSpace
open scoped Topology

/-- The entire manuscript `lem:dirac-product-convergence`, with compact metric parameter
and Polish probability carrier; the laws need not have compact support. -/
def DiracProductConvergenceStatement : Prop :=
  ∀ {T Y : Type*} [MetricSpace T] [CompactSpace T] [TopologicalSpace Y] [PolishSpace Y]
    [MeasurableSpace T] [MeasurableSpace Y] [BorelSpace T] [BorelSpace Y]
    (ts : ℕ → T) (t : T) (ηs : ℕ → ProbabilityMeasure Y) (η : ProbabilityMeasure Y),
    Tendsto ts atTop (𝓝 t) → Tendsto ηs atTop (𝓝 η) →
    Tendsto (fun n ↦ (diracProba (ts n)).prod (ηs n)) atTop (𝓝 ((diracProba t).prod η))
end PaperN.PartI
