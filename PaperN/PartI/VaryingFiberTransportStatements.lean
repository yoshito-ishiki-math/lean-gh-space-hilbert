import PaperN.PartI.FiberTransport
import PaperN.PartI.GHPExternalStatements

namespace PaperN.PartI
open MeasureTheory Filter
open scoped Topology
universe u

/-- Full varying-carrier statement of `eq:fiber-pullbacks`, in prescribed common embeddings. -/
def VaryingFiberTransportStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    (C : CommonRealization Xs X), C.HausdorffConverges →
    ∀ (qs : ∀ n, InvariantFiber (Xs n)) (q : InvariantFiber X),
    Tendsto (fun n ↦ (qs n).val.val) atTop (𝓝 q.val.val) →
    Tendsto (fun n ↦ (fiberProbability (Xs n) (qs n)).map
      (C.seq_isometry n).continuous.measurable.aemeasurable) atTop
      (𝓝 ((fiberProbability X q).map C.limit_isometry.continuous.measurable.aemeasurable))
end PaperN.PartI
