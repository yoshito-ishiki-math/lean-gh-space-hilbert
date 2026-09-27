import PaperN.PartI.UniformOrbitStatements
import PaperN.PartI.HaarAverage

namespace PaperN.PartI
open MeasureTheory Filter
open scoped Topology
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

noncomputable def averagedProbability (C : CommonRealization Xs X) (n : ℕ) :
    ProbabilityMeasure C :=
  (haarAverage (Xs n).probability).map (C.seq_isometry n).continuous.measurable.aemeasurable

/-- The Haar-averaging convergence step of `lem:convergent-invariant-lifts`. -/
def HaarConvergenceStatement (C : CommonRealization Xs X) : Prop :=
  C.HausdorffConverges → C.WeakConverges →
    (∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) →
    Tendsto C.averagedProbability atTop (𝓝 C.limitProbability)
end CommonRealization
end PaperN.PartI
