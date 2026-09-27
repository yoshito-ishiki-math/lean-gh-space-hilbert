import PaperN.PartI.Remeasure

namespace PaperN.PartI
open MeasureTheory Filter
open scoped Topology
universe u
namespace CommonRealization
variable {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}

/-- The constructive part of `lem:convergent-invariant-lifts`, after obtaining
ordinary approximating probabilities in a compact common realization. -/
def InvariantApproximationStatement (C : CommonRealization Xs X) : Prop :=
  C.HausdorffConverges → C.WeakConverges →
    (∀ g : X ≃ᵢ X, Measure.map g X.measure = X.measure) →
    ∃ ν : ∀ n, ProbabilityMeasure (Xs n),
      (∀ n, ((Xs n).withProbability (ν n)).InvariantFullSupport) ∧
      (C.withProbabilities ν).WeakConverges ∧
      Tendsto (fun n ↦ ghpDist ((Xs n).withProbability (ν n)) X) atTop (𝓝 0)
end CommonRealization
end PaperN.PartI
