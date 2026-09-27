import PaperN.PartI.LiftInputs
import PaperN.PartI.GHPExternalStatements

namespace PaperN.PartI
open MeasureTheory Filter GromovHausdorff
open scoped Topology
universe u

/-- `lem:convergent-invariant-lifts`: measures on the given carriers, not replacement spaces. -/
def InvariantLiftsStatement (hm : GHPMetricInput.{u}) : Prop :=
  letI := hm.metricSpace
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}),
    X.InvariantFullSupport →
    Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) →
    ∃ ν : ∀ n, ProbabilityMeasure (Xs n),
      (∀ n, ((Xs n).withProbability (ν n)).InvariantFullSupport) ∧
      Tendsto (fun n ↦ ((Xs n).withProbability (ν n)).toMeasuredGHSpace)
        atTop (𝓝 X.toMeasuredGHSpace)
end PaperN.PartI
