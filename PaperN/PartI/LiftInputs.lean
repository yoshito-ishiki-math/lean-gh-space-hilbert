import PaperN.PartI.Remeasure
import PaperN.PartI.MeasuredProjection

/-! Explicit cited inputs from Khezeli, arXiv:1812.03760v5.
No values are supplied. Neither input contains invariant measures or full support. -/
namespace PaperN.PartI
open MeasureTheory Filter GromovHausdorff
open scoped Topology
universe u

/-- Lemma 2.5 with the singleton constant functor of Example 2.19.
The probabilities carried by `Xs` and `X` are ignored by this geometric input. -/
def GHCommonEmbeddingInput : Prop :=
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}),
    Tendsto (fun n ↦ toGHSpace (Xs n)) atTop (𝓝 (toGHSpace X)) →
    ∃ C : CommonRealization Xs X, C.HausdorffConverges

/-- Lemma 2.13, Example 2.1(iii), and Remarks 2.14(ii)/2.15:
ordinary probabilities approximate a prescribed limiting probability in Prokhorov distance. -/
def ProbabilityApproximationInput : Prop :=
  ∀ (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    (C : CommonRealization Xs X), C.HausdorffConverges →
    ∃ μ : ∀ n, ProbabilityMeasure (Xs n), (C.withProbabilities μ).ProkhorovConverges
end PaperN.PartI
