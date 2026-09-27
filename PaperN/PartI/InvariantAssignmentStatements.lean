import PaperN.PartI.CommonRealization

namespace PaperN.PartI
open MeasureTheory Filter
open scoped Topology

/-- M1, M2 and M3 of `thm:invariant-measures` in the existing Type 0 whole-carrier model.
M3 quantifies arbitrary prescribed compact common embeddings, not merely existence of embeddings. -/
def InvariantAssignmentStatement : Prop :=
  ∃ μ : ∀ X : MeasuredCompact.{0}, ProbabilityMeasure X,
    (∀ X : MeasuredCompact.{0}, (μ X : Measure X).support = Set.univ ∧
      ∀ g : X ≃ᵢ X, Measure.map g (μ X : Measure X) = (μ X : Measure X)) ∧
    (∀ (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y),
      (μ X).map e = μ Y) ∧
    ∀ (Xs : ℕ → MeasuredCompact.{0}) (X : MeasuredCompact.{0})
      (C : CommonRealization Xs X), C.HausdorffConverges →
      Tendsto (fun n ↦ (μ (Xs n)).map (C.seqMap n))
        atTop (𝓝 ((μ X).map C.limitMap))
end PaperN.PartI
