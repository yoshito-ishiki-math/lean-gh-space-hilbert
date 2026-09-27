import PaperN.PartI.MeasuredCompact

namespace PaperN.PartI
open MeasureTheory
/-- Conditions M1 and M2 of `thm:invariant-measures`, without asserting varying-carrier continuity M3. -/
def NaturalInvariantAssignmentStatement : Prop :=
  ∃ μ : ∀ X : MeasuredCompact.{0}, ProbabilityMeasure X,
    (∀ X : MeasuredCompact.{0}, (μ X : Measure X).support = Set.univ ∧
      ∀ g : X ≃ᵢ X, Measure.map g (μ X : Measure X) = (μ X : Measure X)) ∧
    ∀ (X Y : MeasuredCompact.{0}) (e : X ≃ᵢ Y),
      (μ X).map e.continuous.measurable.aemeasurable = μ Y
end PaperN.PartI
