import PaperN.PartI.ValovInput
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

namespace PaperN.PartI
open MeasureTheory
open scoped BoundedContinuousFunction
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [MeasurableSpace X] [BorelSpace X]

/-- The averaging-operator remark, including its norm-one projection conclusion. -/
def LawAveragingStatement (p : C(X, Y)) (s : C(Y, ProbabilityMeasure X)) : Prop :=
  ∃ (A : (X →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ)) (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)),
    (∀ f y, A f y = ∫ x, f x ∂(s y : Measure X)) ∧
    (∀ f, 0 ≤ f → 0 ≤ A f) ∧ A 1 = 1 ∧ (∀ f, ‖A f‖ ≤ ‖f‖) ∧
    (∀ f : Y →ᵇ ℝ, A (f.compContinuous p) = f) ∧
    (∀ f, P f = (A f).compContinuous p) ∧
    (∀ f, P (P f) = P f) ∧
    Set.range P = Set.range (fun f : Y →ᵇ ℝ ↦ f.compContinuous p) ∧ ‖P‖ = 1
end PaperN.PartI
