import PaperN.PartII.DistanceKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u

/-- Maria--Oudot--Solomon, Definition 11 and Propositions 12--13.
Only the cited compactness and self-adjointness are external inputs. -/
def DistanceKernelSpectralInput : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ],
    IsCompactOperator (distanceOperator μ) ∧ IsSelfAdjoint (distanceOperator μ)

/-- All conclusions of lem:distance-operator, with an explicit continuous realization. -/
def DistanceOperatorStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure],
    IsCompactOperator (distanceOperator μ) ∧ IsSelfAdjoint (distanceOperator μ) ∧
    (∀ f : Lp ℝ 2 μ,
      continuousToL2 μ (distanceToContinuous μ f) = distanceOperator μ f ∧
      (∀ x, distanceToContinuous μ f x = ∫ y, dist x y * f y ∂μ) ∧
      ‖distanceToContinuous μ f‖ ≤ diam (univ : Set X) * ‖f‖ ∧
      (∀ x y, |distanceToContinuous μ f x - distanceToContinuous μ f y| ≤ dist x y * ‖f‖)) ∧
    (∀ (f : Lp ℝ 2 μ) (a : ℝ), a ≠ 0 → distanceOperator μ f = a • f →
      ∃! g : C(X, ℝ), continuousToL2 μ g = f)
end PaperN.PartII
