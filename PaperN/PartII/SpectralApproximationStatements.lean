import PaperN.PartII.DistanceOperatorStatements

namespace PaperN.PartII
open MeasureTheory Metric Set
universe u
section Definitions
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

/-- Continuous representatives of eigenvectors for nonzero eigenvalues (including the zero vector). -/
def continuousEigenvectors : Set C(X, ℝ) :=
  {g | ∃ a : ℝ, a ≠ 0 ∧ distanceOperator μ (continuousToL2 μ g) = a • continuousToL2 μ g}

noncomputable def uniformSpectralSpan : Submodule ℝ C(X, ℝ) :=
  (Submodule.span ℝ (continuousEigenvectors μ)).topologicalClosure


end Definitions

/-- The uniform-closure conclusion used in the proof of lem:spectral-density. -/
def UniformSpectralSpanStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
    IsCompactOperator (distanceOperator μ) → IsSelfAdjoint (distanceOperator μ) →
    ∀ x : X, distanceProfile x ∈ uniformSpectralSpan μ

/-- A finite family of eigenfunctions; this does not yet specify the full cutoff space Vη. -/
def FiniteEigenfunctionApproximationStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure],
    IsCompactOperator (distanceOperator μ) → IsSelfAdjoint (distanceOperator μ) →
    ∀ ε > 0, ∃ S : Finset C(X, ℝ), (↑S : Set C(X, ℝ)) ⊆ continuousEigenvectors μ ∧
      (⨆ x : X, infDist (distanceProfile x) (Submodule.span ℝ (S : Set C(X, ℝ)))) < ε
end PaperN.PartII
