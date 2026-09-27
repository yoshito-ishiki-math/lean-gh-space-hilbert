import PaperN.PartI.IsometryGroupDefs
import Mathlib.Topology.Algebra.Group.Basic
import PaperN.PartI.Definitions
import PaperN.PartI.ProbabilityTopology
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Algebra.Support

/-! Reviewable full statements of the five completed lemmas.
No proof of the five results is imported here. ProbabilityTopology proves the
library bridge identifying Giry and weak Borel structures. -/
namespace PaperN.PartI
open MeasureTheory Metric
open scoped Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- lem:metric-bump, including the range, two-variable estimate and both integral bounds. -/
def MetricBumpStatement : Prop :=
  ∀ (μ : ProbabilityMeasure X) (r : ℝ), 0 < r →
    (∀ x y : X, 0 ≤ metricBump x r y ∧ metricBump x r y ≤ 1) ∧
    (∀ x x' y y' : X, |metricBump x r y - metricBump x' r y'| ≤
      (dist x x' + dist y y') / r) ∧
    (∀ x, (1 / 2 : ℝ) * (μ : Measure X).real (ball x (r / 2)) ≤
      ∫ y, metricBump x r y ∂(μ : Measure X)) ∧
    (∀ x, (∫ y, metricBump x r y ∂(μ : Measure X)) ≤ (μ : Measure X).real (ball x r))

/-- lem:normalized-metric-bump, with measure support and closed function support explicit. -/
def NormalizedMetricBumpStatement : Prop :=
  ∀ (μ : ProbabilityMeasure X), (μ : Measure X).support = Set.univ →
    ∀ (x : X) (r : ℝ), 0 < r →
      (0 < ∫ z, metricBump x (r / 2) z ∂(μ : Measure X)) ∧
      Continuous (normalizedMetricBump (μ : Measure X) x r) ∧
      (∀ y, 0 ≤ normalizedMetricBump (μ : Measure X) x r y) ∧
      (∫ y, normalizedMetricBump (μ : Measure X) x r y ∂(μ : Measure X)) = 1 ∧
      tsupport (normalizedMetricBump (μ : Measure X) x r) ⊆ ball x r

/-- The exact real continuous-test-function identity of the barycenter lemma. -/
def BarycenterIdentity (η : ProbabilityMeasure (ProbabilityMeasure X))
    (ν : ProbabilityMeasure X) : Prop :=
  ∀ f : C(X, ℝ), ∫ x, f x ∂(ν : Measure X) =
    ∫ μ : ProbabilityMeasure X, ∫ x, f x ∂(μ : Measure X) ∂η

/-- lem:continuous-barycenter, including uniqueness of the entire map, continuity,
full support for laws concentrated on a Borel set, and isometry invariance. -/
def ContinuousBarycenterStatement : Prop :=
  (∀ η, BarycenterIdentity (X := X) η (barycenter η)) ∧
  (∀ b : ProbabilityMeasure (ProbabilityMeasure X) → ProbabilityMeasure X,
    (∀ η, BarycenterIdentity η (b η)) → b = barycenter) ∧
  Continuous (barycenter : ProbabilityMeasure (ProbabilityMeasure X) → ProbabilityMeasure X) ∧
  (∀ (η : ProbabilityMeasure (ProbabilityMeasure X)) (S : Set (ProbabilityMeasure X)),
    MeasurableSet S → (η : Measure (ProbabilityMeasure X)) S = 1 →
    (∀ μ ∈ S, (μ : Measure X).support = Set.univ) →
    (barycenter η : Measure X).support = Set.univ) ∧
  (∀ (η : ProbabilityMeasure (ProbabilityMeasure X)) (g : X ≃ᵢ X),
    (∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)),
      Measure.map g (μ : Measure X) = (μ : Measure X)) →
    Measure.map g (barycenter η : Measure X) = (barycenter η : Measure X))

/-- lem:compact-isometry-group, for the uniform metric defined in IsometryGroupDefs. -/
def CompactIsometryGroupStatement : Prop :=
  CompactSpace (X ≃ᵢ X) ∧ TopologicalSpace.MetrizableSpace (X ≃ᵢ X) ∧
    IsTopologicalGroup (X ≃ᵢ X)

/-- lem:invariant-full-support, with invariance under every surjective self-isometry. -/
def InvariantFullSupportStatement : Prop :=
  ∃ μ : ProbabilityMeasure X, (μ : Measure X).support = Set.univ ∧
    ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)

end PaperN.PartI
