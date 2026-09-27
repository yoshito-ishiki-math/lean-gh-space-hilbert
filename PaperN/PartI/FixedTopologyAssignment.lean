import PaperN.PartI.FixedTopologyAssignmentStatements
import PaperN.PartI.UniverseAssignment

namespace PaperN.PartI
open MeasureTheory Set Filter Metric
open scoped Topology
universe u v w
local instance fixedMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance fixedBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- μ_X : D(X) → P(X), with the topology and Borel sigma algebra fixed before d is chosen. -/
noncomputable def fixedTopologyProbability (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (d : CompatibleMetric X) : ProbabilityMeasure X := by
  letI := d.toMetric
  exact universalProbability hm hs X

theorem fixedTopologyProbability_fullSupport (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (d : CompatibleMetric X) :
    (fixedTopologyProbability hm hs X d).toMeasure.support = univ := by
  letI := d.toMetric
  exact universalProbability_fullSupport hm hs X

theorem fixedTopologyProbability_natural (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) (Y : Type v) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [CompactSpace Y] [Nonempty Y]
    (d : CompatibleMetric X) (e : CompatibleMetric Y) :
    letI := d.toMetric
    letI := e.toMetric
    ∀ f : X ≃ᵢ Y, (fixedTopologyProbability hm hs X d).map
      f.continuous.measurable.aemeasurable = fixedTopologyProbability hm hs Y e := by
  letI := d.toMetric
  letI := e.toMetric
  exact fun f ↦ universalProbability_natural hm hs X Y f

theorem fixedTopologyProbability_tendsto (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    (Xs : ℕ → Type u) (X : Type v) (Z : Type w)
    [∀ n, TopologicalSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
    [TopologicalSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Z] [CompactSpace Z]
    (ds : ∀ n, CompatibleMetric (Xs n)) (d : CompatibleMetric X) :
    letI := fun n ↦ (ds n).toMetric
    letI := d.toMetric
    ∀ (es : ∀ n, Xs n → Z) (e : X → Z) (hes : ∀ n, Isometry (es n)) (he : Isometry e),
    Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0) →
    Tendsto (fun n ↦ (fixedTopologyProbability hm hs (Xs n) (ds n)).map
      (hes n).continuous.measurable.aemeasurable) atTop
      (𝓝 ((fixedTopologyProbability hm hs X d).map he.continuous.measurable.aemeasurable)) := by
  letI := fun n ↦ (ds n).toMetric
  letI := d.toMetric
  exact universalProbability_tendsto hm hp hs Xs X Z
/-- The manuscript theorem, with its D(X) domain, from the existing six cited inputs. -/
theorem fixedTopologyAssignment_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    FixedTopologyAssignmentStatement.{u} := by
  let hs := invariantFiberLawSelection_spec hm hp hc hg ha hv
  exact ⟨fixedTopologyProbability hm hs,
    fixedTopologyProbability_fullSupport hm hs,
    fixedTopologyProbability_natural hm hs,
    fixedTopologyProbability_tendsto hm hp hs⟩
theorem fixedTopologyProbability_radon (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm)
    (X : Type u) [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (d : CompatibleMetric X) :
    (fixedTopologyProbability hm hs X d).toMeasure.InnerRegularWRT
      (fun K ↦ IsCompact K ∧ IsClosed K) MeasurableSet := by
  letI := d.toMetric
  exact probability_innerRegular_polish _
end PaperN.PartI
