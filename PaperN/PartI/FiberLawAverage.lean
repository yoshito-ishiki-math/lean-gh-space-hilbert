import PaperN.PartI.FiberTopology
import PaperN.PartI.ProbabilityRestriction
import PaperN.PartI.FixedLawAverage
import PaperN.PartI.GHPExternal

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff
open scoped Topology BoundedContinuousFunction
universe u
theorem isClosed_invariantFiber (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  IsClosed {q : InvariantMeasuredGHSpace.{u} | q.val.forget = toGHSpace X} := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  exact isClosed_eq ((ghpForgetLipschitz_spec hm).continuous.comp continuous_subtype_val) continuous_const

/-- Push a law on the actual fiber to probabilities on the specified carrier. -/
noncomputable def transportedFiberLaw (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ProbabilityMeasure (InvariantFiber X) → ProbabilityMeasure (ProbabilityMeasure X) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η
  exact η.map (fiberProbability X)

/-- The concrete barycenter after transport from the measured-isometry fiber. -/
noncomputable def fiberLawAverage (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ProbabilityMeasure (InvariantFiber X) → ProbabilityMeasure X := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η
  exact barycenter (transportedFiberLaw hm X η)

theorem transportedFiberLaw_fullMass (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ∀ η : ProbabilityMeasure (InvariantFiber X),
    (transportedFiberLaw hm X η : Measure (ProbabilityMeasure X))
      {μ | (μ : Measure X).support = univ ∧
        ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)} = 1 := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η
  rw [transportedFiberLaw, ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (continuous_fiberProbability hm X).measurable measurableSet_fixedInvariantFullSupport]
  have he : (fiberProbability X) ⁻¹' {μ : ProbabilityMeasure X |
      (μ : Measure X).support = univ ∧
        ∀ g : X ≃ᵢ X, Measure.map g (μ : Measure X) = (μ : Measure X)} = univ := by
    apply eq_univ_of_forall
    intro q
    exact fiberProbability_fullSupport_invariant X q
  rw [he, measure_univ]

theorem fiberLawAverage_fullSupport_invariant (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ∀ η : ProbabilityMeasure (InvariantFiber X),
    (X.withProbability (fiberLawAverage hm X η)).InvariantFullSupport := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η
  exact fixedLawAverage_spec (transportedFiberLaw hm X η) (transportedFiberLaw_fullMass hm X η)

/-- Continuity here holds for laws on a fixed carrier only. -/
theorem continuous_fiberLawAverage (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  Continuous (fiberLawAverage hm X) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  exact continuous_barycenter.comp (ProbabilityMeasure.continuous_map (continuous_fiberProbability hm X))

/-- The iterated-integral formula for a law on the actual fiber. -/
theorem integral_fiberLawAverage (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ∀ (η : ProbabilityMeasure (InvariantFiber X)) (f : X →ᵇ ℝ),
    (∫ x, f x ∂(fiberLawAverage hm X η : Measure X)) =
      ∫ q, ∫ x, f x ∂(fiberProbability X q : Measure X) ∂(η : Measure (InvariantFiber X)) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η f
  rw [fiberLawAverage, integral_barycenter _ (f.integrable _)]
  exact integral_map (continuous_fiberProbability hm X).measurable.aemeasurable
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).aestronglyMeasurable

/-- Restrict an ambient law concentrated on the fiber, then transport and average it. -/
noncomputable def averageConcentratedLaw (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u}) →
    ((η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace X} = 1) →
    ProbabilityMeasure X := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η hη
  exact fiberLawAverage hm X
    (probabilityOnSubtype η _ (isClosed_invariantFiber hm X).measurableSet hη)

theorem averageConcentratedLaw_fullSupport_invariant (hm : GHPMetricInput.{u}) (X : MeasuredCompact.{u}) :
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  ∀ (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u})
    (hη : (η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace X} = 1),
    (X.withProbability (averageConcentratedLaw hm X η hη)).InvariantFullSupport := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η hη
  exact fiberLawAverage_fullSupport_invariant hm X _
end PaperN.PartI
