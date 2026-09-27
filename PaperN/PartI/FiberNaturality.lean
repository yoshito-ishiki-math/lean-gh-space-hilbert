import PaperN.PartI.FiberLawAverage
import PaperN.PartI.BarycenterNaturality

set_option backward.isDefEq.respectTransparency false

namespace PaperN.PartI
open MeasureTheory Set GromovHausdorff
universe u

/-- The same measured class belongs to the fibers of any two isometric carriers. -/
def fiberReindex {X Y : MeasuredCompact.{u}} (e : X ≃ᵢ Y) : InvariantFiber X → InvariantFiber Y :=
  fun q ↦ ⟨q.val, q.property.trans (toGHSpace_eq_toGHSpace_iff_isometryEquiv.mpr ⟨e⟩)⟩

/-- Naturality of averages for laws with the same image in the ambient invariant GHP space. -/
theorem fiberLawAverage_natural (hm : GHPMetricInput.{u}) {X Y : MeasuredCompact.{u}}
    (e : X ≃ᵢ Y) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
    letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
    ∀ (ηx : ProbabilityMeasure (InvariantFiber X)) (ηy : ProbabilityMeasure (InvariantFiber Y)),
      ηx.map Subtype.val = ηy.map Subtype.val →
      (fiberLawAverage hm X ηx).map e =
        fiberLawAverage hm Y ηy := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro ηx ηy hη
  have hr : Continuous (fiberReindex e) := continuous_subtype_val.subtype_mk _
  have hLaw : Measure.map (fiberReindex e) (ηx : Measure (InvariantFiber X)) =
      (ηy : Measure (InvariantFiber Y)) := by
    apply (MeasurableEmbedding.subtype_coe (isClosed_invariantFiber hm Y).measurableSet).map_injective
    erw [Measure.map_map measurable_subtype_coe hr.measurable]
    exact congrArg ProbabilityMeasure.toMeasure hη
  change (barycenter (transportedFiberLaw hm X ηx)).map e = _
  erw [barycenter_map ⟨e, e.continuous⟩]
  apply congrArg barycenter
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (probabilityPushforward ⟨e, e.continuous⟩)
    (Measure.map (fiberProbability X) (ηx : Measure (InvariantFiber X))) =
      Measure.map (fiberProbability Y) (ηy : Measure (InvariantFiber Y))
  rw [← hLaw, Measure.map_map (continuous_fiberProbability hm Y).measurable hr.measurable,
    Measure.map_map (probabilityPushforward ⟨e, e.continuous⟩).continuous.measurable
      (continuous_fiberProbability hm X).measurable]
  congr 1
  funext q
  exact (fiberProbability_natural e q (fiberReindex e q) rfl).symm

/-- Restriction of one ambient law to the two equal fibers makes the compatibility automatic. -/
theorem averageConcentratedLaw_natural (hm : GHPMetricInput.{u}) {X Y : MeasuredCompact.{u}}
    (e : X ≃ᵢ Y) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
    letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
    ∀ (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (hx : (η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace X} = 1)
      (hy : (η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace Y} = 1),
      (averageConcentratedLaw hm X η hx).map e =
        averageConcentratedLaw hm Y η hy := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro η hx hy
  apply fiberLawAverage_natural hm e
  erw [map_probabilityOnSubtype, map_probabilityOnSubtype]
end PaperN.PartI
