import PaperN.PartI.FamilyAverageIdentification
import PaperN.PartI.CommonIsometryGraph
import Mathlib.Topology.Category.LightProfinite.Sequence

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace Metric GromovHausdorff
open scoped Topology OnePoint
universe u

/-- Package a sequence of carriers and its limit as a family on the convergent-sequence space. -/
def sequenceCarrier (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u}) :
    OnePoint ℕ → MeasuredCompact.{u} := fun t ↦ t.elim X Xs

def CommonRealization.sequenceEmbedding {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) : ∀ t, sequenceCarrier Xs X t → C :=
  OnePoint.rec C.limitMap C.seqMap

theorem CommonRealization.sequenceEmbedding_isometry
    {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) : ∀ t, Isometry (C.sequenceEmbedding t) :=
  OnePoint.rec C.limit_isometry C.seq_isometry

/-- The actual prescribed carrier images give a continuous hyperspace-valued family. -/
theorem CommonRealization.continuous_sequenceImages
    {Xs : ℕ → MeasuredCompact.{u}} {X : MeasuredCompact.{u}}
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) :
    Continuous (fun t : OnePoint ℕ ↦ t.elim C.limitSet C.seqSet) := by
  apply (OnePoint.continuous_iff_from_nat _).mpr
  exact tendsto_iff_dist_tendsto_zero.mpr hH

/-- Restricting and averaging arbitrary convergent fiber laws commutes with the prescribed
varying-carrier embeddings. This concerns the existing carrier-wise average. -/
theorem averageConcentratedLaw_tendsto (hm : GHPMetricInput.{u}) (hp : GHPPolishInput hm)
    (Xs : ℕ → MeasuredCompact.{u}) (X : MeasuredCompact.{u})
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
    letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
    ∀ (ηs : ℕ → ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (hηs : ∀ n, (ηs n : Measure InvariantMeasuredGHSpace.{u})
        {q | q.val.forget = toGHSpace (Xs n)} = 1)
      (hη : (η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace X} = 1),
      Tendsto ηs atTop (𝓝 η) →
      Tendsto (fun n ↦ (averageConcentratedLaw hm (Xs n) (ηs n) (hηs n)).map
        (C.seq_isometry n).continuous.measurable.aemeasurable) atTop
        (𝓝 ((averageConcentratedLaw hm X η hη).map C.limit_isometry.continuous.measurable.aemeasurable)) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  letI := TopologicalSpace.metrizableSpaceMetric (OnePoint ℕ)
  letI : MeasurableSpace (OnePoint ℕ) := borel _
  letI : BorelSpace (OnePoint ℕ) := ⟨rfl⟩
  intro ηs η hηs hη hlim
  let F := sequenceCarrier Xs X
  let e := C.sequenceEmbedding
  have he := C.sequenceEmbedding_isometry
  let K : OnePoint ℕ → NonemptyCompacts C := fun t ↦ t.elim C.limitSet C.seqSet
  have hK : Continuous K := C.continuous_sequenceImages hH
  have hKe (t : OnePoint ℕ) : (K t : Set C) = range (e t) := by
    cases t using OnePoint.rec <;> rfl
  have hF : ∀ (ts : ℕ → OnePoint ℕ) (t : OnePoint ℕ), Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n ↦ hausdorffDist (range (e (ts n))) (range (e t))) atTop (𝓝 0) := by
    intro ts t ht
    have h := tendsto_iff_dist_tendsto_zero.mp (hK.continuousAt.tendsto.comp ht)
    simpa only [Function.comp_def, NonemptyCompacts.dist_eq, hKe] using h
  have ht : Tendsto (fun n : ℕ ↦ (n : OnePoint ℕ)) atTop (𝓝 ∞) :=
    (OnePoint.continuous_iff_from_nat id).mp continuous_id
  have h := familyFiberAverage_tendsto hm hp F e he hF
    (fun n : ℕ ↦ (n : OnePoint ℕ)) ∞ ηs η hηs hη ht hlim
  simp only [familyFiberAverage_eq_map] at h
  convert h using 1 <;> rfl
end PaperN.PartI
