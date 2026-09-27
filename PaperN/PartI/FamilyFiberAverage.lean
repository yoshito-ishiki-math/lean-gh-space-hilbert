import PaperN.PartI.ParameterizedFiberTransport
import PaperN.PartI.ClosedDomainAverage

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace Metric GromovHausdorff
open scoped Topology
universe u v

/-- Average a law on one time slice of the joint closed fiber domain in the fixed ambient space. -/
noncomputable def familyFiberAverage (hm : GHPMetricInput.{u}) (hp : GHPPolishInput hm)
    {T : Type v} [MetricSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (Xs : T → MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : ∀ t, Xs t → Z) (he : ∀ t, Isometry (e t))
    (hH : ∀ (ts : ℕ → T) (t : T), Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n ↦ hausdorffDist (range (e (ts n))) (range (e t))) atTop (𝓝 0)) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
    letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
    (t : T) → (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u}) →
    ((η : Measure InvariantMeasuredGHSpace.{u}) {q | q.val.forget = toGHSpace (Xs t)} = 1) →
    ProbabilityMeasure Z := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI := hp.separable
  letI : SecondCountableTopology InvariantMeasuredGHSpace.{u} :=
    inferInstanceAs (SecondCountableTopology {x : MeasuredGHSpace.{u} // x.invariantFullSupport})
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro t η hη
  let s := {p : T × InvariantMeasuredGHSpace.{u} | p.2.val.forget = toGHSpace (Xs p.1)}
  have hs : IsClosed s := isClosed_familyFiber hm Xs (continuous_familyGH Xs e he hH)
  let law :=  probabilityOnSubtype ((diracProba t).prod η) s hs.measurableSet
    (diracProduct_fullMass t η s hs.measurableSet hη)
  exact barycenter (law.map (familyFiberProbability Xs e he))

/-- The joint-domain construction has the required varying-parameter convergence.
Identification with the existing carrier-wise average is proved in FamilyAverageIdentification. -/
theorem familyFiberAverage_tendsto (hm : GHPMetricInput.{u}) (hp : GHPPolishInput hm)
    {T : Type v} [MetricSpace T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (Xs : T → MeasuredCompact.{u})
    {Z : Type u} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (e : ∀ t, Xs t → Z) (he : ∀ t, Isometry (e t))
    (hH : ∀ (ts : ℕ → T) (t : T), Tendsto ts atTop (𝓝 t) →
      Tendsto (fun n ↦ hausdorffDist (range (e (ts n))) (range (e t))) atTop (𝓝 0)) :
    letI := hm.metricSpace
    letI := hm.invariantMetricSpace
    letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
    letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
    ∀ (ts : ℕ → T) (t : T)
      (ηs : ℕ → ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (hηs : ∀ n, (ηs n : Measure InvariantMeasuredGHSpace.{u})
        {q | q.val.forget = toGHSpace (Xs (ts n))} = 1)
      (hη : (η : Measure InvariantMeasuredGHSpace.{u})
        {q | q.val.forget = toGHSpace (Xs t)} = 1),
      Tendsto ts atTop (𝓝 t) → Tendsto ηs atTop (𝓝 η) →
      Tendsto (fun n ↦ familyFiberAverage hm hp Xs e he hH (ts n) (ηs n) (hηs n)) atTop
        (𝓝 (familyFiberAverage hm hp Xs e he hH t η hη)) := by
  letI := hm.metricSpace
  letI := hm.invariantMetricSpace
  letI := hp.separable
  letI : SecondCountableTopology InvariantMeasuredGHSpace.{u} :=
    inferInstanceAs (SecondCountableTopology {x : MeasuredGHSpace.{u} // x.invariantFullSupport})
  letI : MeasurableSpace InvariantMeasuredGHSpace.{u} := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{u} := ⟨rfl⟩
  intro ts t ηs η hηs hη ht hηlim
  exact closedDomainAverage_tendsto ts t ηs η _
    (isClosed_familyFiber hm Xs (continuous_familyGH Xs e he hH)) hηs hη ht hηlim
    ⟨familyFiberProbability Xs e he, continuous_familyFiberProbability hm Xs e he hH⟩
end PaperN.PartI
