import PaperN.PartI.FamilyFiberAverage
import PaperN.PartI.BarycenterNaturality

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace Metric GromovHausdorff
open scoped Topology
universe u v

/-- A continuous lift between full-mass subsets transports their restricted laws. -/
theorem map_restrictedLaw_lift
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]
    (η : ProbabilityMeasure A) (ν : ProbabilityMeasure B) (s : Set A) (t : Set B)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hη : (η : Measure A) s = 1) (hν : (ν : Measure B) t = 1)
    (f : C(A, B)) (g : C(s, t)) (hg : ∀ x, (g x).val = f x.val)
    (hmap : η.map f = ν) :
    (probabilityOnSubtype η s hs hη).map g =
      probabilityOnSubtype ν t ht hν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply (MeasurableEmbedding.subtype_coe ht).map_injective
  have hleft : Measure.map Subtype.val
      (Measure.map g (probabilityOnSubtype η s hs hη : Measure s)) = (ν : Measure B) := by
    rw [Measure.map_map measurable_subtype_coe g.continuous.measurable]
    have heq : (Subtype.val ∘ g) = f ∘ Subtype.val := funext hg
    rw [heq, ← Measure.map_map f.continuous.measurable measurable_subtype_coe]
    have hrec := congrArg ProbabilityMeasure.toMeasure (map_probabilityOnSubtype η s hs hη)
    change Measure.map Subtype.val (probabilityOnSubtype η s hs hη : Measure s) = _ at hrec
    rw [hrec]
    exact congrArg ProbabilityMeasure.toMeasure hmap
  exact hleft.trans (congrArg ProbabilityMeasure.toMeasure
    (map_probabilityOnSubtype ν t ht hν)).symm

/-- The joint-domain average is precisely the ambient pushforward of the existing
carrier-wise average; it is not a different selection construction. -/
theorem familyFiberAverage_eq_map (hm : GHPMetricInput.{u}) (hp : GHPPolishInput hm)
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
    ∀ (t : T) (η : ProbabilityMeasure InvariantMeasuredGHSpace.{u})
      (hη : (η : Measure InvariantMeasuredGHSpace.{u})
        {q | q.val.forget = toGHSpace (Xs t)} = 1),
      familyFiberAverage hm hp Xs e he hH t η hη =
      (averageConcentratedLaw hm (Xs t) η hη).map (e t) := by
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
  let θ : ProbabilityMeasure (InvariantFiber (Xs t)) := probabilityOnSubtype η _ (isClosed_invariantFiber hm (Xs t)).measurableSet hη
  let ν := (diracProba t).prod η
  have hν : (ν : Measure (T × InvariantMeasuredGHSpace.{u})) s = 1 :=
    diracProduct_fullMass t η s hs.measurableSet hη
  let L := probabilityOnSubtype ν s hs.measurableSet hν
  let f : C(InvariantMeasuredGHSpace.{u}, T × InvariantMeasuredGHSpace.{u}) :=
    ⟨fun q ↦ (t, q), continuous_const.prodMk continuous_id⟩
  let g : C(InvariantFiber (Xs t), s) :=
    ⟨fun q ↦ ⟨(t, q.val), q.property⟩,
      (continuous_const.prodMk continuous_subtype_val).subtype_mk _⟩
  have hmap : η.map f = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    exact (Measure.dirac_prod (ν := (η : Measure InvariantMeasuredGHSpace.{u})) t).symm
  have hL : θ.map g = L :=
    map_restrictedLaw_lift η ν _ s _ hs.measurableSet hη hν f g (fun _ ↦ rfl) hmap
  change barycenter (L.map (familyFiberProbability Xs e he)) =
    (barycenter (transportedFiberLaw hm (Xs t) θ)).map (e t)
  erw [barycenter_map ⟨e t, (he t).continuous⟩, ← hL]
  apply congrArg barycenter
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (familyFiberProbability Xs e he) (Measure.map g (θ : Measure (InvariantFiber (Xs t)))) =
    Measure.map (probabilityPushforward ⟨e t, (he t).continuous⟩)
      (Measure.map (fiberProbability (Xs t)) (θ : Measure (InvariantFiber (Xs t))))
  rw [Measure.map_map (continuous_familyFiberProbability hm Xs e he hH).measurable g.continuous.measurable,
    Measure.map_map (probabilityPushforward ⟨e t, (he t).continuous⟩).continuous.measurable
      (continuous_fiberProbability hm (Xs t)).measurable]
  rfl
end PaperN.PartI
