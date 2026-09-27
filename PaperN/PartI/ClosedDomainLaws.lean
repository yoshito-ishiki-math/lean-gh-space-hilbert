import PaperN.PartI.ProbabilityRestriction
import PaperN.PartI.ClosedDomainLawsStatements
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace Topology
open scoped Topology BoundedContinuousFunction

/-- Weak convergence can be tested after a closed embedding into a normal space. -/
theorem probability_tendsto_of_closedEmbedding
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] [NormalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B]
    {e : A → B} (he : IsClosedEmbedding e)
    {ι : Type*} {l : Filter ι} (μs : ι → ProbabilityMeasure A) (μ : ProbabilityMeasure A)
    (h : Tendsto (fun i ↦ (μs i).map he.continuous.measurable.aemeasurable) l
      (𝓝 (μ.map he.continuous.measurable.aemeasurable))) :
    Tendsto μs l (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  obtain ⟨g, _, hg⟩ := f.exists_extension_norm_eq_of_isClosedEmbedding he
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h g
  have hfun : (fun x ↦ g (e x)) = f := hg
  simpa only [ProbabilityMeasure.toMeasure_map,
    integral_map he.continuous.measurable.aemeasurable g.continuous.aestronglyMeasurable,
    hfun] using ht

/-- Restricting full-mass laws to a fixed closed domain preserves weak convergence.
No compactness of the domain or of the laws' supports is assumed. -/
theorem probabilityOnSubtype_tendsto
    {A : Type*} [TopologicalSpace A] [NormalSpace A] [MeasurableSpace A] [BorelSpace A]
    {ι : Type*} {l : Filter ι} (μs : ι → ProbabilityMeasure A) (μ : ProbabilityMeasure A)
    (s : Set A) (hs : IsClosed s) (hμs : ∀ i, (μs i : Measure A) s = 1)
    (hμ : (μ : Measure A) s = 1) (h : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun i ↦ probabilityOnSubtype (μs i) s hs.measurableSet (hμs i)) l
      (𝓝 (probabilityOnSubtype μ s hs.measurableSet hμ)) := by
  apply probability_tendsto_of_closedEmbedding hs.isClosedEmbedding_subtypeVal
  simpa only [map_probabilityOnSubtype] using h

/-- `lem:dirac-product-convergence`; neither factor needs compact support. -/
theorem diracProduct_tendsto
    {T Y : Type*} [MetricSpace T] [MetricSpace Y]
    [SecondCountableTopology T] [SecondCountableTopology Y]
    [MeasurableSpace T] [MeasurableSpace Y] [BorelSpace T] [BorelSpace Y]
    {ι : Type*} {l : Filter ι} (ts : ι → T) (t : T)
    (ηs : ι → ProbabilityMeasure Y) (η : ProbabilityMeasure Y)
    (ht : Tendsto ts l (𝓝 t)) (hη : Tendsto ηs l (𝓝 η)) :
    Tendsto (fun i ↦ (diracProba (ts i)).prod (ηs i)) l (𝓝 ((diracProba t).prod η)) :=
  ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((continuous_diracProba.continuousAt.tendsto.comp ht).prodMk_nhds hη)

/-- Dirac product laws give full mass to a domain exactly when their time slice does. -/
theorem diracProduct_fullMass
    {T Y : Type*} [MeasurableSpace T] [MeasurableSpace Y]
    (t : T) (η : ProbabilityMeasure Y) (s : Set (T × Y)) (hs : MeasurableSet s)
    (h : (η : Measure Y) {y | (t, y) ∈ s} = 1) :
    ((diracProba t).prod η : Measure (T × Y)) s = 1 := by
  change (Measure.dirac t).prod (η : Measure Y) s = 1
  rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hs]
  exact h

/-- Convergence of laws on a fixed closed domain containing the moving time slices. -/
theorem closedDomainLaw_tendsto
    {T Y : Type*} [MetricSpace T] [MetricSpace Y]
    [SecondCountableTopology T] [SecondCountableTopology Y]
    [MeasurableSpace T] [MeasurableSpace Y] [BorelSpace T] [BorelSpace Y]
    {ι : Type*} {l : Filter ι} (ts : ι → T) (t : T)
    (ηs : ι → ProbabilityMeasure Y) (η : ProbabilityMeasure Y)
    (s : Set (T × Y)) (hs : IsClosed s)
    (hηs : ∀ i, (ηs i : Measure Y) {y | (ts i, y) ∈ s} = 1)
    (hη : (η : Measure Y) {y | (t, y) ∈ s} = 1)
    (ht : Tendsto ts l (𝓝 t)) (hηlim : Tendsto ηs l (𝓝 η)) :
    Tendsto (fun i ↦ probabilityOnSubtype ((diracProba (ts i)).prod (ηs i)) s hs.measurableSet
      (diracProduct_fullMass _ _ _ hs.measurableSet (hηs i))) l
      (𝓝 (probabilityOnSubtype ((diracProba t).prod η) s hs.measurableSet
        (diracProduct_fullMass _ _ _ hs.measurableSet hη))) :=
  probabilityOnSubtype_tendsto _ _ s hs _ _ (diracProduct_tendsto ts t ηs η ht hηlim)
/-- The exact compact-parameter/Polish-carrier statement, proved from mathlib. -/
theorem diracProduct_spec : DiracProductConvergenceStatement := by
  intro T Y _ _ _ _ _ _ _ _ ts t ηs η ht hη
  letI := TopologicalSpace.metrizableSpaceMetric Y
  exact diracProduct_tendsto ts t ηs η ht hη
end PaperN.PartI
