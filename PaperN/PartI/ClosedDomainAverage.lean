import PaperN.PartI.ClosedDomainLaws

namespace PaperN.PartI
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology

/-- Transporting convergent laws on a closed domain and averaging gives convergent probabilities.
The target is compact, but the domain and the laws' supports need not be compact. -/
theorem closedDomainAverage_tendsto
    {T Y Z : Type*} [MetricSpace T] [MetricSpace Y] [MetricSpace Z] [CompactSpace Z]
    [SecondCountableTopology T] [SecondCountableTopology Y]
    [MeasurableSpace T] [MeasurableSpace Y] [MeasurableSpace Z]
    [BorelSpace T] [BorelSpace Y] [BorelSpace Z]
    {ι : Type*} {l : Filter ι} (ts : ι → T) (t : T)
    (ηs : ι → ProbabilityMeasure Y) (η : ProbabilityMeasure Y)
    (s : Set (T × Y)) (hs : IsClosed s)
    (hηs : ∀ i, (ηs i : Measure Y) {y | (ts i, y) ∈ s} = 1)
    (hη : (η : Measure Y) {y | (t, y) ∈ s} = 1)
    (ht : Tendsto ts l (𝓝 t)) (hηlim : Tendsto ηs l (𝓝 η))
    (F : C(s, ProbabilityMeasure Z)) :
    Tendsto (fun i ↦ barycenter ((probabilityOnSubtype
      ((diracProba (ts i)).prod (ηs i)) s hs.measurableSet
      (diracProduct_fullMass _ _ _ hs.measurableSet (hηs i))).map
        F)) l
      (𝓝 (barycenter ((probabilityOnSubtype ((diracProba t).prod η) s hs.measurableSet
        (diracProduct_fullMass _ _ _ hs.measurableSet hη)).map
          F))) :=
  continuous_barycenter.continuousAt.tendsto.comp
    ((ProbabilityMeasure.continuous_map F.continuous).continuousAt.tendsto.comp
      (closedDomainLaw_tendsto ts t ηs η s hs hηs hη ht hηlim))
end PaperN.PartI
