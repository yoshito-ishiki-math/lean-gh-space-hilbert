import PaperN.PartI.HaarAverage
import PaperN.PartI.Statements
import PaperN.PartI.MetricBump
import PaperN.PartI.Barycenter

namespace PaperN.PartI
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

/-- Explicit bridge from the manuscript's measure-support convention. -/
lemma openPos_of_support_eq_univ {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (hμ : μ.support = univ) : IsOpenPosMeasure μ := by
  constructor
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  have hxμ : x ∈ μ.support := by rw [hμ]; trivial
  exact ((mem_support_iff_forall x).1 hxμ U (hU.mem_nhds hx)).ne'

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

theorem metricBump_spec : MetricBumpStatement (X := X) := by
  intro μ r hr
  exact ⟨fun x y ↦ ⟨metricBump_nonneg x y r, metricBump_le_one x y hr⟩,
    fun x x' y y' ↦ metricBump_lipschitz x x' y y' hr,
    fun x ↦ (metricBump_integral_bounds (μ : Measure X) x hr).1,
    fun x ↦ (metricBump_integral_bounds (μ : Measure X) x hr).2⟩

theorem normalizedMetricBump_spec : NormalizedMetricBumpStatement (X := X) := by
  intro μ hμ x r hr
  letI := openPos_of_support_eq_univ (μ : Measure X) hμ
  exact normalizedMetricBump_properties (μ : Measure X) x hr

theorem continuousBarycenter_spec : ContinuousBarycenterStatement (X := X) := by
  refine ⟨fun η f ↦ integral_barycenter_continuous η f, ?_, continuous_barycenter, ?_, ?_⟩
  · intro b hb
    funext η
    exact barycenter_unique_continuous η (b η) (hb η)
  · intro η S hS hηS hfull
    have hmem : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)), μ ∈ S :=
      (mem_ae_iff_prob_eq_one hS).2 hηS
    have hη : ∀ᵐ μ : ProbabilityMeasure X ∂(η : Measure (ProbabilityMeasure X)),
        IsOpenPosMeasure (μ : Measure X) := by
      filter_upwards [hmem] with μ hμ
      exact openPos_of_support_eq_univ (μ : Measure X) (hfull μ hμ)
    letI := barycenter_fullSupport η hη
    exact Measure.support_eq_univ
  · intro η g hη
    exact barycenter_invariant η g.continuous.measurable hη

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactIsometryGroup_spec : CompactIsometryGroupStatement (X := X) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem invariantFullSupport_spec [Nonempty X] : InvariantFullSupportStatement (X := X) :=
  exists_invariant_fullSupport_probability

end PaperN.PartI
