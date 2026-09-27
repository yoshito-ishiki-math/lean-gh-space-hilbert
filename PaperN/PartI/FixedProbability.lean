import PaperN.PartI.FixedProbabilityStatements
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

namespace PaperN.PartI
open MeasureTheory Set TopologicalSpace
open scoped Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Portmanteau makes positivity of an open set an open condition on probabilities. -/
theorem isOpen_probability_positive {U : Set X} (hU : IsOpen U) :
    IsOpen {μ : ProbabilityMeasure X | 0 < (μ : Measure X) U} := by
  have hlow : LowerSemicontinuous (fun μ : ProbabilityMeasure X ↦ (μ : Measure X) U) := by
    apply lowerSemicontinuous_iff_le_liminf.2
    intro μ
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (μ := μ) (μs := id) Filter.tendsto_id hU
  exact hlow.isOpen_preimage 0

omit [BorelSpace X] in
/-- Positivity on a countable nonempty basis characterizes full support. -/
theorem support_eq_univ_iff_basis_positive [SecondCountableTopology X]
    (μ : ProbabilityMeasure X) :
    (μ : Measure X).support = univ ↔
      ∀ U ∈ countableBasis X, 0 < (μ : Measure X) U := by
  constructor
  · intro h U hU
    have hne : U.Nonempty := Set.nonempty_iff_ne_empty.mpr (by
      intro he
      exact empty_notMem_countableBasis X (he ▸ hU))
    obtain ⟨x, hx⟩ := hne
    have hxμ : x ∈ (μ : Measure X).support := by rw [h]; trivial
    exact (Measure.mem_support_iff_forall x).mp hxμ U
      ((isOpen_of_mem_countableBasis hU).mem_nhds hx)
  · intro h
    apply Set.eq_univ_of_forall
    intro x
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hV, _, hVU⟩ := (isBasis_countableBasis X).mem_nhds_iff.mp hU
    exact lt_of_lt_of_le (h V hV) (measure_mono hVU)

theorem fixedFullSupportGDelta_spec [SecondCountableTopology X] :
    FixedFullSupportGDeltaStatement (X := X) := by
  have heq : {μ : ProbabilityMeasure X | (μ : Measure X).support = univ} =
      ⋂ U ∈ countableBasis X, {μ : ProbabilityMeasure X | 0 < (μ : Measure X) U} := by
    ext μ
    simp only [mem_setOf_eq, mem_iInter]
    exact support_eq_univ_iff_basis_positive μ
  change IsGδ _
  rw [heq]
  exact IsGδ.biInter_of_isOpen (countable_countableBasis X)
    (fun U hU ↦ isOpen_probability_positive (isOpen_of_mem_countableBasis hU))

/-- Arbitrary intersections suffice: the isometry group need not be countable. -/
theorem fixedInvariantClosed_spec : FixedInvariantClosedStatement (X := X) := by
  have heq : {μ : ProbabilityMeasure X | ∀ g : X ≃ᵢ X,
      Measure.map g (μ : Measure X) = (μ : Measure X)} =
      ⋂ g : X ≃ᵢ X, {μ : ProbabilityMeasure X |
        probabilityPushforward ⟨g, g.continuous⟩ μ = μ} := by
    ext μ
    simp only [mem_setOf_eq, mem_iInter]
    apply forall_congr'
    intro g
    constructor
    · intro h
      exact ProbabilityMeasure.toMeasure_injective h
    · intro h
      exact congrArg ProbabilityMeasure.toMeasure h
  change IsClosed _
  rw [heq]
  exact isClosed_iInter fun g ↦ isClosed_eq
    (probabilityPushforward ⟨g, g.continuous⟩).continuous continuous_id

theorem fixedInvariantFullSupportGDelta_spec [SecondCountableTopology X] :
    FixedInvariantFullSupportGDeltaStatement (X := X) := by
  exact (fixedFullSupportGDelta_spec (X := X)).inter
    (fixedInvariantClosed_spec (X := X)).isGδ

end PaperN.PartI
