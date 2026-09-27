import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

namespace PaperN.PartI
open MeasureTheory Set TopologicalSpace
open scoped NNReal ENNReal BoundedContinuousFunction Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
private lemma probability_topology_eq :
    (inferInstance : TopologicalSpace (ProbabilityMeasure X)) =
      ⨅ f : X →ᵇ ℝ≥0, TopologicalSpace.induced
        (fun μ : ProbabilityMeasure X ↦ μ.toFiniteMeasure.testAgainstNN f)
        inferInstance := by
  change TopologicalSpace.induced _ (TopologicalSpace.induced _
    (TopologicalSpace.induced _ Pi.topologicalSpace)) = _
  simp only [induced_compose, Pi.topologicalSpace, induced_iInf]
  rfl

/-- All weakly open sets of probabilities on a compact metric space are Giry measurable.
This bridge is needed before forming probability laws on the space of probabilities. -/
instance probabilityOpensMeasurable : OpensMeasurableSpace (ProbabilityMeasure X) := by
  let S : Set (Set (ProbabilityMeasure X)) :=
    ⋃ f : X →ᵇ ℝ≥0, (Set.preimage (fun μ : ProbabilityMeasure X ↦ μ.toFiniteMeasure.testAgainstNN f)) ''
      {U : Set ℝ≥0 | IsOpen U}
  have htop : (inferInstance : TopologicalSpace (ProbabilityMeasure X)) =
      TopologicalSpace.generateFrom S := by
    rw [probability_topology_eq]
    dsimp [S]
    rw [generateFrom_iUnion]
    congr 1
    funext f
    rw [← induced_generateFrom_eq, generateFrom_setOf_isOpen]
  constructor
  rw [borel_eq_generateFrom_of_subbasis htop]
  apply MeasurableSpace.generateFrom_le
  intro U hU
  obtain ⟨f, V, hV, rfl⟩ := mem_iUnion.1 hU
  have hf : Measurable (fun μ : ProbabilityMeasure X ↦ μ.toFiniteMeasure.testAgainstNN f) :=
    ((Measure.measurable_lintegral f.measurable_coe_ennreal_comp).comp
      measurable_subtype_coe).ennreal_toNNReal
  exact hf (show IsOpen V from hV).measurableSet

/-- The Giry sigma algebra agrees with the Borel sigma algebra of weak convergence. -/
instance probabilityBorel : BorelSpace (ProbabilityMeasure X) := by
  constructor
  apply le_antisymm _ OpensMeasurableSpace.borel_le
  change MeasurableSpace.comap (fun μ : ProbabilityMeasure X ↦ (μ : Measure X)) _ ≤ _
  apply measurable_iff_comap_le.1
  letI : MeasurableSpace (ProbabilityMeasure X) := borel (ProbabilityMeasure X)
  letI : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (BorelSpace.measurable_eq (α := X)) isPiSystem_isOpen
  intro U hU
  have hlow : LowerSemicontinuous (fun μ : ProbabilityMeasure X ↦ (μ : Measure X) U) := by
    apply lowerSemicontinuous_iff_le_liminf.2
    intro μ
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (μ := μ) (μs := id) Filter.tendsto_id hU
  exact hlow.measurable

end PaperN.PartI
