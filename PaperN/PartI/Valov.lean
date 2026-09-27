import PaperN.PartI.ValovStatements
import Mathlib.MeasureTheory.Measure.RegularityCompacts

namespace PaperN.PartI
open MeasureTheory TopologicalSpace Set Filter
universe u v
variable {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Every probability in the chosen Polish specialization satisfies the source Radon condition. -/
theorem probability_innerRegular_polish [PolishSpace X] (μ : ProbabilityMeasure X) :
    (μ : Measure X).InnerRegularWRT (fun K ↦ IsCompact K ∧ IsClosed K) MeasurableSet :=
  innerRegular_isCompact_isClosed_measurableSet_of_finite (μ : Measure X)

/-- Compose the cited right inverse with the continuous Dirac map. -/
theorem valovSelection_spec [PolishSpace X] [PolishSpace Y]
    (f : C(X, Y)) (h : ValovProbabilityInput f)
    (ho : IsOpenMap f) (hs : Function.Surjective f) : ValovSelectionStatement f := by
  obtain ⟨R, hR⟩ := h.rightInverse ho hs
  exact ⟨R.comp ⟨diracProba, continuous_diracProba⟩, fun y ↦ hR (diracProba y)⟩

/-- A probability pushing to a point gives full mass to that fiber. -/
theorem measure_fiber_of_pushforward_eq_dirac [T1Space Y]
    (f : C(X, Y)) (μ : ProbabilityMeasure X) (y : Y)
    (h : probabilityPushforward f μ = diracProba y) :
    (μ : Measure X) (f ⁻¹' {y}) = 1 := by
  have hm := congrArg (fun ν : ProbabilityMeasure Y ↦ (ν : Measure Y) {y}) h
  change ((μ : Measure X).map f) {y} = (Measure.dirac y) {y} at hm
  rw [Measure.map_apply f.continuous.measurable (measurableSet_singleton y)] at hm
  simpa using hm

/-- Continuity makes the fiber closed; no compactness of the fiber is required. -/
theorem support_subset_fiber_of_pushforward_eq_dirac [T1Space Y]
    (f : C(X, Y)) (μ : ProbabilityMeasure X) (y : Y)
    (h : probabilityPushforward f μ = diracProba y) :
    (μ : Measure X).support ⊆ f ⁻¹' {y} := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.preimage f.continuous)
  have hm : (μ : Measure X).map f = Measure.dirac y :=
    congrArg ProbabilityMeasure.toMeasure h
  have ha : ∀ᵐ z ∂(μ : Measure X).map f, z = y := by
    rw [hm]
    simp
  exact (ae_map_iff f.continuous.measurable.aemeasurable
    (measurableSet_singleton y)).mp ha

/-- The fiber laws obtained from the explicit Valov input. -/
theorem fiberLawSelection_spec [PolishSpace X] [PolishSpace Y]
    (f : C(X, Y)) (h : ValovProbabilityInput f)
    (ho : IsOpenMap f) (hs : Function.Surjective f) : FiberLawSelectionStatement f := by
  obtain ⟨s, hμ⟩ := valovSelection_spec f h ho hs
  exact ⟨s, fun y ↦ ⟨hμ y, measure_fiber_of_pushforward_eq_dirac f (s y) y (hμ y),
    support_subset_fiber_of_pushforward_eq_dirac f (s y) y (hμ y)⟩⟩

end PaperN.PartI
