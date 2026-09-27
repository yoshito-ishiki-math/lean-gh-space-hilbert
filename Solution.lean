import PaperN.PartIV.MainTheorem
open MeasureTheory TopologicalSpace Set
open scoped Topology
namespace PalomarPaperN
open PaperN.PartI PaperN.PartII PaperN.PartIV GromovHausdorff
/-- Valov's continuous right-inverse consequence for open continuous surjections
between Polish Borel spaces. No compact-support hypothesis is imposed. -/
def ValovInput : Prop :=
  ∀ (X : Type 1) (Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [PolishSpace X] [PolishSpace Y] (f : C(X,Y)),
    IsOpenMap f → Function.Surjective f →
    ∃ R : C(ProbabilityMeasure Y, ProbabilityMeasure X),
      ∀ μ, (R μ).map f.continuous.measurable.aemeasurable = μ

/-- Conditional classification, assuming the five displayed literature results. -/
theorem main
    (hv : ValovInput) (hH : EquivariantHyperspaceARInput)
    (hO : OrbitARInput) (hD : HannerDominationInput)
    (hT : TorunczykRecognitionInput) :
    Nonempty (GHSpace ≃ₜ RealHilbertSpace) := by
  apply ghSpace_homeomorphic_hilbert_main ?_ hH hO hD hT
  letI := ghpMetricInput_proved.metricSpace
  letI := ghpMetricInput_proved.invariantMetricSpace
  letI : MeasurableSpace InvariantMeasuredGHSpace.{0} := borel _
  letI : MeasurableSpace GHSpace := borel _
  letI : BorelSpace InvariantMeasuredGHSpace.{0} := ⟨rfl⟩
  letI : BorelSpace GHSpace := ⟨rfl⟩
  letI : PolishSpace InvariantMeasuredGHSpace.{0} :=
    invariantMeasuredPolish_spec ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved
  change ValovProbabilityInput (invariantProjectionMap ghpMetricInput_proved)
  refine ValovProbabilityInput.mk ?_
  intro hopen hsurj
  obtain ⟨R, hR⟩ := hv _ _ _ hopen hsurj
  exact ⟨R, hR⟩
end PalomarPaperN
