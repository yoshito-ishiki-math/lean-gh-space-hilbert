import PaperN.PartI.Solution
import PaperN.PartI.FixedTopologyAssignment

namespace PaperN.PartI
open MeasureTheory Set Filter Metric
open scoped Topology
universe u

section Barycenter
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The current complete barycenter proposition, with the mass-one invariance clause. -/
def CurrentBarycenterStatement : Prop :=
  (∀ η, BarycenterIdentity (X := X) η (barycenter η)) ∧
  (∀ b : ProbabilityMeasure (ProbabilityMeasure X) → ProbabilityMeasure X,
    (∀ η, BarycenterIdentity η (b η)) → b = barycenter) ∧
  Continuous (barycenter : ProbabilityMeasure (ProbabilityMeasure X) → ProbabilityMeasure X) ∧
  (∀ (η : ProbabilityMeasure (ProbabilityMeasure X)) (S : Set (ProbabilityMeasure X)),
    MeasurableSet S → (η : Measure (ProbabilityMeasure X)) S = 1 →
    (∀ μ ∈ S, (μ : Measure X).support = Set.univ) →
    (barycenter η : Measure X).support = Set.univ) ∧
  (∀ (η : ProbabilityMeasure (ProbabilityMeasure X)) (g : X ≃ᵢ X),
    ((η : Measure (ProbabilityMeasure X))
      {μ | Measure.map g (μ : Measure X) = (μ : Measure X)} = 1) →
    Measure.map g (barycenter η : Measure X) = (barycenter η : Measure X))

theorem currentBarycenter_spec : CurrentBarycenterStatement (X := X) := by
  obtain ⟨hi, hu, hc, hf, _⟩ := continuousBarycenter_spec (X := X)
  exact ⟨hi, hu, hc, hf, fun η g hη ↦ barycenter_invariant_of_mass_one η g.continuous hη⟩
end Barycenter

local instance currentMeasurable (X : Type*) [TopologicalSpace X] : MeasurableSpace X := borel X
local instance currentBorel (X : Type*) [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩

/-- Simultaneous measures on concrete compact metric carriers, M1--M3 in the live manuscript.
The separate naturality and convergence APIs also allow different carrier universes. -/
def CurrentInvariantAssignmentStatement : Prop :=
  ∃ μ : ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X], ProbabilityMeasure X,
    (∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X],
      (μ X : Measure X).support = univ) ∧
    (∀ (X Y : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
      [MetricSpace Y] [CompactSpace Y] [Nonempty Y] (e : X ≃ᵢ Y),
      (μ X).map e = μ Y) ∧
    (∀ (Xs : ℕ → Type u) (X Z : Type u)
      [∀ n, MetricSpace (Xs n)] [∀ n, CompactSpace (Xs n)] [∀ n, Nonempty (Xs n)]
      [MetricSpace X] [CompactSpace X] [Nonempty X] [MetricSpace Z] [CompactSpace Z]
      (es : ∀ n, Xs n → Z) (e : X → Z) (hes : ∀ n, Isometry (es n)) (he : Isometry e),
      Tendsto (fun n ↦ hausdorffDist (range (es n)) (range e)) atTop (𝓝 0) →
      Tendsto (fun n ↦ (μ (Xs n)).map (es n))
        atTop (𝓝 ((μ X).map e)))

/-- The revised selection theorem, using exactly the existing six citation inputs. -/
theorem currentInvariantAssignment_spec (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc) :
    CurrentInvariantAssignmentStatement.{u} := by
  let hs := invariantFiberLawSelection_spec hm hp hc hg ha hv
  exact ⟨universalProbability hm hs, universalProbability_fullSupport hm hs,
    universalProbability_natural hm hs, universalProbability_tendsto hm hp hs⟩

end PaperN.PartI
