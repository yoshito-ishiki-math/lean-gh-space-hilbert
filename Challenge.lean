import Mathlib
/-! # Conditional Hilbert-space classification of Gromov--Hausdorff space
The five assumptions below are literature inputs, not proved inhabitants.
The statement uses only Mathlib imports; the substantive proof is in Solution.
Valov is stated for Polish Borel spaces in the required universes, rather than for the single
invariant measured GH projection used by the proof. -/
open MeasureTheory TopologicalSpace Set
open scoped Topology
namespace PaperN.PartII
universe u v w g
/- IsAbsoluteRetract: exact definition from the substantive development; see README. -/
/-- Metrizable target with a continuous retraction from every closed embedding. -/
def IsAbsoluteRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e

/- IsEquivariantAbsoluteRetract: exact definition from the substantive development; see README. -/
/-- Continuous group action with equivariant retractions from every closed equivariant embedding. -/
def IsEquivariantAbsoluteRetract (G : Type g) [Group G] [TopologicalSpace G]
    (X : Type u) [TopologicalSpace X] [MulAction G X] : Prop :=
  MetrizableSpace X ∧ ContinuousSMul G X ∧
    ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y] [MulAction G Y]
      [ContinuousSMul G Y] (e : X → Y), Topology.IsClosedEmbedding e →
      (∀ (a : G) x, e (a • x) = a • e x) →
      ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e ∧
        ∀ (a : G) y, r (a • y) = a • r y

/- IsAbsoluteNeighborhoodRetract: exact definition from the substantive development; see README. -/
/-- Metrizable target retracting from an open neighborhood of each closed embedded image. -/
def IsAbsoluteNeighborhoodRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ U : Set Y, IsOpen U ∧ Set.range e ⊆ U ∧
        ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x

/- IsSeparableAbsoluteNeighborhoodRetract: exact definition from the substantive development; see README. -/
/-- Neighborhood retract property restricted to separable metrizable ambient spaces. -/
def IsSeparableAbsoluteNeighborhoodRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    [SeparableSpace Y] (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ U : Set Y, IsOpen U ∧ Set.range e ⊆ U ∧
        ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x

/- HasContinuumConnectedBasis: exact definition from the substantive development; see README. -/
/-- Each neighborhood contains an open neighborhood whose points are joined by compact connected subsets. -/
def HasContinuumConnectedBasis (X : Type) [TopologicalSpace X] : Prop :=
  ∀ a : X, ∀ U ∈ nhds a, ∃ V : Set X, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
    ∀ x ∈ V, ∀ y ∈ V, ∃ K : Set X,
      IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ K ⊆ V

/- EquivariantHyperspaceARInput: exact definition from the substantive development; see README. -/
/-- Antonyan hyperspace theorem for compact groups, connected targets and a continuum-connected basis. -/
def EquivariantHyperspaceARInput : Prop :=
  ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [MetricSpace X] [Nonempty X]
    [MulAction G X] [ContinuousSMul G X]
    [MulAction G (NonemptyCompacts X)],
    (∀ (a : G) (K : NonemptyCompacts X),
      ((a • K : NonemptyCompacts X) : Set X) = (fun x ↦ a • x) '' (K : Set X)) →
    IsConnected (Set.univ : Set X) → HasContinuumConnectedBasis X →
    IsEquivariantAbsoluteRetract.{0,0,0} G (NonemptyCompacts X)

/- OrbitARInput: exact definition from the substantive development; see README. -/
/-- Antonyan orbit theorem for a second-countable compact group and an equivariant AR. -/
def OrbitARInput : Prop :=
  ∀ (G X Q : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [CompactSpace G] [SecondCountableTopology G]
    [TopologicalSpace X] [MulAction G X] [TopologicalSpace Q],
    IsEquivariantAbsoluteRetract.{0,0,0} G X →
    ∀ q : X → Q, Topology.IsQuotientMap q →
      (∀ x y, q x = q y ↔ ∃ a : G, x = a • y) →
      IsAbsoluteRetract.{0,0} Q

/- HasSmallANRDomination: exact definition from the substantive development; see README. -/
/-- Domination by a separable metric ANR with arbitrarily small homotopy-track diameter. -/
def HasSmallANRDomination (X : Type) [MetricSpace X] : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (Y : Type) (m : MetricSpace Y),
    letI := m
    SeparableSpace Y ∧ IsAbsoluteNeighborhoodRetract.{0,0} Y ∧
    ∃ f : X → Y, ∃ g : Y → X, Continuous f ∧ Continuous g ∧
      ∃ H : X → Set.Icc (0 : ℝ) 1 → X,
        Continuous (fun p : X × Set.Icc (0 : ℝ) 1 ↦ H p.1 p.2) ∧
        (∀ x, H x ⟨0, by constructor <;> norm_num⟩ = x) ∧
        (∀ x, H x ⟨1, by constructor <;> norm_num⟩ = g (f x)) ∧
        (∀ x, Metric.diam (Set.range (H x)) < ε)

/- HannerDominationInput: exact definition from the substantive development; see README. -/
/-- Hanner theorem converting small ANR domination into separable-category ANR status. -/
def HannerDominationInput : Prop :=
  ∀ (X : Type) [MetricSpace X] [SeparableSpace X], HasSmallANRDomination X →
    IsSeparableAbsoluteNeighborhoodRetract.{0,0} X

end PaperN.PartII
namespace PaperN.PartIV
open PaperN.PartII
/-- Every ambient point has a neighborhood meeting at most one indexed member. -/
def IsDiscreteFamily {J X : Type*} [TopologicalSpace X] (F : J → Set X) : Prop :=
  ∀ x, ∃ V ∈ 𝓝 x, ∀ i j, (F i ∩ V).Nonempty → (F j ∩ V).Nonempty → i = j

/-- Countable product of closed real unit intervals with its product topology. -/
abbrev HilbertCube := ℕ → Set.Icc (0 : ℝ) 1

/-- Every map from countably many Hilbert cubes admits open-cover-close discrete slice images. -/
def HasHilbertCubeDiscreteApproximation (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (f : ℕ × HilbertCube → X), Continuous f →
    ∀ U : Set (Set X), (∀ V ∈ U, IsOpen V) → (∀ x, ∃ V ∈ U, x ∈ V) →
      ∃ g : ℕ × HilbertCube → X, Continuous g ∧
        (∀ x, ∃ V ∈ U, f x ∈ V ∧ g x ∈ V) ∧
        IsDiscreteFamily (fun j ↦ g '' ({j} ×ˢ (univ : Set HilbertCube)))

/-- Real square-summable sequences with their norm topology. -/
abbrev RealHilbertSpace := lp (fun _ : ℕ ↦ ℝ) 2

/-- Hilbert-space recognition for nonempty complete separable metric absolute retracts. -/
def TorunczykRecognitionInput : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X], IsAbsoluteRetract.{0,0} X →
      (Nonempty (X ≃ₜ RealHilbertSpace) ↔ HasHilbertCubeDiscreteApproximation X)

end PaperN.PartIV
namespace PalomarPaperN
open PaperN.PartII PaperN.PartIV GromovHausdorff
/-- Valov's continuous right-inverse consequence for open continuous surjections
between Polish Borel spaces. No compact-support hypothesis is imposed. -/
def ValovInput : Prop :=
  ∀ (X : Type 1) (Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    [PolishSpace X] [PolishSpace Y] (f : C(X,Y)),
    IsOpenMap f → Function.Surjective f →
    ∃ R : C(ProbabilityMeasure Y, ProbabilityMeasure X),
      ∀ μ, (R μ).map f = μ

/-- Conditional classification, assuming the five displayed literature results. -/
theorem main
    (hv : ValovInput) (hH : EquivariantHyperspaceARInput)
    (hO : OrbitARInput) (hD : HannerDominationInput)
    (hT : TorunczykRecognitionInput) :
    Nonempty (GHSpace ≃ₜ RealHilbertSpace) := by
  sorry
end PalomarPaperN
