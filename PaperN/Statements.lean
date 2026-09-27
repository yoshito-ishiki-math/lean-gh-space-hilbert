import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Metrizable.Basic

/-! Preparation only: propositions are specifications, not proved results.
No manuscript theorem is assumed or proved by this module. -/
namespace PaperN

abbrev GH := GromovHausdorff.GHSpace
abbrev RealHilbert := lp (fun _ : ℕ ↦ ℝ) 2

/-- Target of thm:main and thm:part-iv-main. -/
def HilbertHomeomorphismGoal : Prop := Nonempty (GH ≃ₜ RealHilbert)

/-- Pointwise closeness with respect to a family of open sets.
Openness and covering are separate hypotheses of the approximation statement. -/
def CoverClose {A Y : Type*} (cover : Set (Set Y)) (f g : A → Y) : Prop :=
  ∀ a, ∃ U ∈ cover, f a ∈ U ∧ g a ∈ U

/-- Every ambient point has a neighborhood meeting at most one indexed member.
This includes points outside the union and permits empty members. -/
def DiscreteImages {Y : Type*} [TopologicalSpace Y] (s : ℕ → Set Y) : Prop :=
  ∀ y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
    ∀ i j, (U ∩ s i).Nonempty → (U ∩ s j).Nonempty → i = j

/-- Draft specification of thm:discrete-approximation.
Universe generalization and agreement with the manuscript remain review tasks. -/
def DiscreteApproximationGoal : Prop :=
  ∀ (A : ℕ → Type) [∀ n, TopologicalSpace (A n)]
    [∀ n, CompactSpace (A n)] [∀ n, TopologicalSpace.MetrizableSpace (A n)]
    (f : ∀ n, A n → GH), (∀ n, Continuous (f n)) →
    ∀ cover : Set (Set GH), (∀ U ∈ cover, IsOpen U) →
      (∀ x, ∃ U ∈ cover, x ∈ U) →
      ∃ g : ∀ n, A n → GH, (∀ n, Continuous (g n)) ∧
        (∀ n, CoverClose cover (f n) (g n)) ∧
        DiscreteImages (fun n ↦ Set.range (g n))

end PaperN
