import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.MetricSpace.Gluing

namespace PaperN.Shared
open Set Metric GromovHausdorff
universe u v

/-- A relation whose two coordinate projections are onto; no closedness is required. -/
structure Correspondence (X : Type u) (Y : Type v) where
  rel : Set (X × Y)
  left_total : ∀ x, ∃ y, (x, y) ∈ rel
  right_total : ∀ y, ∃ x, (x, y) ∈ rel

instance {X : Type u} {Y : Type v} [Nonempty X] (R : Correspondence X Y) : Nonempty R.rel := by
  obtain ⟨y, hy⟩ := R.left_total (Classical.choice inferInstance)
  exact ⟨⟨(_, y), hy⟩⟩

/-- An upper bound for the distortion, equivalently the corresponding supremum bound. -/
def Correspondence.DistortionLE {X : Type u} {Y : Type v} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] (R : Correspondence X Y) (a : ℝ) : Prop :=
  ∀ p q : R.rel, |dist p.val.1 q.val.1 - dist p.val.2 q.val.2| ≤ a

/-- The prescribed correspondence is realized on the actual disjoint union. -/
def CorrespondenceEmbeddingStatement : Prop :=
  ∀ (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y] [CompactSpace X] [CompactSpace Y]
    (R : Correspondence X Y) (ε : ℝ), 0 < ε → R.DistortionLE (2 * ε) →
    ∃ m : MetricSpace (X ⊕ Y),
      letI := m
      Isometry (Sum.inl : X → X ⊕ Y) ∧ Isometry (Sum.inr : Y → X ⊕ Y) ∧
      (∀ p : R.rel, dist (Sum.inl p.val.1) (Sum.inr p.val.2) ≤ ε) ∧
      hausdorffDist (range (Sum.inl : X → X ⊕ Y)) (range (Sum.inr : Y → X ⊕ Y)) ≤ ε

noncomputable def Correspondence.distortion {X : Type u} {Y : Type v}
    [PseudoMetricSpace X] [PseudoMetricSpace Y] (R : Correspondence X Y) : ℝ :=
  ⨆ z : R.rel × R.rel, |dist z.1.val.1 z.2.val.1 - dist z.1.val.2 z.2.val.2|

/-- The manuscript's supremum convention for the distortion. -/
def CorrespondenceEmbeddingSupStatement : Prop :=
  ∀ (X : Type u) (Y : Type v) [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [Nonempty Y] [CompactSpace X] [CompactSpace Y]
    (R : Correspondence X Y) (ε : ℝ), 0 < ε → R.distortion ≤ 2 * ε →
    ∃ m : MetricSpace (X ⊕ Y),
      letI := m
      Isometry (Sum.inl : X → X ⊕ Y) ∧ Isometry (Sum.inr : Y → X ⊕ Y) ∧
      (∀ p : R.rel, dist (Sum.inl p.val.1) (Sum.inr p.val.2) ≤ ε) ∧
      hausdorffDist (range (Sum.inl : X → X ⊕ Y)) (range (Sum.inr : Y → X ⊕ Y)) ≤ ε
end PaperN.Shared
