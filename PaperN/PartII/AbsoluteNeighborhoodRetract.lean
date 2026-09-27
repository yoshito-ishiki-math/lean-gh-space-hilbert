import PaperN.PartII.AbsoluteRetract

namespace PaperN.PartII
open TopologicalSpace
universe u v

/-- ANR for metrizable ambient spaces of the specified universe. -/
def IsAbsoluteNeighborhoodRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ U : Set Y, IsOpen U ∧ Set.range e ⊆ U ∧
        ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x

/-- The separable-ambient version used in Hanner's domination theorem. -/
def IsSeparableAbsoluteNeighborhoodRetract (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    [SeparableSpace Y] (e : X → Y), Topology.IsClosedEmbedding e →
      ∃ U : Set Y, IsOpen U ∧ Set.range e ⊆ U ∧
        ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x

/-- A global retraction restricts to a neighbourhood retraction by taking the whole ambient space. -/
theorem IsAbsoluteRetract.isAbsoluteNeighborhoodRetract
    {X : Type u} [TopologicalSpace X] (h : IsAbsoluteRetract.{u,v} X) :
    IsAbsoluteNeighborhoodRetract.{u,v} X := by
  refine ⟨h.1, ?_⟩
  intro Y _ _ e he
  obtain ⟨r, hr, hre⟩ := h.2 Y e he
  exact ⟨Set.univ, isOpen_univ, Set.subset_univ _, r ∘ Subtype.val,
    hr.comp continuous_subtype_val, fun x _ ↦ hre x⟩

/-- Restricting ambient spaces to the separable category preserves the ANR property. -/
theorem IsAbsoluteNeighborhoodRetract.separable
    {X : Type u} [TopologicalSpace X] (h : IsAbsoluteNeighborhoodRetract.{u,v} X) :
    IsSeparableAbsoluteNeighborhoodRetract.{u,v} X := by
  refine ⟨h.1, ?_⟩
  intro Y _ _ _ e he
  exact h.2 Y e he

end PaperN.PartII
