import PaperN.PartII.AbsoluteNeighborhoodRetract

namespace PaperN.PartII
open TopologicalSpace
universe u v

/-- Absolute extension for closed subsets of metrizable ambient spaces. -/
def IsAbsoluteExtensor (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (A : Set Y), IsClosed A → ∀ f : A → X, Continuous f →
      ∃ F : Y → X, Continuous F ∧ ∀ a : A, F a = f a

/-- Neighbourhood extension, with an actual open domain containing the closed set. -/
def IsAbsoluteNeighborhoodExtensor (X : Type u) [TopologicalSpace X] : Prop :=
  MetrizableSpace X ∧ ∀ (Y : Type v) [TopologicalSpace Y] [MetrizableSpace Y]
    (A : Set Y), IsClosed A → ∀ f : A → X, Continuous f →
      ∃ U : Set Y, IsOpen U ∧ A ⊆ U ∧ ∃ F : U → X, Continuous F ∧
        ∀ (a : A) (ha : (a : Y) ∈ U), F ⟨a, ha⟩ = f a

/-- Absolute extension gives a retraction by extending the inverse of a closed embedding. -/
theorem IsAbsoluteExtensor.isAbsoluteRetract
    {X : Type u} [TopologicalSpace X] (h : IsAbsoluteExtensor.{u,v} X) :
    IsAbsoluteRetract.{u,v} X := by
  refine ⟨h.1, ?_⟩
  intro Y _ _ e he
  obtain ⟨F, hF, hFe⟩ := h.2 Y (Set.range e) he.isClosed_range
    he.isEmbedding.toHomeomorph.symm he.isEmbedding.toHomeomorph.symm.continuous
  refine ⟨F, hF, ?_⟩
  intro x
  exact (hFe ⟨e x, ⟨x, rfl⟩⟩).trans (he.isEmbedding.toHomeomorph_symm_apply x)

/-- The same inverse-extension argument works on an open neighbourhood. -/
theorem IsAbsoluteNeighborhoodExtensor.isAbsoluteNeighborhoodRetract
    {X : Type u} [TopologicalSpace X] (h : IsAbsoluteNeighborhoodExtensor.{u,v} X) :
    IsAbsoluteNeighborhoodRetract.{u,v} X := by
  refine ⟨h.1, ?_⟩
  intro Y _ _ e he
  obtain ⟨U, hU, hsub, F, hF, hFe⟩ := h.2 Y (Set.range e) he.isClosed_range
    he.isEmbedding.toHomeomorph.symm he.isEmbedding.toHomeomorph.symm.continuous
  refine ⟨U, hU, hsub, F, hF, ?_⟩
  intro x hx
  exact (hFe ⟨e x, ⟨x, rfl⟩⟩ hx).trans (he.isEmbedding.toHomeomorph_symm_apply x)

end PaperN.PartII
