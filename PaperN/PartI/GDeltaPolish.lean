import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.GDelta.Basic

namespace PaperN.PartI
open Set Topology TopologicalSpace

/-- A Gδ subspace of a Polish space is Polish, via the closed diagonal in a countable
product of open Polish subspaces. The subspace topology is retained throughout. -/
theorem polishSpace_of_isGDelta {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {s : Set X} (hs : IsGδ s) : PolishSpace s := by
  obtain ⟨U, hU, rfl⟩ := hs.eq_iInter_nat
  letI (n : ℕ) : PolishSpace (U n) := (hU n).polishSpace
  let f : (⋂ n, U n) → (∀ n, U n) := fun x n ↦ ⟨x.val, mem_iInter.mp x.property n⟩
  have hf : Continuous f := continuous_pi fun n ↦ continuous_subtype_val.subtype_mk _
  let g : (∀ n, U n) → X := fun y ↦ (y 0).val
  have hg : Continuous g := continuous_subtype_val.comp (continuous_apply 0)
  have he : IsEmbedding f := .of_comp hf hg (show IsEmbedding (g ∘ f) from IsEmbedding.subtypeVal)
  have hr : range f = {y | ∀ n, (y n).val = (y 0).val} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact fun _ ↦ rfl
    · intro hy
      have hx : (y 0).val ∈ ⋂ n, U n := mem_iInter.mpr fun n ↦ by
        rw [← hy n]
        exact (y n).property
      refine ⟨⟨(y 0).val, hx⟩, ?_⟩
      funext n
      exact Subtype.ext (hy n).symm
  have hc : IsClosed (range f) := by
    rw [hr]
    simp only [setOf_forall]
    exact isClosed_iInter fun n ↦ isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n)) hg
  exact (show IsClosedEmbedding f from ⟨he, hc⟩).polishSpace
end PaperN.PartI
