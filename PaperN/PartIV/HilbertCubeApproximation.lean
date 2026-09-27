import PaperN.PartIV.DiscreteApproximation

namespace PaperN.PartIV
open PaperN.PartI GromovHausdorff Set

/-- The Hilbert cube carries the product topology of countably many unit intervals. -/
abbrev HilbertCube := ℕ → Set.Icc (0 : ℝ) 1

/-- The open-cover discrete approximation condition used in Hilbert-space recognition. -/
def HasHilbertCubeDiscreteApproximation (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (f : ℕ × HilbertCube → X), Continuous f →
    ∀ U : Set (Set X), (∀ V ∈ U, IsOpen V) → (∀ x, ∃ V ∈ U, x ∈ V) →
      ∃ g : ℕ × HilbertCube → X, Continuous g ∧
        (∀ x, ∃ V ∈ U, f x ∈ V ∧ g x ∈ V) ∧
        IsDiscreteFamily (fun j ↦ g '' ({j} ×ˢ (univ : Set HilbertCube)))

/-- Slices of a map on a product with a discrete index are its component ranges. -/
theorem image_index_slice {J Q X : Type*} (g : J × Q → X) (j : J) :
    g '' ({j} ×ˢ (univ : Set Q)) = range (fun q ↦ g (j, q)) := by
  ext x
  constructor
  · rintro ⟨⟨k, q⟩, hk, rfl⟩
    have hkj : k = j := hk.1
    subst k
    exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨(j, q), ⟨rfl, mem_univ q⟩, rfl⟩

/-- The constructed compact-domain approximations satisfy the exact Hilbert-cube condition. -/
theorem ghSpace_hilbertCubeDiscreteApproximation (hg : GHCommonEmbeddingInput.{0}) :
    HasHilbertCubeDiscreteApproximation GHSpace := by
  intro f hf U ho hc
  have hU : Nonempty U := by
    obtain ⟨V, hV, _⟩ := hc (Classical.choice (inferInstance : Nonempty GHSpace))
    exact ⟨⟨V, hV⟩⟩
  letI := hU
  have hcont (j : ℕ) : Continuous (fun q : HilbertCube ↦ f (j, q)) :=
    hf.comp (Continuous.prodMk_right j)
  obtain ⟨g, hgcont, hgclose, hgdisc⟩ := exists_discrete_approximations
    (fun j q ↦ f (j, q)) hcont (fun V : U ↦ V.val)
    (fun V ↦ ho V.val V.property)
    (fun x ↦ by obtain ⟨V, hV, hx⟩ := hc x; exact ⟨⟨V, hV⟩, hx⟩) hg
  refine ⟨fun x ↦ g x.1 x.2, continuous_prod_of_discrete_left.mpr hgcont, ?_, ?_⟩
  · intro x
    obtain ⟨V, hfV, hgV⟩ := hgclose x.1 x.2
    exact ⟨V.val, V.property, hfV, hgV⟩
  · simpa only [image_index_slice] using hgdisc

end PaperN.PartIV
