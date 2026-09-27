import PaperN.PartIV.LocallyFiniteProducts

namespace PaperN.PartIV
open PaperN.PartI GromovHausdorff Set
open scoped Topology

/-- Discreteness is required at every ambient point, including outside the union. -/
def IsDiscreteFamily {J X : Type*} [TopologicalSpace X] (F : J → Set X) : Prop :=
  ∀ x, ∃ V ∈ 𝓝 x, ∀ i j, (F i ∩ V).Nonempty → (F j ∩ V).Nonempty → i = j

/-- Locally finite, pairwise disjoint closed sets form an ambient discrete family. -/
theorem isDiscreteFamily_of_locallyFinite {J X : Type*} [TopologicalSpace X]
    (F : J → Set X) (hF : LocallyFinite F) (hclosed : ∀ i, IsClosed (F i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (F i) (F j)) : IsDiscreteFamily F := by
  intro x
  let V := ⋂ (i) (_ : x ∉ F i), (F i)ᶜ
  refine ⟨V, hF.iInter_compl_mem_nhds hclosed x, ?_⟩
  intro i j hi hj
  have hx (k : J) (hk : (F k ∩ V).Nonempty) : x ∈ F k := by
    by_contra hn
    obtain ⟨y, hy, hv⟩ := hk
    exact (mem_iInter₂.mp hv k hn) hy
  by_contra hij
  exact Set.disjoint_left.mp (hdisjoint i j hij) (hx i hi) (hx j hj)

/-- Continuous cover-close discrete approximation for arbitrary compact domains. -/
theorem exists_discrete_approximations
    {D : ℕ → Type*} [∀ j, TopologicalSpace (D j)] [∀ j, CompactSpace (D j)]
    (f : ∀ j, D j → GHSpace) (hf : ∀ j, Continuous (f j))
    {I : Type*} [Nonempty I] (U : I → Set GHSpace)
    (ho : ∀ i, IsOpen (U i)) (hc : ∀ q, ∃ i, q ∈ U i)
    (hg : GHCommonEmbeddingInput.{0}) :
    ∃ g : ∀ j, D j → GHSpace, (∀ j, Continuous (g j)) ∧
      (∀ j x, ∃ i, f j x ∈ U i ∧ g j x ∈ U i) ∧
      IsDiscreteFamily (fun j ↦ range (g j)) := by
  obtain ⟨a, ha, hcont, hclose, hsep⟩ :=
    exists_disjoint_product_approximations f hf U ho hc hg
  refine ⟨fun j ↦ cardApprox (a j) U ho hc ∘ f j, hcont, hclose, ?_⟩
  exact isDiscreteFamily_of_locallyFinite _ (cardApprox_locallyFinite U ho hc f a ha)
    (fun j ↦ (isCompact_range (hcont j)).isClosed) hsep

end PaperN.PartIV
