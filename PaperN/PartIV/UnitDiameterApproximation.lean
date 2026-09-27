import PaperN.PartIV.Diameter
import PaperN.PartIV.HilbertCubeApproximation

namespace PaperN.PartIV
open PaperN.PartI GromovHausdorff Set
open scoped Topology

/-- The actual diameter-one subspace of GH space. -/
def UnitDiameterSpace := {q : GHSpace // ghDiameter q = 1}

noncomputable instance : MetricSpace UnitDiameterSpace := inferInstanceAs (MetricSpace {q : GHSpace // ghDiameter q = 1})

/-- The diameter-one locus is closed. -/
theorem unitDiameter_isClosed : IsClosed {q : GHSpace | ghDiameter q = 1} :=
  isClosed_eq ghDiameter_lipschitz.continuous continuous_const

instance : CompleteSpace UnitDiameterSpace := by
  exact @IsClosed.completeSpace_coe GHSpace _ _ {q | ghDiameter q = 1} unitDiameter_isClosed

/-- A closed subspace cover extends to an ambient cover refining it on the subspace. -/
theorem closed_subspace_cover {X : Type*} [TopologicalSpace X] (S : Set X)
    (hS : IsClosed S) (U : Set (Set S)) (hU : U.Nonempty)
    (ho : ∀ V ∈ U, IsOpen V) (hc : ∀ x, ∃ V ∈ U, x ∈ V) :
    ∃ W : Set (Set X), (∀ O ∈ W, IsOpen O) ∧ (∀ x, ∃ O ∈ W, x ∈ O) ∧
      ∀ O ∈ W, ∃ V ∈ U, Subtype.val ⁻¹' O ⊆ V := by
  let W : Set (Set X) := {O | IsOpen O ∧ ∃ V ∈ U, Subtype.val ⁻¹' O ⊆ V}
  refine ⟨W, fun O hO ↦ hO.1, ?_, fun O hO ↦ hO.2⟩
  intro x
  by_cases hx : x ∈ S
  · obtain ⟨V, hV, hxV⟩ := hc ⟨x,hx⟩
    obtain ⟨O, hO, heq⟩ := isOpen_induced_iff.mp (ho V hV)
    refine ⟨O, ⟨hO, V, hV, heq.subset⟩, ?_⟩
    exact (heq.symm ▸ hxV : (⟨x,hx⟩ : S) ∈ Subtype.val ⁻¹' O)
  · obtain ⟨V, hV⟩ := hU
    refine ⟨Sᶜ, ⟨hS.isOpen_compl, V, hV, ?_⟩, hx⟩
    intro y hy
    exact False.elim (hy y.property)

/-- Ambient discreteness of ranges implies discreteness after restricting the codomain. -/
theorem isDiscreteFamily_subtype_ranges {X J : Type*} [TopologicalSpace X]
    {S : Set X} {D : J → Type*} (g : ∀ j, D j → S)
    (hg : IsDiscreteFamily (fun j ↦ range (fun x ↦ (g j x).val))) :
    IsDiscreteFamily (fun j ↦ range (g j)) := by
  intro x
  obtain ⟨V, hV, hdisc⟩ := hg x.val
  refine ⟨Subtype.val ⁻¹' V, continuousAt_subtype_val.preimage_mem_nhds hV, ?_⟩
  intro i j hi hj
  apply hdisc i j
  · obtain ⟨y, ⟨d, rfl⟩, hy⟩ := hi
    exact ⟨(g i d).val, ⟨d, rfl⟩, hy⟩
  · obtain ⟨y, ⟨d, rfl⟩, hy⟩ := hj
    exact ⟨(g j d).val, ⟨d, rfl⟩, hy⟩

/-- The diameter-one subspace satisfies the exact Hilbert-cube recognition approximation condition. -/
theorem unitDiameter_hilbertCubeDiscreteApproximation (hg : GHCommonEmbeddingInput.{0}) :
    HasHilbertCubeDiscreteApproximation UnitDiameterSpace := by
  intro f hf U ho hc
  have hUne : U.Nonempty := by
    obtain ⟨V,hV,_⟩ := hc (f (0, fun _ ↦ ⟨0, by constructor <;> norm_num⟩))
    exact ⟨V,hV⟩
  obtain ⟨W,hWo,hWc,hWU⟩ := closed_subspace_cover {q | ghDiameter q = 1}
    unitDiameter_isClosed U hUne ho hc
  letI : Nonempty W := by
    obtain ⟨O,hO,_⟩ := hWc (Classical.choice (inferInstance : Nonempty GHSpace))
    exact ⟨⟨O,hO⟩⟩
  let A : W → Set GHSpace := fun O ↦ O.val
  have hao : ∀ O, IsOpen (A O) := fun O ↦ hWo O.val O.property
  have hac : ∀ q, ∃ O, q ∈ A O := by
    intro q
    obtain ⟨O,hO,hq⟩ := hWc q
    exact ⟨⟨O,hO⟩,hq⟩
  let F (j : ℕ) (x : HilbertCube) : GHSpace := (f (j,x)).val
  have hF (j : ℕ) : Continuous (F j) :=
    (hf.comp (Continuous.prodMk_right j)).subtype_val
  obtain ⟨a,ha,hcont,hclose,hsep⟩ := exists_disjoint_product_approximations F hF A hao hac hg
  let g (j : ℕ) (x : HilbertCube) : UnitDiameterSpace :=
    ⟨cardApprox (a j) A hao hac (F j x),
      cardApprox_diameter_one A hao hac (a j) (F j x) (f (j,x)).property⟩
  have hgcont (j : ℕ) : Continuous (g j) := (hcont j).subtype_mk _
  have hgdisc : IsDiscreteFamily (fun j ↦ range (g j)) :=
    isDiscreteFamily_subtype_ranges g (isDiscreteFamily_of_locallyFinite _
      (cardApprox_locallyFinite A hao hac F a ha)
      (fun j ↦ (isCompact_range (hcont j)).isClosed) hsep)
  refine ⟨fun x ↦ g x.1 x.2, continuous_prod_of_discrete_left.mpr hgcont, ?_, ?_⟩
  · intro x
    obtain ⟨O,hfO,hgO⟩ := hclose x.1 x.2
    obtain ⟨V,hV,hOV⟩ := hWU O.val O.property
    exact ⟨V,hV,hOV hfO,hOV hgO⟩
  · simpa only [image_index_slice] using hgdisc

end PaperN.PartIV
