import PaperN.PartII.AbsoluteExtensor
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace PaperN.PartII
open Set Topology TopologicalSpace

/-- A metrizable coordinate extension plus a zero-set detector converts an ANR
retraction into a neighbourhood extension. The target factor has the universe of Z. -/
theorem IsAbsoluteNeighborhoodRetract.extension_of_factor
    {X Y : Type*} {Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [MetrizableSpace Z]
    (h : IsAbsoluteNeighborhoodRetract.{_,0} X)
    (A : Set Y) (f : A → X) (j : X → Z) (hj : IsEmbedding j)
    (g : Y → Z) (hg : Continuous g) (hgf : ∀ a : A, g a = j (f a))
    (d : Y → ℝ) (hd : Continuous d) (hz : ∀ y, d y = 0 ↔ y ∈ A) :
    ∃ U : Set Y, IsOpen U ∧ A ⊆ U ∧ ∃ F : U → X, Continuous F ∧
      ∀ (a : A) (ha : (a : Y) ∈ U), F ⟨a,ha⟩ = f a := by
  let S : Set (ℝ × Z) := range (fun x : X ↦ ((0 : ℝ),j x)) ∪ range (fun y : Y ↦ (d y,g y))
  let i : X → S := fun x ↦ ⟨(0,j x),Or.inl ⟨x,rfl⟩⟩
  let G : Y → S := fun y ↦ ⟨(d y,g y),Or.inr ⟨y,rfl⟩⟩
  have hi : Continuous i := (continuous_const.prodMk hj.continuous).subtype_mk _
  have hG : Continuous G := (hd.prodMk hg).subtype_mk _
  have hie : IsEmbedding i := IsEmbedding.of_comp hi
    (continuous_snd.comp continuous_subtype_val) hj
  have hirange : range i = {w : S | w.val.1 = 0} := by
    ext w
    constructor
    · rintro ⟨x,rfl⟩
      rfl
    · intro hw
      rcases w.property with ⟨x,hx⟩ | ⟨y,hy⟩
      · exact ⟨x,Subtype.ext hx⟩
      · have hy0 : d y = 0 := (congrArg Prod.fst hy).trans hw
        have ha : y ∈ A := (hz y).mp hy0
        refine ⟨f ⟨y,ha⟩,Subtype.ext ?_⟩
        change (0,j (f ⟨y,ha⟩)) = w.val
        exact (Prod.ext hy0.symm (hgf ⟨y,ha⟩).symm).trans hy
  have hic : IsClosedEmbedding i := ⟨hie, by
    rw [hirange]
    exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const⟩
  obtain ⟨V,hV,hVi,r,hr,hri⟩ := h.2 S i hic
  have hGa (a : A) : G a = i (f a) := by
    apply Subtype.ext
    exact Prod.ext ((hz a).mpr a.property) (hgf a)
  refine ⟨G ⁻¹' V,hV.preimage hG,?_,fun y ↦ r ⟨G y,y.property⟩,?_,?_⟩
  · intro a ha
    change G a ∈ V
    rw [hGa ⟨a,ha⟩]
    exact hVi ⟨f ⟨a,ha⟩,rfl⟩
  · exact hr.comp ((hG.comp continuous_subtype_val).subtype_mk _)
  · intro a ha
    have he : (⟨G a,ha⟩ : V) = ⟨i (f a),hVi ⟨f a,rfl⟩⟩ := Subtype.ext (hGa a)
    change r ⟨G a,ha⟩ = f a
    rw [he]
    exact hri _ _
end PaperN.PartII
