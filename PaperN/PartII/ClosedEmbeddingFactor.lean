import PaperN.PartII.SmallAmbientRetract

namespace PaperN.PartII
open Set Topology

/-- A continuous factor retaining an embedding and a zero-set detector retains a closed embedding. -/
theorem closedEmbedding_into_factor_range
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : X → Y) (he : Continuous e) (f : Y → Z) (hf : Continuous f) (hfe : IsEmbedding (f ∘ e))
    (d : Y → ℝ) (hd : Continuous d) (hz : ∀ y, d y = 0 ↔ y ∈ range e) :
    IsClosedEmbedding (fun x ↦
      (⟨(d (e x), f (e x)), ⟨e x, rfl⟩⟩ : range (fun y ↦ (d y, f y)))) := by
  let F := fun y ↦ (d y, f y)
  let j : X → range F := fun x ↦ ⟨F (e x), ⟨e x, rfl⟩⟩
  have hj : Continuous j := ((hd.comp he).prodMk (hf.comp he)).subtype_mk _
  have hi : IsEmbedding j := IsEmbedding.of_comp hj
    (continuous_snd.comp continuous_subtype_val) hfe
  refine ⟨hi, ?_⟩
  have hr : range j = {z : range F | z.val.1 = 0} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact (hz (e x)).2 ⟨x, rfl⟩
    · intro h
      obtain ⟨y, hy⟩ := z.property
      have hy0 : d y = 0 := by
        have hh := congrArg Prod.fst hy
        exact hh.trans h
      obtain ⟨x, hx⟩ := (hz y).1 hy0
      refine ⟨x, ?_⟩
      apply Subtype.ext
      change F (e x) = z.val
      rw [hx]
      exact hy
  change IsClosed (range j)
  rw [hr]
  exact isClosed_eq (continuous_fst.comp continuous_subtype_val) continuous_const

/-- A small continuous factor preserving the closed target suffices for a global retraction. -/
theorem IsAbsoluteRetract.retraction_of_factor
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MetricSpace Z] [Small.{0} Z]
    (h : IsAbsoluteRetract.{_,0} X)
    (e : X → Y) (he : Continuous e) (f : Y → Z) (hf : Continuous f)
    (hfe : IsEmbedding (f ∘ e)) (d : Y → ℝ) (hd : Continuous d)
    (hz : ∀ y, d y = 0 ↔ y ∈ range e) :
    ∃ r : Y → X, Continuous r ∧ Function.LeftInverse r e := by
  let F : Y → range (fun y ↦ (d y, f y)) := fun y ↦ ⟨(d y, f y), ⟨y, rfl⟩⟩
  have hF : Continuous F := (hd.prodMk hf).subtype_mk _
  obtain ⟨r, hr, hre⟩ := h.retraction_of_small (F ∘ e)
    (closedEmbedding_into_factor_range e he f hf hfe d hd hz)
  exact ⟨r ∘ F, hr.comp hF, hre⟩
end PaperN.PartII
