import PaperN.PartII.UniversalAbsoluteRetract

namespace PaperN.PartII
open Set Topology TopologicalSpace
universe v

/-- A separable small factor transports a neighbourhood retraction back to any ambient. -/
theorem IsSeparableAbsoluteNeighborhoodRetract.retraction_of_factor
    {X Y : Type*} {Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [MetricSpace Z] [SecondCountableTopology Z]
    (h : IsSeparableAbsoluteNeighborhoodRetract.{_,0} X)
    (e : X → Y) (he : Continuous e) (f : Y → Z) (hf : Continuous f)
    (hfe : IsEmbedding (f ∘ e)) (d : Y → ℝ) (hd : Continuous d)
    (hz : ∀ y, d y = 0 ↔ y ∈ range e) :
    ∃ U : Set Y, IsOpen U ∧ range e ⊆ U ∧
      ∃ r : U → X, Continuous r ∧ ∀ x (hx : e x ∈ U), r ⟨e x, hx⟩ = x := by
  let F : Y → range (fun y ↦ (d y, f y)) := fun y ↦ ⟨(d y, f y), ⟨y, rfl⟩⟩
  have hF : Continuous F := (hd.prodMk hf).subtype_mk _
  obtain ⟨V, hv, hs, r, hr, hre⟩ := h.2 _ (F ∘ e)
    (closedEmbedding_into_factor_range e he f hf hfe d hd hz)
  refine ⟨F ⁻¹' V, hv.preimage hF, ?_, fun y ↦ r ⟨F y.val, y.property⟩, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact hs ⟨x, rfl⟩
  · exact hr.comp ((hF.comp continuous_subtype_val).subtype_mk _)
  · intro x hx
    exact hre x hx

/-- The separable-to-metrizable ambient enlargement, proved by a countable Tietze factor. -/
theorem IsSeparableAbsoluteNeighborhoodRetract.allUniverses
    {X : Type*} [TopologicalSpace X] [SeparableSpace X]
    (h : IsSeparableAbsoluteNeighborhoodRetract.{_,0} X) :
    IsAbsoluteNeighborhoodRetract.{_,v} X := by
  letI : MetrizableSpace X := h.1
  cases isEmpty_or_nonempty X with
  | inl hx =>
    letI := hx
    refine ⟨h.1, ?_⟩
    intro Y _ _ e he
    refine ⟨∅, isOpen_empty, ?_, (fun y ↦ False.elim y.property), continuous_of_discreteTopology, ?_⟩
    · rintro y ⟨x, _⟩
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x
  | inr hx =>
    letI := hx
    letI := TopologicalSpace.metrizableSpaceMetric X
    letI := TopologicalSpace.metrizableSpaceMetric (ℕ → ℝ)
    obtain ⟨i, hi⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
    let j : X → ℕ → ℝ := fun x n ↦ (i x n).val
    have hj : IsEmbedding j :=
      (IsEmbedding.piMap (fun _ : ℕ ↦ IsEmbedding.subtypeVal)).comp hi
    refine ⟨h.1, ?_⟩
    intro Y _ _ e he
    letI := TopologicalSpace.metrizableSpaceMetric Y
    obtain ⟨f, hf⟩ := (⟨j, hj.continuous⟩ : C(X, ℕ → ℝ)).exists_extension' he
    apply h.retraction_of_factor e he.continuous f f.continuous
      (by rw [hf]; exact hj) (fun y ↦ Metric.infDist y (range e))
      (Metric.continuous_infDist_pt _)
    intro y
    exact (he.isClosed_range.mem_iff_infDist_zero (range_nonempty e)).symm

/-- The previously registered Hanner category input is now internally inhabited. -/
theorem hannerANRCategoryInput_proved : HannerANRCategoryInput := by
  intro X _ _ h
  exact h.allUniverses
end PaperN.PartII
