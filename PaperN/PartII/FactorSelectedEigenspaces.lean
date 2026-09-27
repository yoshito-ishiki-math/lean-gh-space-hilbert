import PaperN.PartII.FactorEigenspaces

namespace PaperN.PartII
variable {𝕜 E F : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup F] [Module 𝕜 F]

abbrev selectedEigenspaces (U : E →ₗ[𝕜] E) (s : Set 𝕜) : Submodule 𝕜 E :=
  ⨆ a ∈ s, Module.End.eigenspace U a

theorem factor_map_eigenspace (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F)
    (a : 𝕜) (ha : a ≠ 0) :
    Submodule.map B (Module.End.eigenspace (A.comp B) a) =
      Module.End.eigenspace (B.comp A) a := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact (factorEigenspaceEquiv A B a ha ⟨x,hx⟩).property
  · intro y hy
    let x := (factorEigenspaceEquiv A B a ha).symm ⟨y,hy⟩
    refine ⟨x, x.property, ?_⟩
    exact congrArg Subtype.val ((factorEigenspaceEquiv A B a ha).apply_symm_apply ⟨y,hy⟩)

theorem factor_map_selectedEigenspaces (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F)
    (s : Set 𝕜) (hs : 0 ∉ s) :
    Submodule.map B (selectedEigenspaces (A.comp B) s) =
      selectedEigenspaces (B.comp A) s := by
  simp only [selectedEigenspaces, Submodule.map_iSup]
  apply iSup_congr
  intro a
  apply iSup_congr
  intro ha
  exact factor_map_eigenspace A B a (fun h ↦ hs (h ▸ ha))

theorem factor_selected_restrict_zero (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F)
    (s : Set 𝕜) (hs : 0 ∉ s) (x : E)
    (hx : x ∈ selectedEigenspaces (A.comp B) s) (hB : B x = 0) : x = 0 := by
  have hdis := (Module.End.eigenspaces_iSupIndep (A.comp B)).disjoint_biSup hs
  have hz : x ∈ Module.End.eigenspace (A.comp B) 0 := by
    rw [Module.End.mem_eigenspace_iff]
    simp [hB]
  have hh := hdis.le_bot ⟨hz,hx⟩
  exact hh

noncomputable def factorSelectedEigenspacesEquiv
    (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F) (s : Set 𝕜) (hs : 0 ∉ s) :
    selectedEigenspaces (A.comp B) s ≃ₗ[𝕜] selectedEigenspaces (B.comp A) s := by
  let V := selectedEigenspaces (A.comp B) s
  let W := selectedEigenspaces (B.comp A) s
  let R : V →ₗ[𝕜] W := (B.domRestrict V).codRestrict W (by
    intro x
    change B x ∈ selectedEigenspaces (B.comp A) s
    rw [← factor_map_selectedEigenspaces A B s hs]
    exact ⟨x,x.property,rfl⟩)
  apply LinearEquiv.ofBijective R
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hzero : B ((x : E)-(y : E)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    exact sub_eq_zero.mp (factor_selected_restrict_zero A B s hs _
      (V.sub_mem x.property y.property) hzero)
  · intro y
    have hy : (y : F) ∈ selectedEigenspaces (B.comp A) s := y.property
    rw [← factor_map_selectedEigenspaces A B s hs] at hy
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,hx⟩, Subtype.ext hxy⟩

theorem factorSelectedEigenspacesEquiv_apply
    (A : F →ₗ[𝕜] E) (B : E →ₗ[𝕜] F) (s : Set 𝕜) (hs : 0 ∉ s)
    (x : selectedEigenspaces (A.comp B) s) :
    (factorSelectedEigenspacesEquiv A B s hs x : F) = B x := rfl
end PaperN.PartII
