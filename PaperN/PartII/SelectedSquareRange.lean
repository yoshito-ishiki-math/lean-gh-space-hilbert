import PaperN.PartII.FactorSelectedEigenspaces

namespace PaperN.PartII
variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Selected nonzero eigenspaces lie in the algebraic range of the square. -/
theorem selectedEigenspaces_le_square_range (U : E →ₗ[𝕜] E)
    (s : Set 𝕜) (hs : 0 ∉ s) :
    selectedEigenspaces U s ≤ LinearMap.range (U.comp U) := by
  apply iSup_le
  intro a
  apply iSup_le
  intro ha x hx
  have hn : a ≠ 0 := fun h ↦ hs (h ▸ ha)
  have he := Module.End.mem_eigenspace_iff.mp hx
  refine ⟨(a⁻¹ * a⁻¹) • x, ?_⟩
  simp only [LinearMap.comp_apply, map_smul, he, smul_smul]
  simp [hn, mul_assoc]
end PaperN.PartII
