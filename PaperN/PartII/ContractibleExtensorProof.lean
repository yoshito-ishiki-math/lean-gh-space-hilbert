import PaperN.PartII.GHAbsoluteRetract
import Mathlib.Topology.UrysohnsLemma

namespace PaperN.PartII
open Set Topology TopologicalSpace Filter
open scoped Topology

/-- A contraction turns a neighbourhood extension into a global extension. -/
theorem IsAbsoluteNeighborhoodExtensor.of_contractible
    {X : Type*} [TopologicalSpace X] [ContractibleSpace X]
    (h : IsAbsoluteNeighborhoodExtensor.{_,v} X) : IsAbsoluteExtensor.{_,v} X := by
  classical
  obtain ⟨p, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic X).mp inferInstance
  refine ⟨h.1, ?_⟩
  intro Y _ _ A hA f hf
  letI := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨U, hU, hAU, g, hg, hgf⟩ := h.2 Y A hA f hf
  obtain ⟨V, hV, hAV, hVU⟩ := normal_exists_closure_subset hA hU hAU
  obtain ⟨t, ht0, ht1, ht⟩ := exists_continuous_zero_one_of_isClosed hA
    hV.isClosed_compl (Set.disjoint_left.mpr (fun y ha hv ↦ hv (hAV ha)))
  let T : C(Y, Set.Icc (0 : ℝ) 1) := ⟨fun y ↦ ⟨t y, ht y⟩, t.continuous.subtype_mk _⟩
  let G : U → X := fun y ↦ H (T y.val, g y)
  have hG : Continuous G := H.continuous.comp
    ((T.continuous.comp continuous_subtype_val).prodMk hg)
  let F : Y → X := fun y ↦ if hy : y ∈ U then G ⟨y, hy⟩ else p
  have hFU : ContinuousOn F U := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : U.domRestrict F = G := by
      funext y
      simp [Set.domRestrict, F, y.property]
    rw [heq]
    exact hG
  have hFp : ∀ y ∉ closure V, F y = p := by
    intro y hy
    have hv : y ∉ V := fun hv ↦ hy (subset_closure hv)
    have hT : T y = 1 := by
      apply Subtype.ext
      exact ht1 hv
    dsimp [F]
    split_ifs with hu
    · change H (T y, g ⟨y, hu⟩) = p
      rw [hT]
      exact H.apply_one _
    · rfl
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro y
    by_cases hy : y ∈ U
    · exact hFU.continuousAt (hU.mem_nhds hy)
    · have hv : y ∈ (closure V)ᶜ := fun hv ↦ hy (hVU hv)
      have heq : F =ᶠ[𝓝 y] fun _ ↦ p := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hv] with z hz
        exact hFp z hz
      exact continuousAt_const.congr_of_eventuallyEq heq
  refine ⟨F, hF, ?_⟩
  intro a
  have hu := hAU a.property
  have hT : T a.val = 0 := by
    apply Subtype.ext
    exact ht0 a.property
  simp only [F, dif_pos hu, G, hT, H.apply_zero]
  exact hgf a hu

/-- The registered contractible-ANE-to-AE input is proved internally. -/
theorem contractibleANEToAEInput_proved : ContractibleANEToAEInput := by
  intro X _ _ _ h
  exact h.of_contractible
end PaperN.PartII
