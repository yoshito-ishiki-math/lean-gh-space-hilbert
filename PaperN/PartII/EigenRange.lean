import PaperN.PartII.EigenProjection

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The closed span of the eigenspaces with eigenvalue in `s`. -/
abbrev closedEigenSpan (U : E →L[ℂ] E) (s : Set ℂ) : Submodule ℂ E :=
  (⨆ a ∈ s, Module.End.eigenspace U.toLinearMap a).topologicalClosure

/-- A continuous spectral selector has precisely the selected closed eigenspan as its range. -/
theorem range_eq_closedEigenSpan (U P : E →L[ℂ] E) (s : Set ℂ)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤)
    (hfix : ∀ a ∈ s, ∀ v, U v = a • v → P v = v)
    (hkill : ∀ a ∉ s, ∀ v, U v = a • v → P v = 0) :
    LinearMap.range P.toLinearMap = closedEigenSpan U s := by
  let V := closedEigenSpan U s
  have hclosed : IsClosed (V : Set E) := Submodule.isClosed_topologicalClosure _
  have hmap : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a) ≤
      V.comap P.toLinearMap := by
    apply iSup_le
    intro a v hv
    have he := Module.End.mem_eigenspace_iff.mp hv
    change U v = a • v at he
    change P v ∈ V
    by_cases ha : a ∈ s
    · rw [hfix a ha v he]
      have hin : Module.End.eigenspace U.toLinearMap a ≤
          ⨆ b ∈ s, Module.End.eigenspace U.toLinearMap b :=
        le_iSup_of_le a (le_iSup_of_le ha le_rfl)
      exact Submodule.le_topologicalClosure _ (hin hv)
    · rw [hkill a ha v he]
      exact V.zero_mem
  have hall := (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure_minimal
    hmap (hclosed.preimage P.continuous)
  rw [hd] at hall
  have hfixed : V ≤ (P - ContinuousLinearMap.id ℂ E).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro a
      apply iSup_le
      intro ha v hv
      have he := Module.End.mem_eigenspace_iff.mp hv
      change U v = a • v at he
      change P v - v = 0
      exact sub_eq_zero.mpr (hfix a ha v he)
    · exact (P - ContinuousLinearMap.id ℂ E).isClosed_ker
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    exact hall (show w ∈ (⊤ : Submodule ℂ E) from trivial)
  · intro v hv
    refine ⟨v, ?_⟩
    have h := hfixed hv
    change P v - v = 0 at h
    exact sub_eq_zero.mp h

/-- The complementary eigenspan is the kernel of a continuous spectral selector. -/
theorem ker_eq_closedEigenSpan_compl (U P : E →L[ℂ] E) (s : Set ℂ)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤)
    (hfix : ∀ a ∈ s, ∀ v, U v = a • v → P v = v)
    (hkill : ∀ a ∉ s, ∀ v, U v = a • v → P v = 0) :
    P.ker = closedEigenSpan U sᶜ := by
  have hid : P.comp P = P := by
    apply idempotent_of_dense_eigenspaces U P hd
    intro a v hv
    by_cases ha : a ∈ s
    · exact Or.inr (hfix a ha v hv)
    · exact Or.inl (hkill a ha v hv)
  have hr := range_eq_closedEigenSpan U (ContinuousLinearMap.id ℂ E - P) sᶜ hd
    (by
      intro a ha v hv
      change v - P v = v
      rw [hkill a ha v hv, sub_zero])
    (by
      intro a ha v hv
      change v - P v = 0
      rw [hfix a (by simpa using ha) v hv, sub_self])
  rw [← hr]
  apply le_antisymm
  · intro v hv
    refine ⟨v, ?_⟩
    change v - P v = v
    change P v = 0 at hv
    rw [hv, sub_zero]
  · rintro v ⟨w, rfl⟩
    change P (w - P w) = 0
    rw [map_sub]
    have hi : P (P w) = P w := DFunLike.congr_fun hid w
    rw [hi, sub_self]

open Metric Set in
theorem circleResolvent_kills_not_inside [CompleteSpace E] (U : E →L[ℂ] E)
    (a c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (ha : a ∉ ball c r) (v : E) (hv : U v = a • v) :
    circleResolvent U c r v = 0 := by
  by_cases hzero : v = 0
  · simp [hzero]
  have he : Module.End.HasEigenvalue U.toLinearMap a :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hv, hzero⟩
  have ho : a ∉ closedBall c r := by
    intro hcl
    have hdist : dist a c = r := le_antisymm hcl (le_of_not_gt ha)
    have hspec : a ∈ spectrum ℂ U := by
      rw [ContinuousLinearMap.spectrum_eq]
      exact he.mem_spectrum
    exact hspec (hz a (mem_sphere.mpr hdist))
  exact circleResolvent_kills_outside U a c r hr hz ho v hv

open Metric Set in
theorem circleResolvent_range [CompleteSpace E] (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤) :
    LinearMap.range (circleResolvent U c r).toLinearMap = closedEigenSpan U (ball c r) := by
  apply range_eq_closedEigenSpan U _ _ hd
  · intro a ha v hv
    exact circleResolvent_fixes_inside U a c r hz ha v hv
  · intro a ha v hv
    exact circleResolvent_kills_not_inside U a c r hr hz ha v hv

open Metric Set in
theorem circleResolvent_ker [CompleteSpace E] (U : E →L[ℂ] E) (c : ℂ) (r : ℝ)
    (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U)
    (hd : (⨆ a : ℂ, Module.End.eigenspace U.toLinearMap a).topologicalClosure = ⊤) :
    (circleResolvent U c r).ker = closedEigenSpan U (ball c r)ᶜ := by
  apply ker_eq_closedEigenSpan_compl U _ _ hd
  · intro a ha v hv
    exact circleResolvent_fixes_inside U a c r hz ha v hv
  · intro a ha v hv
    exact circleResolvent_kills_not_inside U a c r hr hz ha v hv

open Metric Set in
theorem circleResolvent_range_of_compact_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    LinearMap.range (circleResolvent U c r).toLinearMap = closedEigenSpan U (ball c r) := by
  apply circleResolvent_range U c r hr hz
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs

open Metric Set in
theorem circleResolvent_ker_of_compact_symmetric
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    (circleResolvent U c r).ker = closedEigenSpan U (ball c r)ᶜ := by
  apply circleResolvent_ker U c r hr hz
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs

theorem closedEigenSpan_compl_le_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H →L[ℂ] H) (hs : U.toLinearMap.IsSymmetric) (s : Set ℂ) :
    closedEigenSpan U sᶜ ≤ (closedEigenSpan U s)ᗮ := by
  unfold closedEigenSpan
  rw [Submodule.orthogonal_closure]
  apply Submodule.topologicalClosure_minimal _ _ (Submodule.isClosed_orthogonal _)
  change (⨆ a ∈ sᶜ, Module.End.eigenspace U.toLinearMap a) ⟂
    (⨆ a ∈ s, Module.End.eigenspace U.toLinearMap a)
  simp only [Submodule.isOrtho_iSup_left, Submodule.isOrtho_iSup_right]
  intro a ha b hb
  exact hs.orthogonalFamily_eigenspaces.pairwise (by aesop)

open Metric Set in
theorem circleResolvent_eq_starProjection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : H →L[ℂ] H) (hc : IsCompactOperator U) (hs : U.toLinearMap.IsSymmetric)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ U) :
    circleResolvent U c r = (closedEigenSpan U (ball c r)).starProjection := by
  have hid := circleResolvent_idempotent_of_compact_symmetric U hc hs c r hr hz
  have hrange := circleResolvent_range_of_compact_symmetric U hc hs c r hr hz
  have hker := circleResolvent_ker_of_compact_symmetric U hc hs c r hr hz
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [← hrange]
    exact ⟨v, rfl⟩
  · apply closedEigenSpan_compl_le_orthogonal U hs (ball c r)
    rw [← hker]
    change circleResolvent U c r (v - circleResolvent U c r v) = 0
    rw [map_sub]
    have hi : circleResolvent U c r (circleResolvent U c r v) = circleResolvent U c r v :=
      DFunLike.congr_fun hid v
    rw [hi, sub_self]

namespace ComplexKernel
open MeasureTheory Metric Set
universe u
variable {X : Type u} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem distance_circleResolvent_range (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ (distanceOperator μ)) :
    LinearMap.range (circleResolvent (distanceOperator μ) c r).toLinearMap =
      closedEigenSpan (distanceOperator μ) (ball c r) :=
  circleResolvent_range_of_compact_symmetric _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) c r hr hz
theorem distance_circleResolvent_ker (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ (distanceOperator μ)) :
    (circleResolvent (distanceOperator μ) c r).ker =
      closedEigenSpan (distanceOperator μ) (ball c r)ᶜ :=
  circleResolvent_ker_of_compact_symmetric _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) c r hr hz
theorem distance_circleResolvent_eq_starProjection (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hz : ∀ z ∈ sphere c r, z ∈ resolventSet ℂ (distanceOperator μ)) :
    circleResolvent (distanceOperator μ) c r =
      (closedEigenSpan (distanceOperator μ) (ball c r)).starProjection :=
  circleResolvent_eq_starProjection _
    (AmbientKernel.distanceOperator_compact (ContinuousMap.id X) μ isometry_id)
    (distanceOperator_symmetric μ) c r hr hz
end ComplexKernel
end PaperN.PartII
