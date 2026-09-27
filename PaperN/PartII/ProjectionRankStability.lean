import PaperN.PartII.FiniteSubspaceStability

namespace PaperN.PartII
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A small squared difference gives injectivity on the other projection range. -/
theorem projection_injective_on_range_of_square_norm_lt_one
    (P Q : E →L[ℂ] E) (hQ : ∀ x, Q (Q x) = Q x)
    (hsmall : ‖(Q-P).comp (Q-P)‖ < 1) :
    Function.Injective (fun x : LinearMap.range Q.toLinearMap ↦ P x) := by
  have hzero : ∀ x : LinearMap.range Q.toLinearMap, P x = 0 → x = 0 := by
    intro x hx
    have hfix : Q x = x := by
      obtain ⟨y, hy⟩ := x.property
      change Q y = (x : E) at hy
      rw [← hy, hQ]
    have he : ((Q-P).comp (Q-P)) x = (x : E) := by
      change Q (Q x - P x) - P (Q x - P x) = (x : E)
      simp only [hx, sub_zero, hfix]
    have hn := ((Q-P).comp (Q-P)).le_opNorm (x : E)
    rw [he] at hn
    have hn0 := norm_nonneg (x : E)
    have hz : ‖(x : E)‖ = 0 := by nlinarith
    apply Subtype.ext
    exact norm_eq_zero.mp hz
  intro x y hxy
  change P (x : E) = P (y : E) at hxy
  have hz := hzero (x-y) (by
    change P ((x : E) - (y : E)) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp hz

/-- Two projections with small squared difference have equal finite rank. -/
theorem projection_finite_rank_eq_of_square_norm_lt_one
    (P Q : E →L[ℂ] E) (hP : ∀ x, P (P x) = P x) (hQ : ∀ x, Q (Q x) = Q x)
    (hsmall : ‖(Q-P).comp (Q-P)‖ < 1)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)] :
    FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range Q.toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
  let f := P.toLinearMap.rangeRestrict.comp (LinearMap.range Q.toLinearMap).subtype
  have hf : Function.Injective f := by
    intro x y hxy
    apply projection_injective_on_range_of_square_norm_lt_one P Q hQ hsmall
    exact congrArg Subtype.val hxy
  letI := FiniteDimensional.of_injective f hf
  have hrev : ‖(P-Q).comp (P-Q)‖ < 1 := by
    have he : (P-Q).comp (P-Q) = (Q-P).comp (Q-P) := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]
      abel
    rwa [he]
  let g := Q.toLinearMap.rangeRestrict.comp (LinearMap.range P.toLinearMap).subtype
  have hg : Function.Injective g := by
    intro x y hxy
    apply projection_injective_on_range_of_square_norm_lt_one Q P hP hrev
    exact congrArg Subtype.val hxy
  exact ⟨inferInstance, le_antisymm (LinearMap.finrank_le_finrank_of_injective hf)
    (LinearMap.finrank_le_finrank_of_injective hg)⟩

open Filter
open scoped Topology

/-- Collectively compact, strongly convergent projections have stable finite rank. -/
theorem collectivelyCompact_projection_rank_stable
    (Ps : ℕ → E →L[ℂ] E) (P : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Ps n x) atTop (𝓝 (P x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ps n x - P x ∈ K)
    (hP : ∀ x, P (P x) = P x)
    (hPs : ∀ᶠ n in atTop, ∀ x, Ps n (Ps n x) = Ps n x)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)] :
    ∀ᶠ n in atTop, FiniteDimensional ℂ (LinearMap.range (Ps n).toLinearMap) ∧
      Module.finrank ℂ (LinearMap.range (Ps n).toLinearMap) =
        Module.finrank ℂ (LinearMap.range P.toLinearMap) := by
  have ht := collectivelyCompact_difference_square_tendsto Ps P hs hk
  have he : ∀ᶠ n in atTop, ‖(Ps n-P).comp (Ps n-P)‖ < 1 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, hPs] with n hn hp
  exact projection_finite_rank_eq_of_square_norm_lt_one P (Ps n) hP hp hn
end PaperN.PartII

