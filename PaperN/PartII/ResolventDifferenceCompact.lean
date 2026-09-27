import PaperN.PartII.ResolventCompactImages

namespace PaperN.PartII
open Set Filter
open scoped Topology

/-- The vector form of the second resolvent identity. -/
theorem resolvent_apply_sub_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : E →L[ℂ] E) (z : ℂ)
    (hS : z ∈ resolventSet ℂ S) (hT : z ∈ resolventSet ℂ T) (x : E) :
    resolvent S z x - resolvent T z x =
      resolvent S z ((S-T) (resolvent T z x)) := by
  let A := algebraMap ℂ (E →L[ℂ] E) z - S
  let B := algebraMap ℂ (E →L[ℂ] E) z - T
  have hl : Ring.inverse A (A (Ring.inverse B x)) = Ring.inverse B x :=
    congrArg (fun R : E →L[ℂ] E ↦ R (Ring.inverse B x)) (Ring.inverse_mul_cancel A hS)
  have hr : B (Ring.inverse B x) = x :=
    congrArg (fun R : E →L[ℂ] E ↦ R x) (Ring.mul_inverse_cancel B hT)
  have he : S-T = B-A := by dsimp [A,B]; abel
  change Ring.inverse A x - Ring.inverse B x = Ring.inverse A ((S-T) (Ring.inverse B x))
  rw [he]
  simp only [sub_apply, map_sub, hr, hl]

/-- A collectively compact family has common compact images of every bounded ball. -/
theorem collectivelyCompact_bounded_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ts : ℕ → E →L[ℂ] E)
    (ht : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ C → Ts n x ∈ L := by
  obtain ⟨K,hK,hm⟩ := ht
  let c : ℂ := (C+1 : ℝ)
  have hc : ‖c‖ = C+1 := by
    change ‖((C+1 : ℝ) : ℂ)‖ = C+1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; positivity)
  refine ⟨(fun y : E ↦ c • y) '' K, hK.image (continuous_const.smul continuous_id), ?_⟩
  intro n x hx
  have hy : ‖c⁻¹ • x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hc]
    have hi : 0 ≤ (C+1)⁻¹ := inv_nonneg.mpr (by positivity)
    have he : (C+1)⁻¹ * (C+1) = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hx hi]
  refine ⟨Ts n (c⁻¹ • x), hm n _ hy, ?_⟩
  simp only [map_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul]

/-- Resolvent differences over a compact parameter set are collectively compact
on a sufficiently late tail. -/
theorem collectivelyCompact_resolvent_difference_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U) :
    ∃ N : ℕ, ∃ L : Set E, IsCompact L ∧ ∀ n, N ≤ n →
      ∀ z ∈ A, ∀ x, ‖x‖ ≤ 1 → resolvent (Us n) z x - resolvent U z x ∈ L := by
  have hcont : ContinuousOn (resolvent U) A := fun z hz ↦
    (spectrum.hasDerivAt_resolvent_const_left (hr hz)).continuousAt.continuousWithinAt
  obtain ⟨B,hB,hbound⟩ := (hA.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  obtain ⟨K,hK,hm⟩ := collectivelyCompact_bounded_images (fun n ↦ Us n-U) hk B hB.le
  obtain ⟨N,L,hL,himages⟩ := collectivelyCompact_resolvent_tail_compact_images Us U hs hk A hA hr K hK
  obtain ⟨C,hC,hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound Us U hs hk A hA hr
  obtain ⟨M,hM⟩ := eventually_atTop.mp hb
  refine ⟨max N M,L,hL,fun n hn z hz x hx ↦ ?_⟩
  rw [resolvent_apply_sub_eq (Us n) U z (hM n (le_trans (le_max_right _ _) hn) z hz).1 (hr hz)]
  apply himages n (le_trans (le_max_left _ _) hn) z hz
  apply hm n
  have hbz := hbound (resolvent U z) ⟨z,hz,rfl⟩
  calc
    ‖resolvent U z x‖ ≤ ‖resolvent U z‖ * ‖x‖ := (resolvent U z).le_opNorm x
    _ ≤ B * ‖x‖ := mul_le_mul_of_nonneg_right hbz (norm_nonneg _)
    _ ≤ B := by nlinarith
end PaperN.PartII
