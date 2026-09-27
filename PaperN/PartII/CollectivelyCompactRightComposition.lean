import PaperN.PartII.StrongCompactImages

namespace PaperN.PartII

/-- Right composition by a uniformly bounded family preserves collective compactness. -/
theorem collectivelyCompact_comp_of_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ts Rs : ℕ → E →L[ℂ] E)
    (ht : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K)
    (C : ℝ) (hC : 0 ≤ C) (hr : ∀ n, ‖Rs n‖ ≤ C) :
    ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 → (Ts n).comp (Rs n) x ∈ L := by
  obtain ⟨K,hK,hmem⟩ := ht
  let c : ℂ := (C+1 : ℝ)
  have hc : ‖c‖ = C+1 := by
    change ‖((C+1 : ℝ) : ℂ)‖ = C+1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hc0 : c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hc]
    positivity
  refine ⟨(fun y : E ↦ c • y) '' K, hK.image (continuous_const.smul continuous_id), ?_⟩
  intro n x hx
  have hRx : ‖Rs n x‖ ≤ C := by
    calc
      _ ≤ ‖Rs n‖ * ‖x‖ := (Rs n).le_opNorm x
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (hr n) (norm_nonneg _)
      _ ≤ C := by nlinarith
  have hy : ‖c⁻¹ • Rs n x‖ ≤ 1 := by
    rw [norm_smul, norm_inv, hc]
    have hi : 0 ≤ (C+1)⁻¹ := inv_nonneg.mpr (by positivity)
    have he : (C+1)⁻¹ * (C+1) = 1 := inv_mul_cancel₀ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hRx hi]
  refine ⟨Ts n (c⁻¹ • Rs n x), hmem n _ hy, ?_⟩
  simp only [map_smul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rfl

open Filter
open scoped Topology

/-- A collectively compact family remains so between a strongly convergent
bounded left factor and a bounded right factor. -/
theorem collectivelyCompact_sandwich
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ls Ts Rs : ℕ → E →L[ℂ] E) (L : E →L[ℂ] E)
    (hl : ∀ x, Tendsto (fun n ↦ Ls n x) atTop (𝓝 (L x)))
    (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hls : ∀ n, ‖Ls n‖ ≤ C) (hrs : ∀ n, ‖Rs n‖ ≤ D)
    (ht : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K) :
    ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 →
      (Ls n).comp ((Ts n).comp (Rs n)) x ∈ K := by
  exact collectivelyCompact_comp_of_strong Ls L hl C hC hls
    (fun n ↦ (Ts n).comp (Rs n))
    (collectivelyCompact_comp_of_norm_bound Ts Rs ht D hD hrs)
end PaperN.PartII

