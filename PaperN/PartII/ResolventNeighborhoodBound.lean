import PaperN.PartII.InversePerturbationBound

namespace PaperN.PartII
open Set Filter Metric
open scoped Topology

/-- Changing the spectral parameter changes the shifted operator by at most its distance. -/
theorem norm_shift_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (z w : ℂ) :
    ‖(algebraMap ℂ (E →L[ℂ] E) w - T) - (algebraMap ℂ (E →L[ℂ] E) z - T)‖ ≤ dist w z := by
  have he : (algebraMap ℂ (E →L[ℂ] E) w - T) - (algebraMap ℂ (E →L[ℂ] E) z - T) =
      algebraMap ℂ (E →L[ℂ] E) (w - z) := by rw [map_sub]; abel
  rw [he, dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  simp only [Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, norm_smul]
  exact le_rfl

/-- A resolvent bound at one point controls a whole parameter neighbourhood. -/
theorem resolvent_near_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (z : ℂ) (hz : z ∈ resolventSet ℂ T)
    (B : ℝ) (hB : 0 ≤ B) (hb : ‖resolvent T z‖ ≤ B)
    (w : ℂ) (hw : B * dist w z < 1 / 2) :
    w ∈ resolventSet ℂ T ∧ ‖resolvent T w‖ ≤ 2 * B := by
  apply isUnit_and_inverse_norm_le_of_near
    (algebraMap ℂ (E →L[ℂ] E) z - T) (algebraMap ℂ (E →L[ℂ] E) w - T) hz B hB hb
  exact (mul_le_mul_of_nonneg_left (norm_shift_sub_le T z w) hB).trans_lt hw

/-- One neighbourhood and bound work for every sufficiently late operator. -/
theorem collectivelyCompact_eventually_resolvent_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (z : ℂ) (hz : z ∈ resolventSet ℂ U) :
    ∃ r B : ℝ, 0 < r ∧ 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ w ∈ ball z r,
      w ∈ resolventSet ℂ (Us n) ∧ ‖resolvent (Us n) w‖ ≤ B := by
  let A : E →L[ℂ] E := algebraMap ℂ (E →L[ℂ] E) z
  have hstrong : ∀ x, Tendsto (fun n ↦ (A - Us n) x) atTop (𝓝 ((A - U) x)) := by
    intro x
    exact (tendsto_const_nhds (x := A x)).sub (hs x)
  have hcompact : ∃ K : Set E, IsCompact K ∧
      ∀ n x, ‖x‖ ≤ 1 → (A - Us n) x - (A - U) x ∈ K := by
    obtain ⟨K, hK, hm⟩ := hk
    refine ⟨Neg.neg '' K, hK.image continuous_neg, ?_⟩
    intro n x hx
    refine ⟨Us n x - U x, hm n x hx, ?_⟩
    change -(Us n x - U x) = (A x - Us n x) - (A x - U x)
    abel
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_inverse_norm_bound
    (fun n ↦ A - Us n) (A - U) hz hstrong hcompact
  refine ⟨1 / (4 * (B + 1)), 2 * B, by positivity, by positivity, ?_⟩
  filter_upwards [hb] with n hn
  intro w hw
  apply resolvent_near_bound (Us n) z hn.1 B hB hn.2 w
  have hd := mem_ball.mp hw
  have hmul : (4 * (B + 1)) * dist w z < 1 := by
    nlinarith [(lt_div_iff₀ (show 0 < 4 * (B + 1) by positivity)).mp hd]
  have h0 := dist_nonneg (x := w) (y := z)
  nlinarith
end PaperN.PartII
