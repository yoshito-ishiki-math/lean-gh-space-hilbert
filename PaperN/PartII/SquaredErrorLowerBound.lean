import PaperN.PartII.SquaredErrorInvertibility

namespace PaperN.PartII
open Filter
open scoped Topology

/-- A half-unit bound on the squared error gives an explicit lower bound for one minus the error. -/
theorem norm_le_one_sub_of_square_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (hT : ‖T.comp T‖ ≤ 1 / 2) (x : E) :
    ‖x‖ ≤ 2 * (1 + ‖T‖) * ‖x - T x‖ := by
  have hsq : ‖T (T x)‖ ≤ (1 / 2 : ℝ) * ‖x‖ :=
    (T.comp T).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
  have ht := T.le_opNorm (x - T x)
  have hid : x = T (T x) + ((x - T x) + T (x - T x)) := by
    rw [map_sub]
    abel
  have hn : ‖x‖ ≤ ‖T (T x)‖ + (‖x - T x‖ + ‖T (x - T x)‖) := by
    calc
      ‖x‖ = ‖T (T x) + ((x - T x) + T (x - T x))‖ := congrArg norm hid
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
  nlinarith

/-- The lower bound is uniform eventually for strongly vanishing collectively compact errors. -/
theorem collectivelyCompact_eventually_one_sub_lowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Ts : ℕ → E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Ts n x) atTop (𝓝 0))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ B * ‖x - Ts n x‖ := by
  have hk' : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x - (0 : E →L[ℂ] E) x ∈ K := by
    simpa using hk
  obtain ⟨C, hC, hb⟩ := collectivelyCompact_differences_norm_bound Ts 0 hk'
  have hh := collectivelyCompact_difference_square_tendsto Ts 0 (by simpa using hs) hk'
  simp only [sub_zero] at hh
  refine ⟨2 * (1 + C), by positivity, ?_⟩
  filter_upwards [hh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn
  intro x
  exact (norm_le_one_sub_of_square_bound (Ts n) hn.le x).trans
    (mul_le_mul_of_nonneg_right (by linarith [hb n]) (norm_nonneg _))

/-- Uniform lower bounds turn strong convergence into convergence of solutions. -/
theorem tendsto_solutions_of_uniform_lowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (B : ℝ) (hb : ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ B * ‖Us n x‖)
    (ys : ℕ → E) (y x : E) (hy : Tendsto ys atTop (𝓝 y)) (hx : U x = y)
    (xs : ℕ → E) (heq : ∀ᶠ n in atTop, Us n (xs n) = ys n) :
    Tendsto xs atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim : Tendsto (fun n ↦ B * ‖ys n - Us n x‖) atTop (𝓝 0) := by
    have hh := (hy.sub (hs x)).norm.const_mul B
    simpa [hx] using hh
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) _ hlim
  filter_upwards [hb, heq] with n hn he
  have h := hn (xs n - x)
  rwa [map_sub, he] at h
end PaperN.PartII
