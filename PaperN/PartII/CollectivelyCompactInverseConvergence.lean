import PaperN.PartII.SquaredErrorLowerBound

namespace PaperN.PartII
open Filter
open scoped Topology

/-- Uniform lower bounds for perturbations of an arbitrary invertible limit. -/
theorem collectivelyCompact_eventually_lowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E) (hu : IsUnit U)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ∀ x, ‖x‖ ≤ B * ‖Us n x‖ := by
  obtain ⟨u, rfl⟩ := hu
  let R : E →L[ℂ] E := ↑u⁻¹
  let Ts := fun n ↦ R.comp ((u : E →L[ℂ] E) - Us n)
  have ht : ∀ x, Tendsto (fun n ↦ Ts n x) atTop (𝓝 0) := by
    intro x
    have hh := R.continuous.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (u : E →L[ℂ] E) x)).sub (hs x))
    simpa [Ts, Function.comp_def, map_sub] using hh
  obtain ⟨K, hK, hmem⟩ := hk
  have htk : ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ L := by
    refine ⟨(fun y ↦ R (-y)) '' K, hK.image (R.continuous.comp continuous_neg), ?_⟩
    intro n x hx
    refine ⟨Us n x - (u : E →L[ℂ] E) x, hmem n x hx, ?_⟩
    simp [Ts, neg_sub]
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_one_sub_lowerBound Ts ht htk
  refine ⟨B * ‖R‖, mul_nonneg hB.le (norm_nonneg _), ?_⟩
  filter_upwards [hb] with n hn
  intro x
  have hRU : R ((u : E →L[ℂ] E) x) = x := by
    have hh : R * (u : E →L[ℂ] E) = 1 := by simp [R, ← Units.val_mul]
    exact congrArg (fun T : E →L[ℂ] E ↦ T x) hh
  have hid : x - Ts n x = R (Us n x) := by
    simp only [Ts, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply, map_sub, hRU]
    abel
  have hn' := hn x
  rw [hid] at hn'
  exact hn'.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (R.le_opNorm (Us n x)) hB.le)


/-- The inverse operators converge strongly, including for converging right-hand sides. -/
theorem collectivelyCompact_inverse_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E) (hu : IsUnit U)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (ys : ℕ → E) (y : E) (hy : Tendsto ys atTop (𝓝 y)) :
    Tendsto (fun n ↦ Ring.inverse (Us n) (ys n)) atTop (𝓝 (Ring.inverse U y)) := by
  obtain ⟨B, _, hb⟩ := collectivelyCompact_eventually_lowerBound Us U hu hs hk
  apply tendsto_solutions_of_uniform_lowerBound Us U hs B hb ys y (Ring.inverse U y) hy
  · exact congrArg (fun T : E →L[ℂ] E ↦ T y) (Ring.mul_inverse_cancel U hu)
  · filter_upwards [collectivelyCompact_eventually_isUnit Us U hu hs hk] with n hn
    exact congrArg (fun T : E →L[ℂ] E ↦ T (ys n)) (Ring.mul_inverse_cancel (Us n) hn)
end PaperN.PartII
