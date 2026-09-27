import PaperN.PartII.CollectivelyCompactBounds

namespace PaperN.PartII
open Set Metric Filter
open scoped Topology

/-- Uniformly bounded strongly convergent operators converge uniformly on each compact set. -/
theorem strong_eventually_uniform_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖Us n‖ ≤ C)
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x ∈ K, ‖Us n x - U x‖ < ε := by
  let D := C + ‖U‖ + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := ε / (3 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨S, hS, hc⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  have hp : ∀ᶠ n in atTop, ∀ c ∈ S, ‖Us n c - U c‖ < ε / 3 := by
    apply hS.eventually_all.mpr
    intro c _
    simpa only [dist_eq_norm] using
      (eventually_atTop.mpr (Metric.tendsto_atTop.mp (hs c) (ε / 3) (by positivity)))
  filter_upwards [hp] with n hn
  intro x hx
  obtain ⟨c, hcs, hxc⟩ : ∃ c ∈ S, dist x c < δ := by
    simpa only [mem_iUnion, mem_ball, exists_prop] using hc hx
  have h1 : ‖Us n x - Us n c‖ ≤ C * dist x c := by
    rw [← map_sub, dist_eq_norm]
    exact ((Us n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))
  have h2 : ‖U c - U x‖ ≤ ‖U‖ * dist x c := by
    rw [← map_sub, dist_comm x c, dist_eq_norm]
    exact U.le_opNorm _
  have h3 : ‖Us n x - U x‖ ≤ ‖Us n x - Us n c‖ + ‖Us n c - U c‖ + ‖U c - U x‖ := by
    calc
      _ = ‖(Us n x - Us n c) + (Us n c - U c) + (U c - U x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hm : D * dist x c < ε / 3 := by
    have ht := mul_lt_mul_of_pos_left hxc hD
    have hd : D * δ = ε / 3 := by dsimp [δ]; field_simp
    rwa [hd] at ht
  have hn' := hn c hcs
  have hd0 := dist_nonneg (x := x) (y := c)
  dsimp [D] at hm
  linarith

/-- The square of the error operator converges in norm under collective compactness. -/
theorem collectivelyCompact_difference_square_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) :
    Tendsto (fun n ↦ ‖(Us n - U).comp (Us n - U)‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := collectivelyCompact_differences_norm_bound Us U hk
  obtain ⟨K, hK, hmem⟩ := hk
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (strong_eventually_uniform_on_compact Us U hs C hC hb K hK (ε / 2) (by positivity))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hh : ‖(Us n - U).comp (Us n - U)‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    exact (hN n hn (Us n x - U x) (hmem n x hx.le)).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith
end PaperN.PartII
