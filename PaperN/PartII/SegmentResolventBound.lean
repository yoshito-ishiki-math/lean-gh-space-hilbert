import PaperN.PartII.SegmentResolventConvergence

namespace PaperN.PartII
open Set Filter MeasureTheory
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The operator norm of an edge integral is at most length times resolvent bound. -/
theorem segmentResolvent_norm_le (U : E →L[ℂ] E) (a b : ℂ) (B : ℝ)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖resolvent U (segmentParameter a b t)‖ ≤ B) :
    ‖segmentResolvent U a b‖ ≤ ‖b-a‖ * B := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖b-a‖ * B)
    (f := fun t ↦ (b-a) • resolvent U (segmentParameter a b t)) (by
      intro t ht
      have hm : t ∈ Icc (0 : ℝ) 1 := ⟨by simpa using ht.1.le, by simpa using ht.2⟩
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hb t hm) (norm_nonneg _))
  simpa [segmentResolvent] using hn

/-- A common eventual norm bound for segment resolvent integrals. -/
theorem collectivelyCompact_segmentResolvent_eventually_norm_bound
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (a b : ℂ)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, ‖segmentResolvent (Us n) a b‖ ≤ B := by
  let A := segmentParameter a b '' Icc (0 : ℝ) 1
  have hA : IsCompact A := isCompact_Icc.image (by unfold segmentParameter; fun_prop)
  have hAr : A ⊆ resolventSet ℂ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hr t ht
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound Us U hs hk A hA hAr
  refine ⟨‖b-a‖ * B, mul_nonneg (norm_nonneg _) hB, ?_⟩
  filter_upwards [hb] with n hn
  exact segmentResolvent_norm_le (Us n) a b B (fun t ht ↦ (hn _ ⟨t, ht, rfl⟩).2)

/-- Include the finitely many initial terms in a common segment integral bound. -/
theorem collectivelyCompact_segmentResolvent_norm_bound
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (a b : ℂ)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖segmentResolvent (Us n) a b‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_segmentResolvent_eventually_norm_bound Us U hs hk a b hr
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let C := ∑ n ∈ Finset.range N, ‖segmentResolvent (Us n) a b‖
  have hC : 0 ≤ C := Finset.sum_nonneg (fun n _ ↦ norm_nonneg _)
  refine ⟨B+C, add_nonneg hB hC, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_add_of_nonneg_right hC)
  · have hh : ‖segmentResolvent (Us n) a b‖ ≤ C :=
      Finset.single_le_sum (fun i _ ↦ norm_nonneg (segmentResolvent (Us i) a b)) (show n ∈ Finset.range N from Finset.mem_range.mpr (by omega))
    exact hh.trans (le_add_of_nonneg_left hB)
end PaperN.PartII

