import PaperN.PartII.CompactIntegralImages
import PaperN.PartII.SegmentResolventConvergence

namespace PaperN.PartII
open Set MeasureTheory

/-- Integrating a family of operator-valued paths with common compact vector
images preserves collective compactness. -/
theorem collectivelyCompact_intervalIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : ℕ → ℝ → E →L[ℂ] E)
    (hi : ∀ n, IntervalIntegrable (F n) volume 0 1)
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      ∀ x, ‖x‖ ≤ 1 → F n t x ∈ K) :
    ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 →
      (∫ t in (0 : ℝ)..1, F n t) x ∈ L := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨K,hK,hm⟩ := hk
  obtain ⟨L,hL,hint⟩ := compact_unit_interval_integral_container K hK
  refine ⟨L,hL,fun n x hx ↦ ?_⟩
  rw [ContinuousLinearMap.intervalIntegral_apply (hi n)]
  apply hint (fun t ↦ F n t x)
  · let ev : (E →L[ℂ] E) →L[ℂ] E := ContinuousLinearMap.apply ℂ E x
    exact ⟨ev.integrable_comp (hi n).1, ev.integrable_comp (hi n).2⟩
  · exact fun t ht ↦ hm n t ht x hx

/-- Compact vector images of resolvent differences give collective compactness
of the corresponding edge-integral differences. -/
theorem collectivelyCompact_segmentResolvent_difference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E) (a b : ℂ)
    (hs : ∀ n t, t ∈ Icc (0 : ℝ) 1 → segmentParameter a b t ∈ resolventSet ℂ (Us n))
    (hu : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U)
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      ∀ x, ‖x‖ ≤ 1 →
        resolvent (Us n) (segmentParameter a b t) x - resolvent U (segmentParameter a b t) x ∈ K) :
    ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 →
      segmentResolvent (Us n) a b x - segmentResolvent U a b x ∈ L := by
  let F := fun n t ↦ (b-a) • resolvent (Us n) (segmentParameter a b t) -
    (b-a) • resolvent U (segmentParameter a b t)
  have hi : ∀ n, IntervalIntegrable (F n) volume 0 1 := fun n ↦
    (segmentResolvent_integrable (Us n) a b (hs n)).sub (segmentResolvent_integrable U a b hu)
  have hc : ∃ K : Set E, IsCompact K ∧ ∀ n t, t ∈ Icc (0 : ℝ) 1 →
      ∀ x, ‖x‖ ≤ 1 → F n t x ∈ K := by
    obtain ⟨K,hK,hm⟩ := hk
    refine ⟨(fun y : E ↦ (b-a) • y) '' K, hK.image (continuous_const.smul continuous_id), ?_⟩
    intro n t ht x hx
    refine ⟨_,hm n t ht x hx, ?_⟩
    simp [F, smul_sub]
  obtain ⟨L,hL,hm⟩ := collectivelyCompact_intervalIntegral F hi hc
  refine ⟨L,hL,fun n x hx ↦ ?_⟩
  have hh := hm n x hx
  dsimp [F] at hh
  rw [intervalIntegral.integral_sub
    (segmentResolvent_integrable (Us n) a b (hs n))
    (segmentResolvent_integrable U a b hu)] at hh
  exact hh
end PaperN.PartII

