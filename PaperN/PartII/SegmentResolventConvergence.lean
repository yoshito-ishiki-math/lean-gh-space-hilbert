import PaperN.PartII.InverseDifferenceBound
import PaperN.PartII.SegmentResolvent

namespace PaperN.PartII
open Set Filter MeasureTheory
open scoped Topology

/-- A uniform vector resolvent error bounds the error of one oriented edge integral. -/
theorem segmentResolvent_apply_sub_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S T : E →L[ℂ] E) (a b : ℂ)
    (hS : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ S)
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ T)
    (x : E) (δ : ℝ)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖resolvent S (segmentParameter a b t) x - resolvent T (segmentParameter a b t) x‖ ≤ δ) :
    ‖segmentResolvent S a b x - segmentResolvent T a b x‖ ≤ ‖b-a‖ * δ := by
  have hs := segmentResolvent_integrable S a b hS
  have ht := segmentResolvent_integrable T a b hT
  have he : segmentResolvent S a b x - segmentResolvent T a b x =
      (∫ t in (0 : ℝ)..1,
        ((b-a) • resolvent S (segmentParameter a b t) -
          (b-a) • resolvent T (segmentParameter a b t))) x := by
    rw [intervalIntegral.integral_sub hs ht]
    rfl
  rw [he, ContinuousLinearMap.intervalIntegral_apply (hs.sub ht)]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := ‖b-a‖ * δ) (f := fun t ↦
      (((b-a) • resolvent S (segmentParameter a b t) -
        (b-a) • resolvent T (segmentParameter a b t)) : E →L[ℂ] E) x) (by
      intro t ht'
      have hm : t ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          (show t ∈ Icc (0 : ℝ) 1 from ⟨(by simpa using ht'.1.le), (by simpa using ht'.2)⟩)
      simp only [sub_apply, smul_apply, ← smul_sub, norm_smul]
      exact mul_le_mul_of_nonneg_left (hd t hm) (norm_nonneg _))
  simpa using hn

/-- Strong convergence of the actual operator-valued line-segment integral. -/
theorem collectivelyCompact_segmentResolvent_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (a b : ℂ)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U)
    (x : E) :
    Tendsto (fun n ↦ segmentResolvent (Us n) a b x) atTop
      (𝓝 (segmentResolvent U a b x)) := by
  let A := segmentParameter a b '' Icc (0 : ℝ) 1
  have hA : IsCompact A := isCompact_Icc.image (by unfold segmentParameter; fun_prop)
  have hAr : A ⊆ resolventSet ℂ U := by
    rintro z ⟨t, ht, rfl⟩
    exact hr t ht
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound
    Us U hs hk A hA hAr
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hd := collectivelyCompact_resolvent_uniform_on_compact Us U hs hk A hA hAr x
    (ε / (‖b-a‖ + 1)) (div_pos hε (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hb.and hd)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [dist_eq_norm]
  have hh := segmentResolvent_apply_sub_norm_le (Us n) U a b
    (fun t ht ↦ ((hN n hn).1 _ ⟨t, ht, rfl⟩).1) hr x (ε / (‖b-a‖ + 1))
    (fun t ht ↦ ((hN n hn).2 _ ⟨t, ht, rfl⟩).le)
  apply hh.trans_lt
  have hp : 0 < ε / (‖b-a‖ + 1) := div_pos hε (by positivity)
  have he : (‖b-a‖ + 1) * (ε / (‖b-a‖ + 1)) = ε := by field_simp
  nlinarith
end PaperN.PartII

