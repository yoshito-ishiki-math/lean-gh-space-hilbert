import PaperN.PartII.CompactResolventBound

namespace PaperN.PartII

/-- Inverse differences are controlled by the residual at the limit solution. -/
theorem inverse_apply_sub_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : E →L[ℂ] E) (hS : IsUnit S) (hT : IsUnit T) (x : E) :
    ‖Ring.inverse S x - Ring.inverse T x‖ ≤
      ‖Ring.inverse S‖ * ‖(T - S) (Ring.inverse T x)‖ := by
  have hleft : Ring.inverse S (S (Ring.inverse T x)) = Ring.inverse T x := by
    have h := congrArg (fun R : E →L[ℂ] E ↦ R (Ring.inverse T x))
      (Ring.inverse_mul_cancel S hS)
    exact h
  have hright : T (Ring.inverse T x) = x := by
    have h := congrArg (fun R : E →L[ℂ] E ↦ R x) (Ring.mul_inverse_cancel T hT)
    exact h
  calc
    _ = ‖Ring.inverse S ((T - S) (Ring.inverse T x))‖ := by
      simp only [sub_apply, map_sub, hright, hleft]
    _ ≤ _ := (Ring.inverse S).le_opNorm _

/-- Resolvent differences are bounded by the operator error on a limit resolvent vector. -/
theorem resolvent_apply_sub_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (S T : E →L[ℂ] E) (z : ℂ)
    (hS : z ∈ resolventSet ℂ S) (hT : z ∈ resolventSet ℂ T) (x : E) :
    ‖resolvent S z x - resolvent T z x‖ ≤
      ‖resolvent S z‖ * ‖(S - T) (resolvent T z x)‖ := by
  have h := inverse_apply_sub_norm_le
    (algebraMap ℂ (E →L[ℂ] E) z - S)
    (algebraMap ℂ (E →L[ℂ] E) z - T) hS hT x
  have he : (algebraMap ℂ (E →L[ℂ] E) z - T) -
      (algebraMap ℂ (E →L[ℂ] E) z - S) = S - T := by abel
  rw [he] at h
  exact h

open Set Filter
open scoped Topology

/-- Uniform strong resolvent convergence when the limit resolvent orbit is compact. -/
theorem collectivelyCompact_resolvent_uniform_of_compact_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U)
    (x : E) (him : IsCompact ((fun z ↦ resolvent U z x) '' A))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ A, ‖resolvent (Us n) z x - resolvent U z x‖ < ε := by
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound Us U hs hk A hA hr
  obtain ⟨C, hC, hc⟩ := collectivelyCompact_differences_norm_bound Us U hk
  have he := strong_eventually_uniform_on_compact Us U hs C hC hc _ him
    (ε / (B + 1)) (div_pos hε (by positivity))
  filter_upwards [hb, he] with n hn he
  intro z hz
  have hd := he (resolvent U z x) ⟨z, hz, rfl⟩
  have hbz := hn z hz
  have hn0 : 0 ≤ ‖Us n (resolvent U z x) - U (resolvent U z x)‖ := norm_nonneg _
  have hsmall : B * ‖Us n (resolvent U z x) - U (resolvent U z x)‖ < ε := by
    have ht := (lt_div_iff₀ (show 0 < B + 1 by positivity)).mp hd
    nlinarith
  exact (resolvent_apply_sub_norm_le (Us n) U z hbz.1 (hr hz) x).trans_lt
    ((mul_le_mul_of_nonneg_right hbz.2 (norm_nonneg _)).trans_lt hsmall)

/-- Strong resolvent convergence is uniform on every compact subset of the limit resolvent. -/
theorem collectivelyCompact_resolvent_uniform_on_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U)
    (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ z ∈ A, ‖resolvent (Us n) z x - resolvent U z x‖ < ε := by
  apply collectivelyCompact_resolvent_uniform_of_compact_image Us U hs hk A hA hr x
    (hA.image_of_continuousOn ?_) ε hε
  intro z hz
  have hi : ContinuousAt Ring.inverse (algebraMap ℂ (E →L[ℂ] E) z - U) := by
    simpa only [(hr hz).unit_spec] using NormedRing.inverse_continuousAt (hr hz).unit
  have ha : ContinuousAt (fun w : ℂ ↦ algebraMap ℂ (E →L[ℂ] E) w - U) z :=
    (continuous_algebraMap ℂ (E →L[ℂ] E)).continuousAt.sub continuousAt_const
  exact ((ContinuousAt.comp (f := fun w : ℂ ↦ algebraMap ℂ (E →L[ℂ] E) w - U) hi ha).clm_apply continuousAt_const).continuousWithinAt
end PaperN.PartII


