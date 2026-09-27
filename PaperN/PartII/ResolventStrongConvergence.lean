import PaperN.PartII.CollectivelyCompactInverseConvergence
import PaperN.PartII.PointwiseResolventStability

namespace PaperN.PartII
open Filter Set
open scoped Topology

/-- A lower bound bounds the norm of the inverse. -/
theorem inverse_norm_le_of_lowerBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (ht : IsUnit T) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x, ‖x‖ ≤ B * ‖T x‖) : ‖Ring.inverse T‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro y
  have he : T (Ring.inverse T y) = y :=
    congrArg (fun A : E →L[ℂ] E ↦ A y) (Ring.mul_inverse_cancel T ht)
  simpa only [he] using hb (Ring.inverse T y)

/-- Inverse norms are eventually uniformly bounded for collectively compact perturbations. -/
theorem collectivelyCompact_eventually_inverse_norm_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E) (hu : IsUnit U)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop, IsUnit (Us n) ∧ ‖Ring.inverse (Us n)‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := collectivelyCompact_eventually_lowerBound Us U hu hs hk
  refine ⟨B, hB, ?_⟩
  filter_upwards [hb, collectivelyCompact_eventually_isUnit Us U hu hs hk] with n hn hi
  exact ⟨hi, inverse_norm_le_of_lowerBound (Us n) hi B hB hn⟩

/-- At a fixed limit-resolvent point, resolvents converge strongly on moving vectors. -/
theorem collectivelyCompact_resolvent_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (z : ℂ) (hz : z ∈ resolventSet ℂ U)
    (ys : ℕ → E) (y : E) (hy : Tendsto ys atTop (𝓝 y)) :
    Tendsto (fun n ↦ resolvent (Us n) z (ys n)) atTop (𝓝 (resolvent U z y)) := by
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
  exact collectivelyCompact_inverse_tendsto (fun n ↦ A - Us n) (A - U) hz hstrong hcompact ys y hy
end PaperN.PartII
