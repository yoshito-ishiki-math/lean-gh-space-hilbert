import PaperN.PartII.SquaredErrorInvertibility

namespace PaperN.PartII
open Filter Set
open scoped Topology

/-- Every fixed point of the limit resolvent eventually stays in the resolvent. -/
theorem collectivelyCompact_eventually_mem_resolvent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (z : ℂ) (hz : z ∈ resolventSet ℂ U) :
    ∀ᶠ n in atTop, z ∈ resolventSet ℂ (Us n) := by
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
    simp only [ContinuousLinearMap.sub_apply]
    abel
  exact collectivelyCompact_eventually_isUnit (fun n ↦ A - Us n) (A - U) hz hstrong hcompact

/-- Finite subsets of the limit resolvent admit one common eventual index. -/
theorem collectivelyCompact_eventually_finite_resolvent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : A.Finite) (hr : A ⊆ resolventSet ℂ U) :
    ∀ᶠ n in atTop, A ⊆ resolventSet ℂ (Us n) :=
  hA.eventually_all.mpr (fun z hz ↦ collectivelyCompact_eventually_mem_resolvent Us U hs hk z (hr hz))
end PaperN.PartII
