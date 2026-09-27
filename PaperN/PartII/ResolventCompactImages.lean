import PaperN.PartII.ParameterStrongCompactConvergence
import PaperN.PartII.InverseDifferenceBound
import PaperN.PartII.ResolventIntegrability

namespace PaperN.PartII
open Set Filter
open scoped Topology

/-- Compact vector images for resolvents on a common compact parameter set,
assuming a common bound and contour avoidance for the whole indexed family. -/
theorem collectivelyCompact_resolvent_compact_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U)
    (hrs : ∀ n, A ⊆ resolventSet ℂ (Us n))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n z, z ∈ A → ‖resolvent (Us n) z‖ ≤ C)
    (K : Set E) (hK : IsCompact K) :
    ∃ L : Set E, IsCompact L ∧ ∀ n z, z ∈ A → ∀ x ∈ K, resolvent (Us n) (z : ℂ) x ∈ L := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  have hcont (T : E →L[ℂ] E) (ht : A ⊆ resolventSet ℂ T) :
      Continuous (fun z : A ↦ resolvent T (z : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (spectrum.hasDerivAt_resolvent_const_left (ht z.property)).continuousAt.comp
      continuousAt_subtype_val
  have hlim := hcont U hr
  have hcompact := isCompact_univ.image hlim
  obtain ⟨B,hB,hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  have hunif : ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ z : A,
      ‖resolvent (Us n) (z : ℂ) x - resolvent U (z : ℂ) x‖ < ε := by
    intro x ε hε
    filter_upwards [collectivelyCompact_resolvent_uniform_on_compact Us U hs hk A hA hr x ε hε]
      with n hn
    exact fun z ↦ hn z z.property
  obtain ⟨L,hL,hm⟩ := parameter_strong_compact_images_contained
    (fun n (z : A) ↦ resolvent (Us n) (z : ℂ)) (fun z : A ↦ resolvent U (z : ℂ))
    (fun n ↦ hcont (Us n) (hrs n)) hlim hunif C B hC hB.le
    (fun n z ↦ hb n z z.property) (fun z ↦ hbound _ ⟨z,mem_univ _,rfl⟩) K hK
  exact ⟨L,hL,fun n z hz x hx ↦ hm n ⟨z,hz⟩ x hx⟩

/-- No initial contour avoidance is needed: a sufficiently late resolvent tail
maps compact vector sets into one common compact set over all parameters. -/
theorem collectivelyCompact_resolvent_tail_compact_images
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (A : Set ℂ) (hA : IsCompact A) (hr : A ⊆ resolventSet ℂ U)
    (K : Set E) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ L : Set E, IsCompact L ∧
      ∀ n, N ≤ n → ∀ z ∈ A, ∀ x ∈ K, resolvent (Us n) z x ∈ L := by
  obtain ⟨C,hC,hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound Us U hs hk A hA hr
  obtain ⟨N,hN⟩ := eventually_atTop.mp hb
  have hs' : ∀ x, Tendsto (fun n ↦ Us (n+N) x) atTop (𝓝 (U x)) :=
    fun x ↦ (hs x).comp (tendsto_add_atTop_nat N)
  have hk' : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us (n+N) x - U x ∈ K := by
    obtain ⟨J,hJ,hm⟩ := hk
    exact ⟨J,hJ,fun n x hx ↦ hm (n+N) x hx⟩
  obtain ⟨L,hL,hm⟩ := collectivelyCompact_resolvent_compact_images
    (fun n ↦ Us (n+N)) U hs' hk' A hA hr
    (fun n z hz ↦ (hN (n+N) (by omega) z hz).1) C hC
    (fun n z hz ↦ (hN (n+N) (by omega) z hz).2) K hK
  refine ⟨N,L,hL,fun n hn z hz x hx ↦ ?_⟩
  simpa only [Nat.sub_add_cancel hn] using hm (n-N) z hz x hx
end PaperN.PartII

