import PaperN.PartII.StrongCompactConvergence
import Mathlib.Topology.ContinuousMap.Compact

namespace PaperN.PartII
open Set Filter Metric
open scoped Topology

/-- A uniformly bounded strongly convergent sequence maps a compact set into
one common compact set, including the limit image. -/
theorem strong_compact_images_contained
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖Us n‖ ≤ C)
    (K : Set E) (hK : IsCompact K) :
    ∃ L : Set E, IsCompact L ∧ (∀ n x, x ∈ K → Us n x ∈ L) ∧
      ∀ x ∈ K, U x ∈ L := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fs : ℕ → C(K,E) := fun n ↦ ⟨fun x ↦ Us n x, (Us n).continuous.comp continuous_subtype_val⟩
  let f : C(K,E) := ⟨fun x ↦ U x, U.continuous.comp continuous_subtype_val⟩
  have hf : Tendsto fs atTop (𝓝 f) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (strong_eventually_uniform_on_compact Us U hs C hC hb K hK (ε/2) (by positivity))
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    have hbound : ‖fs n-f‖ ≤ ε/2 := (ContinuousMap.norm_le _ (by positivity)).mpr
      (fun x ↦ (hN n hn x x.property).le)
    exact hbound.trans_lt (by linarith)
  let A := insert f (range fs)
  have hA : IsCompact A := hf.isCompact_insert_range
  let ev : C(K,E) × K → E := fun p ↦ p.1 p.2
  have hev : Continuous ev := continuous_eval
  refine ⟨ev '' (A ×ˢ (univ : Set K)), (hA.prod isCompact_univ).image hev, ?_, ?_⟩
  · intro n x hx
    exact ⟨(fs n, ⟨x,hx⟩), ⟨mem_insert_of_mem _ ⟨n,rfl⟩, mem_univ _⟩, rfl⟩
  · intro x hx
    exact ⟨(f, ⟨x,hx⟩), ⟨mem_insert _ _, mem_univ _⟩, rfl⟩

/-- Left composition by a bounded strongly convergent sequence preserves
collective compactness. -/
theorem collectivelyCompact_comp_of_strong
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖Us n‖ ≤ C)
    (Ts : ℕ → E →L[ℂ] E)
    (ht : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Ts n x ∈ K) :
    ∃ L : Set E, IsCompact L ∧ ∀ n x, ‖x‖ ≤ 1 → (Us n).comp (Ts n) x ∈ L := by
  obtain ⟨K,hK,hmem⟩ := ht
  obtain ⟨L,hL,hm,_⟩ := strong_compact_images_contained Us U hs C hC hb K hK
  exact ⟨L,hL,fun n x hx ↦ hm n (Ts n x) (hmem n x hx)⟩
end PaperN.PartII

