import PaperN.PartII.StrongCompactConvergence
import Mathlib.Topology.ContinuousMap.Compact

namespace PaperN.PartII
open Set Metric Filter
open scoped Topology

/-- Parameter-uniform strong convergence is uniform on compact vector sets
when both operator families have common norm bounds. -/
theorem parameter_strong_uniform_on_compact
    {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → A → E →L[ℂ] E) (U : A → E →L[ℂ] E)
    (hs : ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ a, ‖Us n a x - U a x‖ < ε)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hb : ∀ n a, ‖Us n a‖ ≤ C) (hbu : ∀ a, ‖U a‖ ≤ B)
    (K : Set E) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ a x, x ∈ K → ‖Us n a x - U a x‖ < ε := by
  let D := C + B + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let δ := ε / (3 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨S, hS, hc⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded δ hδ
  have hp : ∀ᶠ n in atTop, ∀ c ∈ S, ∀ a, ‖Us n a c - U a c‖ < ε / 3 := by
    apply hS.eventually_all.mpr
    intro c _
    exact hs c (ε / 3) (by positivity)
  filter_upwards [hp] with n hn
  intro a x hx
  obtain ⟨c, hcs, hxc⟩ : ∃ c ∈ S, dist x c < δ := by
    simpa only [mem_iUnion, mem_ball, exists_prop] using hc hx
  have h1 : ‖Us n a x - Us n a c‖ ≤ C * dist x c := by
    rw [← map_sub, dist_eq_norm]
    exact ((Us n a).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hb n a) (norm_nonneg _))
  have h2 : ‖U a c - U a x‖ ≤ B * dist x c := by
    rw [← map_sub, dist_comm x c, dist_eq_norm]
    exact ((U a).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbu a) (norm_nonneg _))
  have h3 : ‖Us n a x - U a x‖ ≤ ‖Us n a x - Us n a c‖ + ‖Us n a c - U a c‖ + ‖U a c - U a x‖ := by
    calc
      _ = ‖(Us n a x - Us n a c) + (Us n a c - U a c) + (U a c - U a x)‖ := by congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hm : D * dist x c < ε / 3 := by
    have ht := mul_lt_mul_of_pos_left hxc hD
    have hd : D * δ = ε / 3 := by dsimp [δ]; field_simp
    rwa [hd] at ht
  have hn' := hn c hcs a
  have hd0 := dist_nonneg (x := x) (y := c)
  dsimp [D] at hm
  linarith


/-- Common compact images for a compact parameter family with uniform strong convergence. -/
theorem parameter_strong_compact_images_contained
    {A E : Type*} [TopologicalSpace A] [CompactSpace A]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Us : ℕ → A → E →L[ℂ] E) (U : A → E →L[ℂ] E)
    (hcs : ∀ n, Continuous (Us n)) (hcu : Continuous U)
    (hs : ∀ x ε, 0 < ε → ∀ᶠ n in atTop, ∀ a, ‖Us n a x - U a x‖ < ε)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hb : ∀ n a, ‖Us n a‖ ≤ C) (hbu : ∀ a, ‖U a‖ ≤ B)
    (K : Set E) (hK : IsCompact K) :
    ∃ L : Set E, IsCompact L ∧ ∀ n a x, x ∈ K → Us n a x ∈ L := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fs : ℕ → C(A × K,E) := fun n ↦ ⟨fun p ↦ Us n p.1 p.2,
    ((hcs n).comp continuous_fst).clm_apply (continuous_subtype_val.comp continuous_snd)⟩
  let f : C(A × K,E) := ⟨fun p ↦ U p.1 p.2,
    (hcu.comp continuous_fst).clm_apply (continuous_subtype_val.comp continuous_snd)⟩
  have hf : Tendsto fs atTop (𝓝 f) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp
      (parameter_strong_uniform_on_compact Us U hs C B hC hB hb hbu K hK (ε/2) (by positivity))
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm]
    have hh : ‖fs n-f‖ ≤ ε/2 := (ContinuousMap.norm_le _ (by positivity)).mpr
      (fun p ↦ (hN n hn p.1 p.2 p.2.property).le)
    exact hh.trans_lt (by linarith)
  let S := insert f (range fs)
  have hS : IsCompact S := hf.isCompact_insert_range
  let ev : C(A × K,E) × (A × K) → E := fun p ↦ p.1 p.2
  have hev : Continuous ev := continuous_eval
  refine ⟨ev '' (S ×ˢ (univ : Set (A × K))), (hS.prod isCompact_univ).image hev, ?_⟩
  intro n a x hx
  exact ⟨(fs n, (a, ⟨x,hx⟩)), ⟨mem_insert_of_mem _ ⟨n,rfl⟩, mem_univ _⟩, rfl⟩
end PaperN.PartII

