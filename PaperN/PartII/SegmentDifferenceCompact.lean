import PaperN.PartII.CollectivelyCompactIntegral
import PaperN.PartII.ResolventDifferenceCompact

namespace PaperN.PartII
open Set Filter
open scoped Topology

/-- Strong convergence and collectively compact operator differences imply
collective compactness of the edge integral differences on a late tail. -/
theorem collectivelyCompact_segmentResolvent_difference_tail
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Us : ℕ → E →L[ℂ] E) (U : E →L[ℂ] E)
    (hs : ∀ x, Tendsto (fun n ↦ Us n x) atTop (𝓝 (U x)))
    (hk : ∃ K : Set E, IsCompact K ∧ ∀ n x, ‖x‖ ≤ 1 → Us n x - U x ∈ K)
    (a b : ℂ)
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, segmentParameter a b t ∈ resolventSet ℂ U) :
    ∃ N : ℕ, ∃ L : Set E, IsCompact L ∧ ∀ n, N ≤ n → ∀ x, ‖x‖ ≤ 1 →
      segmentResolvent (Us n) a b x - segmentResolvent U a b x ∈ L := by
  let A := segmentParameter a b '' Icc (0 : ℝ) 1
  have hA : IsCompact A := isCompact_Icc.image (by unfold segmentParameter; fun_prop)
  have hAr : A ⊆ resolventSet ℂ U := by
    rintro z ⟨t,ht,rfl⟩
    exact hr t ht
  obtain ⟨N,K,hK,hm⟩ := collectivelyCompact_resolvent_difference_tail Us U hs hk A hA hAr
  obtain ⟨B,hB,hb⟩ := collectivelyCompact_eventually_compact_resolvent_bound Us U hs hk A hA hAr
  obtain ⟨M,hM⟩ := eventually_atTop.mp hb
  let R := max N M
  have hnr (n : ℕ) : N ≤ n+R := by dsimp [R]; omega
  have hmr (n : ℕ) : M ≤ n+R := by dsimp [R]; omega
  obtain ⟨L,hL,hl⟩ := collectivelyCompact_segmentResolvent_difference
    (fun n ↦ Us (n+R)) U a b
    (fun n t ht ↦ (hM (n+R) (hmr n) _ ⟨t,ht,rfl⟩).1) hr
    ⟨K,hK,fun n t ht x hx ↦ hm (n+R) (hnr n) _ ⟨t,ht,rfl⟩ x hx⟩
  refine ⟨R,L,hL,fun n hn x hx ↦ ?_⟩
  simpa only [Nat.sub_add_cancel hn] using hl (n-R) x hx
end PaperN.PartII
