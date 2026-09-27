import PaperN.PartII.BlockSumSeparable
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

namespace PaperN.PartII
open Set Metric
open scoped Topology

/-- A real normed space is connected, including the zero space. -/
theorem normedSpace_connected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsConnected (Set.univ : Set E) :=
  (convex_univ : Convex ℝ (Set.univ : Set E)).isConnected Set.univ_nonempty

/-- Any two points of an open ball lie in a compact connected subset of that ball. -/
theorem ball_contains_continuum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (r : ℝ) {x y : E} (hx : x ∈ ball a r) (hy : y ∈ ball a r) :
    ∃ K : Set E, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ K ⊆ ball a r := by
  refine ⟨segment ℝ x y, ?_, ?_, left_mem_segment ℝ x y, right_mem_segment ℝ x y,
    (convex_ball a r).segment_subset hx hy⟩
  · rw [← Path.range_segment]
    exact isCompact_range (Path.segment x y).continuous
  · exact (convex_segment x y).isConnected ⟨x, left_mem_segment ℝ x y⟩

/-- Explicit local continuum-connectedness in the neighbourhood formulation. -/
theorem normedSpace_local_continua {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (U : Set E) (hU : U ∈ nhds a) :
    ∃ V : Set E, IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, ∃ K : Set E,
        IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ K ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨ball a r, isOpen_ball, mem_ball_self hr, hsub, ?_⟩
  intro x hx y hy
  obtain ⟨K, hc, hn, hX, hY, hK⟩ := ball_contains_continuum a r hx hy
  exact ⟨K, hc, hn, hX, hY, hK.trans hsub⟩

/-- The actual Banach block space satisfies the local continuum hypothesis. -/
theorem sphereBlockSum_local_continua (n : ℕ → ℕ) (a : SphereBlockSum n)
    (U : Set (SphereBlockSum n)) (hU : U ∈ nhds a) :
    ∃ V : Set (SphereBlockSum n), IsOpen V ∧ a ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, ∃ K : Set (SphereBlockSum n),
        IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ y ∈ K ∧ K ⊆ U :=
  normedSpace_local_continua a U hU

end PaperN.PartII
