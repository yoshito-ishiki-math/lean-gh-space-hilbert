import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Isometry

namespace PaperN.PartI
open Set Filter
open scoped Topology BoundedContinuousFunction

/-- Isometric embeddings between compact metric spaces form a compact set
in the uniform metric on bounded continuous maps. -/
theorem isCompact_isometry_embeddings {X Z : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Z] [CompactSpace Z] : IsCompact {f : X →ᵇ Z | Isometry f} := by
  apply BoundedContinuousFunction.arzela_ascoli₁
  · have he : {f : X →ᵇ Z | Isometry f} =
        ⋂ x : X, ⋂ y : X, {f : X →ᵇ Z | dist (f x) (f y) = dist x y} := by
      ext f
      simp only [mem_setOf_eq, mem_iInter]
      exact ⟨fun h x y ↦ h.dist_eq x y, Isometry.of_dist_eq⟩
    rw [he]
    exact isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
      isClosed_eq ((continuous_eval_const x).dist (continuous_eval_const y)) continuous_const
  · exact (LipschitzWith.uniformEquicontinuous
      (fun f : {f : X →ᵇ Z | Isometry f} ↦ (f.val : X → Z)) 1
      (fun f ↦ f.property.lipschitz)).equicontinuous

/-- An isometric embedding sequence has a uniformly convergent isometric subsequence. -/
theorem isometry_embeddings_subsequence {X Z : Type*} [MetricSpace X] [CompactSpace X]
    [MetricSpace Z] [CompactSpace Z] (f : ℕ → X →ᵇ Z) (hf : ∀ n, Isometry (f n)) :
    ∃ (g : X →ᵇ Z) (φ : ℕ → ℕ), Isometry g ∧ StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 g) := by
  obtain ⟨g, hg, φ, hφ, ht⟩ := isCompact_isometry_embeddings.isSeqCompact hf
  exact ⟨g, φ, hg, hφ, ht⟩
end PaperN.PartI
