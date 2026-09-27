import Mathlib.Topology.EMetricSpace.Paracompact

import PaperN.PartII.VariableErrorLocalModel
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Compactness.Lindelof

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff Set

/-- A nonempty open cover of a Lindelof normal paracompact space admits a
countably indexed subordinate partition, with closed supports inside the cover. -/
theorem exists_countable_subordinate_partition
    {X I : Type*} [TopologicalSpace X] [LindelofSpace X] [NormalSpace X]
    [ParacompactSpace X] [Nonempty I] (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = univ) :
    ∃ a : ℕ → I, ∃ ρ : PartitionOfUnity ℕ X,
      ρ.IsSubordinate (fun n ↦ U (a n)) := by
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover U ho (by rw [hcover])
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun n ↦ U (a n)) (fun n ↦ ho (a n)) ha
  exact ⟨a, ρ, hρ⟩

/-- Near each point only finitely many blocks occur, all their domains contain
the same neighborhood, and their weights sum to one there. -/
theorem partition_finite_common_neighborhood
    {X I : Type*} [TopologicalSpace X] (ρ : PartitionOfUnity I X)
    (U : I → Set X) (ho : ∀ i, IsOpen (U i)) (hρ : ρ.IsSubordinate U) (x : X) :
    ∃ J : Finset I, ∃ V ∈ nhds x,
      V ⊆ ⋂ i ∈ J, U i ∧
      ∀ y ∈ V, Function.support (fun i ↦ ρ i y) ⊆ J ∧ ∑ i ∈ J, ρ i y = 1 := by
  obtain ⟨J, V, hV, hsub, hs⟩ := ρ.exists_finset_nhds_support_subset hρ ho x
  refine ⟨J, V, hV, hsub, fun y hy ↦ ⟨hs y hy, ?_⟩⟩
  rw [← finsum_eq_sum_of_support_subset _ (hs y hy)]
  exact ρ.sum_eq_one (Set.mem_univ y)

namespace AmbientKernel
/-- Local models for a positive continuous error control admit a countable
subordinate partition of unity on the whole GH space. -/
theorem exists_localModel_partition
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (ε : GHSpace → ℝ) (hε : Continuous ε) (hpos : ∀ q, 0 < ε q) :
    ∃ a : ℕ → GHSpace,
    ∃ M : ∀ n, LocalModel (ghRepresentative (a n)) (ε (a n)),
    ∃ ρ : PartitionOfUnity ℕ GHSpace,
      ρ.IsSubordinate (fun n ↦ (M n).domain) ∧
      (∀ n, Continuous (M n).ghMap) ∧
      (∀ n q, q ∈ (M n).domain → (M n).error q < ε q) := by
  obtain ⟨M, ho, hcover, _, hc, he⟩ :=
    exists_variable_error_model_cover hm hp hs hg hk   hf   ε hε hpos
  obtain ⟨a, ρ, hρ⟩ := exists_countable_subordinate_partition (fun q ↦ (M q).domain) ho hcover
  exact ⟨a, fun n ↦ M (a n), ρ, hρ, fun n ↦ hc (a n), fun n ↦ he (a n)⟩

end AmbientKernel
end PaperN.PartII
