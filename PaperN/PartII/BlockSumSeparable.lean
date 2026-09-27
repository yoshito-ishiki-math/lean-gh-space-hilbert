import PaperN.PartII.BlockSum
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

namespace PaperN.PartII
open Set TopologicalSpace
open scoped Topology
variable {I : Type*} [DecidableEq I] {B : I → Type*} [∀ i, NormedAddCommGroup (B i)]
    [∀ i, NormedSpace ℝ (B i)]

/-- Finite block synthesis is continuous for the product topology on the blocks. -/
theorem continuous_blockSum_finite (s : Finset I) :
    Continuous (fun f : ∀ i, B i ↦ ∑ i ∈ s, lp.single (1 : ENNReal) i (f i)) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := B) (p := 1) i).continuous.comp (continuous_apply i)

omit [∀ i, NormedSpace ℝ (B i)] in
/-- Finite block vectors are dense in the l1 sum. -/
theorem dense_blockSum_finite :
    Dense (⋃ s : Finset I, Set.range (fun f : ∀ i, B i ↦ ∑ i ∈ s, lp.single (1 : ENNReal) i (f i))) := by
  intro f
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single (by simp : (1 : ENNReal) ≠ ⊤) f)
  apply Filter.Eventually.of_forall
  intro s
  apply subset_closure
  exact mem_iUnion.mpr ⟨s, mem_range.mpr ⟨fun i ↦ f i, rfl⟩⟩

/-- A countable l1 sum of separable real normed spaces is separable. -/
theorem blockSum_separable [Countable I] [∀ i, SeparableSpace (B i)] :
    SeparableSpace (lp B 1) := by
  have hs : IsSeparable (⋃ s : Finset I, Set.range
      (fun f : ∀ i, B i ↦ ∑ i ∈ s, lp.single (1 : ENNReal) i (f i))) :=
    isSeparable_iUnion.mpr (fun s ↦ isSeparable_range (continuous_blockSum_finite s))
  have hc := hs.closure
  rw [dense_blockSum_finite.closure_eq] at hc
  exact isSeparable_univ_iff.mp hc

/-- The sphere-function Banach block space in the global construction is separable. -/
theorem sphereBlockSum_separable (n : ℕ → ℕ) : SeparableSpace (SphereBlockSum n) :=
  blockSum_separable

end PaperN.PartII
