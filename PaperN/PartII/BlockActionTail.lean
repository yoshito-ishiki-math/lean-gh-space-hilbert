import PaperN.PartII.BlockSumSeparable

namespace PaperN.PartII
variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]

/-- Acting on a single block agrees with inserting the acted-on vector. -/
theorem blockSumAction_single (U : ∀ i, B i ≃ₗᵢ[ℝ] B i) (i : I) (x : B i) :
    blockSumAction U (lp.single 1 i x) = lp.single 1 i (U i x) := by
  apply Subtype.ext
  funext j
  change U j (lp.single 1 i x j) = lp.single 1 i (U i x) j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

omit [∀ i, NormedSpace ℝ (B i)] in
/-- The l1 tail has exactly the missing block mass. -/
theorem blockSum_tail_norm (f : lp B 1) (s : Finset I) :
    ‖f - ∑ i ∈ s, lp.single 1 i (f i)‖ = ‖f‖ - ∑ i ∈ s, ‖f i‖ := by
  simpa using lp.norm_compl_sum_single (by norm_num : 0 < (1 : ENNReal).toReal) f s

/-- Two block actions differ by the finite-block error plus twice the original tail. -/
theorem blockSumAction_difference_le (U V : ∀ i, B i ≃ₗᵢ[ℝ] B i)
    (f : lp B 1) (s : Finset I) :
    ‖blockSumAction U f - blockSumAction V f‖ ≤
      (∑ i ∈ s, ‖U i (f i) - V i (f i)‖) +
      2 * ‖f - ∑ i ∈ s, lp.single 1 i (f i)‖ := by
  let g : lp B 1 := ∑ i ∈ s, lp.single 1 i (f i)
  have hf : ‖blockSumAction U g - blockSumAction V g‖ ≤
      ∑ i ∈ s, ‖U i (f i) - V i (f i)‖ := by
    simp only [g, map_sum, blockSumAction_single, ← Finset.sum_sub_distrib, ← lp.single_sub]
    exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦
      lp.norm_single (by norm_num : (0 : ENNReal) < 1) i _)
  have h := norm_sub_le_norm_sub_add_norm_sub (blockSumAction U f) (blockSumAction U g) (blockSumAction V f)
  have h' := norm_sub_le_norm_sub_add_norm_sub (blockSumAction U g) (blockSumAction V g) (blockSumAction V f)
  rw [← map_sub, (blockSumAction U).norm_map] at h
  rw [← map_sub, (blockSumAction V).norm_map, norm_sub_rev g f] at h'
  dsimp [g] at *
  linarith

end PaperN.PartII
