import PaperN.PartI.CommonRealization
import PaperN.Shared.Correspondence
import Mathlib.Analysis.SpecificLimits.Basic

namespace PaperN.PartI.CommonRealization
open PaperN.Shared Set Metric Filter
open scoped Topology

/-- Hausdorff convergence in a compact common realization supplies actual
correspondences with both vanishing ambient displacement and distortion. -/
theorem exists_correspondences_tendsto
    {Xs : ℕ → MeasuredCompact} {X : MeasuredCompact}
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges) :
    ∃ R : ∀ k, Correspondence (Xs k) X,
      Tendsto (fun k ↦ ⨆ z : (R k).rel,
        dist (C.seqMap k z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) ∧
      Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0) := by
  let r := fun k ↦ hausdorffDist (range (C.seqMap k)) (range C.limitMap) + 1 / ((k : ℝ) + 1)
  have hr k : hausdorffDist (range (C.seqMap k)) (range C.limitMap) < r k := by
    dsimp [r]
    exact lt_add_of_pos_right _ (by positivity)
  have ht : Tendsto r atTop (𝓝 0) := by
    simpa only [add_zero] using hH.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hfin k := hausdorffEDist_ne_top_of_nonempty_of_bounded
    (range_nonempty (C.seqMap k)) (range_nonempty C.limitMap)
    (isCompact_range (C.seq_isometry k).continuous).isBounded
    (isCompact_range C.limit_isometry.continuous).isBounded
  let R : ∀ k, Correspondence (Xs k) X := fun k ↦ {
    rel := {p | dist (C.seqMap k p.1) (C.limitMap p.2) < r k}
    left_total := by
      intro x
      obtain ⟨_, ⟨y, rfl⟩, hy⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self x) (hr k) (hfin k)
      exact ⟨y, hy⟩
    right_total := by
      intro y
      obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) (hr k) (hfin k)
      exact ⟨x, hx⟩ }
  letI (k : ℕ) : Nonempty (R k).rel := by
    obtain ⟨y, hy⟩ := (R k).left_total (Classical.choice (Xs k).nonempty)
    exact ⟨⟨(_, y), hy⟩⟩
  refine ⟨R, ?_, ?_⟩
  · exact squeeze_zero (fun _ ↦ Real.iSup_nonneg (fun _ ↦ dist_nonneg))
      (fun k ↦ ciSup_le (fun z ↦ z.property.le)) ht
  · apply squeeze_zero (fun _ ↦ Real.iSup_nonneg (fun _ ↦ abs_nonneg _)) _
      (show Tendsto (fun k ↦ 2 * r k) atTop (𝓝 0) by simpa using ht.const_mul 2)
    intro k
    apply ciSup_le
    intro z
    have hp : dist (C.seqMap k z.1.val.1) (C.limitMap z.1.val.2) < r k := z.1.property
    have hq : dist (C.seqMap k z.2.val.1) (C.limitMap z.2.val.2) < r k := z.2.property
    rw [← (C.seq_isometry k).dist_eq, ← C.limit_isometry.dist_eq]
    have h₀ := dist_triangle4 (C.seqMap k z.1.val.1) (C.limitMap z.1.val.2)
      (C.limitMap z.2.val.2) (C.seqMap k z.2.val.1)
    have h₁ := dist_triangle4 (C.limitMap z.1.val.2) (C.seqMap k z.1.val.1)
      (C.seqMap k z.2.val.1) (C.limitMap z.2.val.2)
    rw [dist_comm (C.limitMap z.2.val.2) (C.seqMap k z.2.val.1)] at h₀
    rw [dist_comm (C.limitMap z.1.val.2) (C.seqMap k z.1.val.1)] at h₁
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end PaperN.PartI.CommonRealization
