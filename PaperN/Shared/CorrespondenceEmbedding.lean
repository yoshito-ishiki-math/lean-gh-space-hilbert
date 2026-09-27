import PaperN.Shared.Correspondence

namespace PaperN.Shared
open Set Metric GromovHausdorff
universe u v

/-- mathlib's approximate gluing realizes each related pair at exactly ε. -/
theorem correspondenceEmbedding_spec : CorrespondenceEmbeddingStatement.{u,v} := by
  intro X Y _ _ _ _ _ _ R ε hε hR
  let m := glueMetricApprox (fun p : R.rel ↦ p.val.1) (fun p : R.rel ↦ p.val.2) ε hε hR
  letI := m
  have he (p : R.rel) : dist (Sum.inl p.val.1) (Sum.inr p.val.2) = ε :=
    glueDist_glued_points _ _ _ p
  refine ⟨m, Isometry.of_dist_eq (fun _ _ ↦ rfl),
    Isometry.of_dist_eq (fun _ _ ↦ rfl), fun p ↦ (he p).le, ?_⟩
  apply hausdorffDist_le_of_mem_dist hε.le
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := R.left_total x
    exact ⟨Sum.inr y, mem_range_self _, (he ⟨(x,y), hy⟩).le⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := R.right_total y
    exact ⟨Sum.inl x, mem_range_self _, by rw [dist_comm]; exact (he ⟨(x,y), hx⟩).le⟩

/-- The distortion upper bound, including zero distortion, implies the sharp GH bound. -/
theorem ghDist_le_half_distortion {X : Type u} {Y : Type v}
    [MetricSpace X] [MetricSpace Y] [Nonempty X] [Nonempty Y] [CompactSpace X] [CompactSpace Y]
    (R : Correspondence X Y) (a : ℝ) (ha : R.DistortionLE a) : ghDist X Y ≤ a / 2 := by
  have ha0 : 0 ≤ a := (abs_nonneg _).trans (ha (Classical.choice inferInstance) (Classical.choice inferInstance))
  apply le_of_forall_pos_le_add
  intro δ hδ
  obtain ⟨m, hl, hr, _, hh⟩ := correspondenceEmbedding_spec X Y R (a / 2 + δ)
    (by linarith) (fun p q ↦ (ha p q).trans (by linarith))
  letI := m
  exact (ghDist_le_hausdorffDist hl hr).trans hh
end PaperN.Shared
