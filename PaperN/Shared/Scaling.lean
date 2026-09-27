import PaperN.Shared.PseudometricComparison

namespace PaperN.Shared
open Set Metric GromovHausdorff
open scoped NNReal
universe u v

/-- Arbitrarily close to optimal correspondences, with no external theorem input. -/
theorem exists_correspondence_distortion (X : Type u) (Y : Type v)
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (r : ℝ) (hr : ghDist X Y < r) :
    ∃ R : Correspondence X Y, R.DistortionLE (2*r) := by
  obtain ⟨f,g,hf,hg,heq⟩ := ghDist_eq_hausdorffDist X Y
  have hfin := hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty f)
    (range_nonempty g) (isCompact_range hf.continuous).isBounded
    (isCompact_range hg.continuous).isBounded
  let R : Correspondence X Y := {
    rel := {p | dist (f p.1) (g p.2) < r}
    left_total := by
      intro x
      obtain ⟨_,⟨y,rfl⟩,hy⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self x) (heq ▸ hr) hfin
      exact ⟨y,hy⟩
    right_total := by
      intro y
      obtain ⟨_,⟨x,rfl⟩,hx⟩ := exists_dist_lt_of_hausdorffDist_lt' (mem_range_self y) (heq ▸ hr) hfin
      exact ⟨x,hx⟩ }
  refine ⟨R, ?_⟩
  intro p q
  have hp : dist (f p.val.1) (g p.val.2) < r := p.property
  have hq : dist (f q.val.1) (g q.val.2) < r := q.property
  rw [← hf.dist_eq, ← hg.dist_eq]
  apply abs_le.mpr
  have h₀ := dist_triangle4 (f p.val.1) (g p.val.2) (g q.val.2) (f q.val.1)
  have h₁ := dist_triangle4 (g p.val.2) (f p.val.1) (f q.val.1) (g q.val.2)
  rw [dist_comm (g q.val.2) (f q.val.1)] at h₀
  rw [dist_comm (g p.val.2) (f p.val.1)] at h₁
  constructor <;> linarith

/-- The sharp scaling estimate, including a=0 and b=0. -/
theorem scaledGH_dist_le (X : Type u) (Y : Type v)
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] (a b : ℝ≥0) :
    dist (scaledGH a X) (scaledGH b Y) ≤
      (a : ℝ) * ghDist X Y + |(a : ℝ)-b| / 2 * diam (univ : Set Y) := by
  have bound (r : ℝ) (hr : ghDist X Y < r) :
      dist (scaledGH a X) (scaledGH b Y) ≤
        (a : ℝ)*r + |(a : ℝ)-b|/2 * diam (univ : Set Y) := by
    obtain ⟨R,hR⟩ := exists_correspondence_distortion X Y r hr
    apply (quotient_ghDist_le R ((ContinuousPseudometric.ofMetric X).scale a)
      ((ContinuousPseudometric.ofMetric Y).scale b)).trans
    have hb : correspondenceError R ((ContinuousPseudometric.ofMetric X).scale a)
        ((ContinuousPseudometric.ofMetric Y).scale b) ≤
        (a : ℝ)*(2*r) + |(a : ℝ)-b| * diam (univ : Set Y) := by
      apply ciSup_le
      intro z
      change |(a : ℝ)*dist z.1.val.1 z.2.val.1 - (b : ℝ)*dist z.1.val.2 z.2.val.2| ≤ _
      calc
        _ = |(a : ℝ)*(dist z.1.val.1 z.2.val.1-dist z.1.val.2 z.2.val.2) +
            ((a : ℝ)-b)*dist z.1.val.2 z.2.val.2| := by congr 1; ring
        _ ≤ |(a : ℝ)*(dist z.1.val.1 z.2.val.1-dist z.1.val.2 z.2.val.2)| +
            |((a : ℝ)-b)*dist z.1.val.2 z.2.val.2| := abs_add_le _ _
        _ = (a : ℝ)*|dist z.1.val.1 z.2.val.1-dist z.1.val.2 z.2.val.2| +
            |(a : ℝ)-b| *dist z.1.val.2 z.2.val.2 := by rw [abs_mul, abs_mul, abs_of_nonneg a.coe_nonneg, abs_dist]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hR z.1 z.2) a.coe_nonneg)
          (mul_le_mul_of_nonneg_left (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)) (abs_nonneg _))
    linarith
  apply le_of_forall_pos_le_add
  intro ε hε
  have hp : 0 < ε / ((a : ℝ)+1) := div_pos hε (by positivity)
  have h := bound (ghDist X Y + ε/((a : ℝ)+1)) (by linarith)
  have he := (div_mul_cancel₀ ε (show (a : ℝ)+1 ≠ 0 by positivity))
  nlinarith
end PaperN.Shared
