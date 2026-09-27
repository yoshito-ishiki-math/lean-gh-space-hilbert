import PaperN.PartII.ModelFeatureRepresentatives

namespace PaperN.PartII
open PaperN.Shared TopologicalSpace Filter
open scoped Topology

/-- A uniform bound along a correspondence controls the Hausdorff distance of feature images. -/
theorem featureImage_dist_le {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y] [MetricSpace E]
    (f : X → E) (g : Y → E) (hf : Continuous f) (hg : Continuous g)
    (R : Correspondence X Y) (r : ℝ) (h : ∀ z : R.rel, dist (f z.val.1) (g z.val.2) ≤ r) :
    dist (featureImage f hf) (featureImage g hg) ≤ r := by
  rw [Metric.NonemptyCompacts.dist_eq]
  have hr : 0 ≤ r := dist_nonneg.trans (h (Classical.choice inferInstance))
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := R.left_total x
    exact ⟨g y, Set.mem_range_self y, h ⟨(x,y), hy⟩⟩
  · rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := R.right_total y
    exact ⟨f x, Set.mem_range_self x, by simpa only [dist_comm] using h ⟨(x,y), hx⟩⟩

/-- Variation of both weights and block vectors has a finite explicit error bound. -/
theorem finiteBlockFeature_dist_le_variable {I : Type*} [DecidableEq I] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (s : Finset I) (w v : I → ℝ) (f g : ∀ i, B i) :
    dist (finiteBlockFeature s w f) (finiteBlockFeature s v g) ≤
      ∑ i ∈ s, (|w i| * dist (f i) (g i) + |w i - v i| * ‖g i‖) := by
  rw [dist_eq_norm]
  have he : finiteBlockFeature s w f - finiteBlockFeature s v g =
      ∑ i ∈ s, lp.single 1 i (w i • f i - v i • g i) := by
    simp only [finiteBlockFeature, ← Finset.sum_sub_distrib, lp.single_sub]
  rw [he]
  have hn := lp.norm_sum_single (by norm_num : 0 < (1 : ENNReal).toReal)
    (fun i ↦ w i • f i - v i • g i) s
  simp only [ENNReal.toReal_one, Real.rpow_one] at hn
  rw [hn]
  apply Finset.sum_le_sum
  intro i _
  have hi : w i • f i - v i • g i = w i • (f i - g i) + (w i - v i) • g i := by
    simp only [smul_sub, sub_smul]
    abel
  rw [hi]
  simpa only [norm_smul, Real.norm_eq_abs, dist_eq_norm] using
    norm_add_le (w i • (f i - g i)) ((w i - v i) • g i)

/-- The explicit finite-block error estimate passes to compact images on different carriers. -/
theorem finiteFeatureImage_dist_le {I X Y : Type*} [DecidableEq I]
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (s : Finset I) (w v : I → ℝ) (f : ∀ i, X → B i) (g : ∀ i, Y → B i)
    (hf : ∀ i ∈ s, Continuous (f i)) (hg : ∀ i ∈ s, Continuous (g i))
    (R : Correspondence X Y) (e C : I → ℝ)
    (he : ∀ i ∈ s, ∀ z : R.rel, dist (f i z.val.1) (g i z.val.2) ≤ e i)
    (hC : ∀ i ∈ s, ∀ y, ‖g i y‖ ≤ C i) :
    dist (finiteFeatureImage s w f hf) (finiteFeatureImage s v g hg) ≤
      ∑ i ∈ s, (|w i| * e i + |w i - v i| * C i) := by
  apply featureImage_dist_le _ _ _ _ R
  intro z
  apply (finiteBlockFeature_dist_le_variable s w v _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  exact add_le_add (mul_le_mul_of_nonneg_left (he i hi z) (abs_nonneg _))
    (mul_le_mul_of_nonneg_left (hC i hi _) (abs_nonneg _))

/-- Converging weights and uniform block errors imply convergence of compact images,
even when the source carriers vary. -/
theorem finiteFeatureImage_tendsto {I Y : Type*} [DecidableEq I]
    (X : ℕ → Type*) [∀ k, TopologicalSpace (X k)] [TopologicalSpace Y]
    [∀ k, CompactSpace (X k)] [CompactSpace Y]
    [∀ k, Nonempty (X k)] [Nonempty Y] {B : I → Type*}
    [∀ i, NormedAddCommGroup (B i)] [∀ i, NormedSpace ℝ (B i)]
    (s : Finset I) (w : ℕ → I → ℝ) (v : I → ℝ)
    (f : ∀ k i, X k → B i) (g : ∀ i, Y → B i)
    (hf : ∀ k i, i ∈ s → Continuous (f k i)) (hg : ∀ i ∈ s, Continuous (g i))
    (R : ∀ k, Correspondence (X k) Y) (e : ℕ → I → ℝ) (C : I → ℝ)
    (he : ∀ k i, i ∈ s → ∀ z : (R k).rel,
      dist (f k i z.val.1) (g i z.val.2) ≤ e k i)
    (hC : ∀ i ∈ s, ∀ y, ‖g i y‖ ≤ C i)
    (hw : ∀ i ∈ s, Tendsto (fun k ↦ w k i) atTop (𝓝 (v i)))
    (hε : ∀ i ∈ s, Tendsto (fun k ↦ e k i) atTop (𝓝 0)) :
    Tendsto (fun k ↦ finiteFeatureImage s (w k) (f k) (hf k)) atTop
      (𝓝 (finiteFeatureImage s v g hg)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg)
    (fun k ↦ finiteFeatureImage_dist_le s (w k) v (f k) g (hf k) hg (R k) (e k) C (he k) hC)
  have h : Tendsto (fun k ↦ ∑ i ∈ s, (|w k i| * e k i + |w k i - v i| * C i))
      atTop (𝓝 (∑ i ∈ s, (|v i| * 0 + |v i - v i| * C i))) := by
    apply tendsto_finsetSum
    intro i hi
    exact ((hw i hi).abs.mul (hε i hi)).add
      (((hw i hi).sub tendsto_const_nhds).abs.mul_const (C i))
  simpa using h

end PaperN.PartII
