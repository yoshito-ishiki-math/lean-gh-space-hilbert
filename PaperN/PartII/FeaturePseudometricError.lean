import PaperN.PartII.GlobalModelError

namespace PaperN.PartII
open PaperN.Shared Filter
open scoped Topology

/-- Pointwise feature error controls the induced pseudometric correspondence error. -/
theorem feature_pseudometric_error_le {X Y E : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X] [MetricSpace E]
    (R : Correspondence X Y) (d : ContinuousPseudometric X) (c : ContinuousPseudometric Y)
    (f : X → E) (g : Y → E)
    (hf : ∀ x y, dist (f x) (f y) = d x y)
    (hg : ∀ x y, dist (g x) (g y) = c x y)
    (r : ℝ) (h : ∀ z : R.rel, dist (f z.val.1) (g z.val.2) ≤ r) :
    correspondenceError R d c ≤ 2 * r := by
  apply ciSup_le
  intro z
  rw [← hf, ← hg, ← Real.dist_eq]
  exact (dist_dist_dist_le _ _ _ _).trans (by linarith [h z.1, h z.2])

/-- Uniform metric errors differ by at most twice the feature error plus the
original-metric correspondence distortion. -/
theorem feature_uniform_error_comparison {X Y E : Type*}
    [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
    [Nonempty X] [Nonempty Y] [MetricSpace E]
    (R : Correspondence X Y) (d : ContinuousPseudometric X) (c : ContinuousPseudometric Y)
    (f : X → E) (g : Y → E)
    (hf : ∀ x y, dist (f x) (f y) = d x y)
    (hg : ∀ x y, dist (g x) (g y) = c x y)
    (r : ℝ) (h : ∀ z : R.rel, dist (f z.val.1) (g z.val.2) ≤ r) :
    |‖(ContinuousPseudometric.ofMetric X).kernel - d.kernel‖ -
      ‖(ContinuousPseudometric.ofMetric Y).kernel - c.kernel‖| ≤ 2*r + R.distortion := by
  rw [norm_sub_rev (ContinuousPseudometric.ofMetric X).kernel,
    norm_sub_rev (ContinuousPseudometric.ofMetric Y).kernel,
    ← uniform_metric_error_eq_norm, ← uniform_metric_error_eq_norm]
  exact (uniform_metric_error_comparison R d c).trans
    (add_le_add (feature_pseudometric_error_le R d c f g hf hg r h) le_rfl)

/-- Vanishing feature errors and correspondence distortions yield convergence
of the actual uniform metric errors on varying carriers. -/
theorem feature_uniform_error_tendsto {Y E : Type*} (X : ℕ → Type*)
    [∀ k, MetricSpace (X k)] [MetricSpace Y] [∀ k, CompactSpace (X k)] [CompactSpace Y]
    [∀ k, Nonempty (X k)] [Nonempty Y] [MetricSpace E]
    (R : ∀ k, Correspondence (X k) Y)
    (ds : ∀ k, ContinuousPseudometric (X k)) (d : ContinuousPseudometric Y)
    (f : ∀ k, X k → E) (g : Y → E)
    (hf : ∀ k x y, dist (f k x) (f k y) = ds k x y)
    (hg : ∀ x y, dist (g x) (g y) = d x y)
    (r : ℕ → ℝ) (hr : ∀ k (z : (R k).rel), dist (f k z.val.1) (g z.val.2) ≤ r k)
    (he : Tendsto r atTop (𝓝 0))
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ‖(ContinuousPseudometric.ofMetric (X k)).kernel - (ds k).kernel‖)
      atTop (𝓝 ‖(ContinuousPseudometric.ofMetric Y).kernel - d.kernel‖) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ ↦ abs_nonneg _)
    (fun k ↦ feature_uniform_error_comparison (R k) (ds k) d (f k) g (hf k) hg (r k) (hr k))
  simpa using (he.const_mul 2).add hd

/-- Arbitrary local representatives on a common finite superset realize the
actual global pseudometric pointwise, not just its GH class. -/
theorem modelPseudometric_eq_representative_feature
    {A : ℕ → PaperN.PartI.MeasuredCompact.{0}} {τ : ℕ → ℝ}
    (M : ∀ i, LocalModel (A i) (τ i)) (ρ : PartitionOfUnity ℕ GromovHausdorff.GHSpace)
    (hρ : ρ.IsSubordinate (fun i ↦ (M i).domain)) (X : PaperN.PartI.MeasuredCompact.{0})
    (J : Finset ℕ) (hJ : ρ.finsupport (GromovHausdorff.toGHSpace X) ⊆ J)
    (a : ∀ i, NormedCoordinatePair X (EuclideanSpace ℝ (Fin (M i).dimension)))
    (ha : ∀ i (hi : i ∈ ρ.finsupport (GromovHausdorff.toGHSpace X)),
      Quotient.mk _ (a i) = (M i).coordinateClass X (modelFeature_active_mem M ρ hρ X i hi))
    (x y : X) :
    dist (finiteBlockFeature J (fun i ↦ ρ i (GromovHausdorff.toGHSpace X))
        (fun i ↦ (a i).dualFeature x))
      (finiteBlockFeature J (fun i ↦ ρ i (GromovHausdorff.toGHSpace X))
        (fun i ↦ (a i).dualFeature y)) = modelPseudometric M ρ X x y := by
  let s := ρ.finsupport (GromovHausdorff.toGHSpace X)
  have hw : ∀ i ∈ J, i ∉ s → ρ i (GromovHausdorff.toGHSpace X) = 0 := by
    intro i _ hi
    simpa only [s, ρ.mem_finsupport, Function.mem_support, not_not] using hi
  rw [← finiteBlockFeature_eq_of_subset s J hJ _ _ hw,
      ← finiteBlockFeature_eq_of_subset s J hJ _ _ hw]
  rw [finiteBlockFeature_dist _ _ (fun i _ ↦ ρ.nonneg i _)]
  simp only [modelPseudometric, weightedPseudometric_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hX := modelFeature_active_mem M ρ hρ X i hi
  have heq := NormedCoordinatePair.pseudometric_eq_of_equivalent
    (Quotient.exact ((ha i hi).trans ((M i).chosenPair_class X hX).symm))
  rw [(a i).dualFeature_dist]
  exact congrArg (ρ i (GromovHausdorff.toGHSpace X) * ·)
    (congrArg (fun d : ContinuousPseudometric X ↦ d x y) heq)

end PaperN.PartII
