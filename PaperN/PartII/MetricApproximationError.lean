import PaperN.Shared.PseudometricComparison
import PaperN.PartII.CoordinateEstimate
import PaperN.PartII.NormedCoordinateClass

namespace PaperN.PartII
open PaperN.Shared Filter
open scoped Topology

/-- The manuscript supremum error is the norm of the continuous kernel difference. -/
theorem uniform_metric_error_eq_norm
    {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (d : ContinuousPseudometric X) :
    (⨆ z : X × X, |d z.1 z.2 - dist z.1 z.2|) =
      ‖d.kernel - (ContinuousPseudometric.ofMetric X).kernel‖ := by
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl

/-- Approximation errors differ by at most the pseudometric correspondence error
plus the distortion of the original metrics. -/
theorem uniform_metric_error_comparison
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (R : Correspondence X Y) (d : ContinuousPseudometric X) (e : ContinuousPseudometric Y) :
    |(⨆ z : X × X, |d z.1 z.2 - dist z.1 z.2|) -
      (⨆ z : Y × Y, |e z.1 z.2 - dist z.1 z.2|)| ≤
      correspondenceError R d e + R.distortion := by
  rw [uniform_metric_error_eq_norm, uniform_metric_error_eq_norm]
  exact uniform_norm_comparison R d (ContinuousPseudometric.ofMetric X)
    e (ContinuousPseudometric.ofMetric Y)

/-- Along correspondences of vanishing distortion and pseudometric error, the
uniform approximation errors themselves converge, on varying carriers. -/
theorem uniform_metric_error_tendsto
    {X : Type*} (Xs : ℕ → Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (R : ∀ k, Correspondence (Xs k) X)
    (ds : ∀ k, ContinuousPseudometric (Xs k)) (d : ContinuousPseudometric X)
    (he : Tendsto (fun k ↦ correspondenceError (R k) (ds k) d) atTop (𝓝 0))
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ z : Xs k × Xs k, |ds k z.1 z.2 - dist z.1 z.2|) atTop
      (𝓝 (⨆ z : X × X, |d z.1 z.2 - dist z.1 z.2|)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ ↦ abs_nonneg _)
    (fun k ↦ uniform_metric_error_comparison (R k) (ds k) d)
    (by simpa using he.add hd)

/-- Coordinate convergence and an eventual coordinate bound give convergence of
uniform metric approximation errors, on varying compact carriers. -/
theorem coordinate_metric_error_tendsto
    {X : Type*} (Xs : ℕ → Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (n : ℕ) [NeZero n] (R : ∀ k, Correspondence (Xs k) X)
    (as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)))
    (a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)))
    (M : ℝ) (hM : ∀ᶠ k in atTop, coordinateBound (as k).coordinates ≤ M)
    (hn : Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0))
    (hc : Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0))
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ⨆ z : Xs k × Xs k,
      |(as k).pseudometric z.1 z.2 - dist z.1 z.2|) atTop
      (𝓝 (⨆ z : X × X, |a.pseudometric z.1 z.2 - dist z.1 z.2|)) := by
  apply uniform_metric_error_tendsto Xs R (fun k ↦ (as k).pseudometric) a.pseudometric _ hd
  have ht : Tendsto (fun k ↦ 2 * M * unitNormError (as k).norm a.norm +
      2 * unitNormBound a.norm * coordinateError (R k) (as k).coordinates a.coordinates)
      atTop (𝓝 0) := by
    simpa using (hn.const_mul (2 * M)).add (hc.const_mul (2 * unitNormBound a.norm))
  refine squeeze_zero' (Eventually.of_forall (fun k ↦ error_nonneg (R k) _ _)) ?_ ht
  filter_upwards [hM] with k hk
  have he := coordinate_pseudometric_estimate n (R k) (as k).norm a.norm
      (as k).coordinates a.coordinates
  refine he.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
      (Real.iSup_nonneg (fun _ ↦ abs_nonneg _))

end PaperN.PartII
