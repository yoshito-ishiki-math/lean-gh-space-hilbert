import PaperN.PartII.ZeroCoordinateModel
import PaperN.PartII.CommonCorrespondences

namespace PaperN.PartII
open PaperN.Shared Metric Set Filter
open scoped Topology

/-- Diameter changes by at most the distortion of any correspondence. -/
theorem diameter_sub_le_distortion
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace X] [CompactSpace Y] [Nonempty X] [Nonempty Y]
    (R : Correspondence X Y) :
    |diam (univ : Set X) - diam (univ : Set Y)| ≤ R.distortion := by
  have h := uniform_metric_error_comparison R
    (zeroCoordinatePair X).pseudometric (zeroCoordinatePair Y).pseudometric
  simpa [zeroCoordinatePair_metric_error, correspondenceError,
    zeroCoordinatePair_pseudometric] using h

/-- Vanishing correspondence distortion implies convergence of diameters. -/
theorem diameter_tendsto_of_distortion
    {X : Type*} (Xs : ℕ → Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    [∀ k, MetricSpace (Xs k)] [∀ k, CompactSpace (Xs k)] [∀ k, Nonempty (Xs k)]
    (R : ∀ k, Correspondence (Xs k) X)
    (hd : Tendsto (fun k ↦ (R k).distortion) atTop (𝓝 0)) :
    Tendsto (fun k ↦ diam (univ : Set (Xs k))) atTop (𝓝 (diam (univ : Set X))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ ↦ abs_nonneg _) (fun k ↦ diameter_sub_le_distortion (R k)) hd

/-- Diameter is continuous along a compact common realization. -/
theorem diameter_tendsto_of_commonRealization
    {Xs : ℕ → PartI.MeasuredCompact} {X : PartI.MeasuredCompact}
    (C : PartI.CommonRealization Xs X) (hH : C.HausdorffConverges) :
    Tendsto (fun k ↦ diam (univ : Set (Xs k))) atTop (𝓝 (diam (univ : Set X))) := by
  obtain ⟨R, _, hd⟩ := C.exists_correspondences_tendsto hH
  exact diameter_tendsto_of_distortion (fun k ↦ Xs k) R hd

end PaperN.PartII
