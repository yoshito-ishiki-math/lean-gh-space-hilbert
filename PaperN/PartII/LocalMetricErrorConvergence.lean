import PaperN.PartII.LocalSpectralContinuity
import PaperN.PartII.CommonCorrespondences
import PaperN.PartII.CoordinateBoundConvergence

namespace PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
open MeasureTheory Filter PaperN.PartI GromovHausdorff
open scoped Topology
variable {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
  {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}

/-- Uniform metric approximation error of the local spectral class is sequentially
continuous throughout the neighborhood in any compact common realization. -/
theorem metric_error_tendsto (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hp : GHPPolishInput hm)

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hη : 0 < η) [NeZero n]
    {Xs : ℕ → MeasuredCompact.{0}} {X : MeasuredCompact.{0}}
    (hXs : ∀ k, dist (toGHSpace (Xs k)) (toGHSpace X₀) < B.radius)
    (hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius)
    (C : CommonRealization Xs X) (hH : C.HausdorffConverges)
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X : Measure X))]
    [∀ k, StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs (Xs k) : Measure (Xs k)))] :
    Tendsto (fun k ↦ ⨆ z : Xs k × Xs k,
      |(NormedCoordinateClass.pseudometric _ _ (B.coordinateClass hf hη (Xs k) (hXs k) p))
        z.1 z.2 - dist z.1 z.2|) atTop
      (𝓝 (⨆ z : X × X,
        |(NormedCoordinateClass.pseudometric _ _ (B.coordinateClass hf hη X hX p))
          z.1 z.2 - dist z.1 z.2|)) := by
  obtain ⟨a, as, ha, has, hn, hc⟩ := B.representatives_converge hp   hf   hη
    hXs hX C hH p hpfin hp2
  obtain ⟨R, hdisp, hdist⟩ := C.exists_correspondences_tendsto hH
  have ht := coordinate_metric_error_tendsto_of_errors (fun k ↦ Xs k) n R as a
    hn (hc R hdisp) hdist
  have heq k := congrArg (NormedCoordinateClass.pseudometric (Xs k) (EuclideanSpace ℝ (Fin n))) (has k)
  have heq0 := congrArg (NormedCoordinateClass.pseudometric X (EuclideanSpace ℝ (Fin n))) ha
  simp only [NormedCoordinateClass.pseudometric_mk] at heq heq0
  simpa only [heq, heq0] using ht

end PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
