import PaperN.PartII.LocalMetricErrorConvergence

namespace PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
open MeasureTheory Filter PaperN.PartI GromovHausdorff
open scoped Topology
variable {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
  {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}

/-- The intrinsic uniform approximation error; strict convexity is explicit. -/
noncomputable def metricError (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (Y : MeasuredCompact.{0}) (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius)
    (p : ENNReal) [Fact (1 ≤ p)]
    (hc : StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))) : ℝ :=
  letI := hc
  ⨆ z : Y × Y, |(NormedCoordinateClass.pseudometric _ _
    (B.coordinateClass hf hη Y hY p)) z.1 z.2 - dist z.1 z.2|

/-- Any strict center error threshold holds throughout a smaller GH ball.
Strict convexity is assumed only for carriers in the original neighborhood. -/
theorem exists_metric_error_ball (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hp : GHPPolishInput hm) (hg : GHCommonEmbeddingInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hη : 0 < η) [NeZero n]
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hc : ∀ (Y : MeasuredCompact.{0}),
      dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y)))
    (hX₀ : dist (toGHSpace X₀) (toGHSpace X₀) < B.radius)
    (τ : ℝ) (herr : B.metricError hf hη X₀ hX₀ p (hc X₀ hX₀) < τ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ B.radius ∧
      ∀ (Y : MeasuredCompact.{0}) (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius),
        dist (toGHSpace Y) (toGHSpace X₀) < δ →
        B.metricError hf hη Y hY p (hc Y hY) < τ := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (min B.radius (1 / ((k : ℝ) + 1)))
    (lt_min B.radius_pos (by positivity)) (min_le_left _ _)
  choose Xs hXs hdist hfail using hbad
  have ht : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X₀)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg)
      (fun k ↦ (hdist k).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hH⟩ := hg Xs X₀ ht
  letI : StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs X₀ : Measure X₀)) := hc X₀ hX₀
  letI : ∀ k, StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs (Xs k) : Measure (Xs k))) :=
    fun k ↦ hc (Xs k) (hXs k)
  have he := B.metric_error_tendsto hp   hf   hη hXs hX₀ C hH p hpfin hp2
  have he' : Tendsto (fun k ↦ B.metricError hf hη (Xs k) (hXs k) p (hc (Xs k) (hXs k)))
      atTop (𝓝 (B.metricError hf hη X₀ hX₀ p (hc X₀ hX₀))) := he
  obtain ⟨k, hk⟩ := (he'.eventually (gt_mem_nhds herr)).exists
  exact (not_lt_of_ge (hfail k)) hk

end PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
