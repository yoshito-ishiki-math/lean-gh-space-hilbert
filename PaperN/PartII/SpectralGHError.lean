import PaperN.PartII.CoordinateEquivariance
import PaperN.PartII.LocalApproximationNeighborhood
import PaperN.PartI.GHSection

namespace PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
open MeasureTheory Filter PaperN.PartI GromovHausdorff Metric
open scoped Topology
variable {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
  {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}

/-- The actual spectral approximation error as a function on the GH ball. -/
noncomputable def ghError (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (p : ENNReal) [Fact (1 ≤ p)]
    (hc : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y)))
    (q : ball (toGHSpace X₀) B.radius) : ℝ :=
  B.metricError hf hη (ghRepresentative q.val)
    (by simpa only [ghRepresentative_class, mem_ball] using q.property) p
    (hc _ (by simpa only [ghRepresentative_class, mem_ball] using q.property))

/-- The GH error agrees with the error of every whole carrier representative. -/
theorem ghError_toGHSpace (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (p : ENNReal) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (hc : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y)))
    (X : MeasuredCompact.{0}) (hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius) :
    B.ghError hf hη p hc ⟨toGHSpace X, hX⟩ = B.metricError hf hη X hX p (hc X hX) := by
  let Y := ghRepresentative (toGHSpace X)
  have hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius := by
    simpa only [Y, ghRepresentative_class] using hX
  letI := hc X hX
  letI := hc Y hY
  obtain ⟨e⟩ := toGHSpace_eq_toGHSpace_iff_isometryEquiv.mp (ghRepresentative_class (toGHSpace X))
  exact coordinate_metric_error_eq_of_comap_eq e _ _
    (B.coordinateClass_comap hf hη Y X hY hX e p hp)

/-- Nonnegativity holds at every point of the GH domain. -/
theorem ghError_nonneg (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (p : ENNReal) [Fact (1 ≤ p)]
    (hc : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y)))
    (q : ball (toGHSpace X₀) B.radius) : 0 ≤ B.ghError hf hη p hc q :=
  Real.iSup_nonneg (fun _ ↦ abs_nonneg _)

/-- The spectral error is continuous on the actual GH neighborhood. -/
theorem continuous_ghError (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hp : GHPPolishInput hm) (hg : GHCommonEmbeddingInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hη : 0 < η) [NeZero n]
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hc : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))) :
    Continuous (B.ghError hf hη p hc) := by
  apply continuous_iff_seqContinuous.mpr
  intro qs q hq
  let Xs := fun k ↦ ghRepresentative (qs k).val
  let X := ghRepresentative q.val
  have hXs k : dist (toGHSpace (Xs k)) (toGHSpace X₀) < B.radius := by
    simpa only [Xs, ghRepresentative_class, mem_ball] using (qs k).property
  have hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius := by
    simpa only [X, ghRepresentative_class, mem_ball] using q.property
  have ht : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)) := by
    simpa only [Xs, X, ghRepresentative_class, Function.comp_def] using
      (continuous_subtype_val.tendsto q).comp hq
  obtain ⟨C, hH⟩ := hg Xs X ht
  letI := hc X hX
  letI : ∀ k, StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs (Xs k) : Measure (Xs k))) :=
    fun k ↦ hc (Xs k) (hXs k)
  exact B.metric_error_tendsto hp   hf   hη hXs hX C hH p hpfin hp2

end PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
