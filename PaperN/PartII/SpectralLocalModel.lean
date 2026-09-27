import PaperN.PartII.LocalModel
import PaperN.PartII.SpectralGHError
import PaperN.PartII.SubspaceModelBounds
import PaperN.PartII.ApproximatingSpectralNeighborhood

namespace PaperN.PartII.AmbientKernel.SpectralModelNeighborhood
open MeasureTheory PaperN.PartI GromovHausdorff Metric Set

/-- Assemble the spectral construction into all local-model conditions.
The center error and neighborhood-local strict convexity remain explicit. -/
noncomputable def toLocalModel
    {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
    {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}
    (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hp : GHPPolishInput hm) (hg : GHCommonEmbeddingInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})
     (hη : 0 < η) (hn : 0 < n)
    (p : ENNReal) [Fact (1 ≤ p)] (hpfin : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hc : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < B.radius →
      StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y)))
    (hX₀ : dist (toGHSpace X₀) (toGHSpace X₀) < B.radius)
    (τ : ℝ) (herr : B.metricError hf hη X₀ hX₀ p (hc X₀ hX₀) < τ) :
    LocalModel X₀ τ := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let err : GHSpace → ℝ := fun q ↦
    if hq : q ∈ ball (toGHSpace X₀) B.radius then B.ghError hf hη p hc ⟨q, hq⟩ else 0
  have heq (X : MeasuredCompact.{0}) (hX : dist (toGHSpace X) (toGHSpace X₀) < B.radius) :
      err (toGHSpace X) = B.metricError hf hη X hX p (hc X hX) := by
    dsimp [err]
    rw [dif_pos (show toGHSpace X ∈ ball (toGHSpace X₀) B.radius from hX)]
    exact B.ghError_toGHSpace hf hη p hpfin hc X hX
  refine {
    domain := ball (toGHSpace X₀) B.radius
    domain_open := isOpen_ball
    center_mem := hX₀
    dimension := n
    dimension_pos := hn
    coordinateClass := fun X hX ↦ @coordinateClass _ _ _ _ _ B hf hη X hX p _ (hc X hX)
    error := err
    error_nonneg := ?_
    error_continuous := ?_
    center_error := ?_
    equivariance := ?_
    bound := ?_
    representatives_converge := ?_
    error_eq := ?_ }
  · intro q hq
    dsimp [err]
    rw [dif_pos hq]
    exact B.ghError_nonneg hf hη p hc ⟨q, hq⟩
  · rw [continuousOn_iff_continuous_restrict]
    have he : (ball (toGHSpace X₀) B.radius).domRestrict err = B.ghError hf hη p hc := by
      funext q
      simp only [Set.domRestrict, err, dif_pos q.property]
    rw [he]
    exact B.continuous_ghError hp hg   hf   hη p hpfin hp2 hc
  · rwa [heq X₀ hX₀]
  · intro X Y hX hY e a b ha hb
    letI := hc X hX
    letI := hc Y hY
    exact B.representative_equivariance hf hη X Y hX hY e p hpfin a b ha hb
  · intro X hX a ha x
    letI := hc X hX
    exact B.representative_bound hf hη X hX p a ha x
  · intro Xs X hXs hX C hH
    letI := hc X hX
    letI : ∀ k, StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs (Xs k) : Measure (Xs k))) :=
      fun k ↦ hc (Xs k) (hXs k)
    exact B.representatives_converge hp   hf   hη hXs hX C hH p hpfin hp2
  · intro X hX a ha
    letI := hc X hX
    rw [heq X hX]
    have he := congrArg (NormedCoordinateClass.pseudometric X (EuclideanSpace ℝ (Fin n))) ha
    simp only [NormedCoordinateClass.pseudometric_mk] at he
    simp only [metricError, ← he]

end PaperN.PartII.AmbientKernel.SpectralModelNeighborhood

namespace PaperN.PartII.AmbientKernel
open MeasureTheory PaperN.PartI GromovHausdorff

/-- Local-model existence with the still-unproved Lp strict-convexity property
listed explicitly, alongside the previously registered general inputs. -/
theorem exists_localModel_of_strictConvex
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hc : ∀ (q : ℝ), 2 ≤ q → ∀ [Fact (1 ≤ ENNReal.ofReal q)] (Y : MeasuredCompact.{0}),
      StrictConvexSpace ℝ (Lp ℝ (ENNReal.ofReal q) (selectedProbability hm hs Y : Measure Y)))
    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) : Nonempty (LocalModel X τ) := by
  classical
  rcases subsingleton_or_nontrivial X with hsub | hnon
  · letI := hsub
    exact exists_localModel_of_subsingleton hg X τ hτ
  · letI := hnon
    obtain ⟨q, η, hq, hη, n, hn, B, hX, herr⟩ :=
      exists_approximating_spectral_neighborhood hm hp hs hg hk   hf   X τ hτ
    have hp2 : (2 : ENNReal) ≤ ENNReal.ofReal q := by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hq)
    letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨le_trans (by norm_num) hp2⟩
    letI := hc q hq X
    obtain ⟨a, ha⟩ := Quotient.exists_rep (B.coordinateClass hf hη X hX (ENNReal.ofReal q))
    have he := congrArg (NormedCoordinateClass.pseudometric X (EuclideanSpace ℝ (Fin n))) ha
    simp only [NormedCoordinateClass.pseudometric_mk] at he
    have herr' : B.metricError hf hη X hX (ENNReal.ofReal q) (hc q hq X) < τ := by
      simpa only [SpectralModelNeighborhood.metricError, ← he] using (herr a ha).2
    exact ⟨B.toLocalModel hp hg   hf   hη hn (ENNReal.ofReal q)
      ENNReal.ofReal_ne_top hp2 (fun Y _ ↦ hc q hq Y) hX τ herr'⟩

end PaperN.PartII.AmbientKernel
