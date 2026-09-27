import PaperN.PartII.SelectedClassConvergence
import PaperN.PartII.SpectralNeighborhood

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel GromovHausdorff
open scoped Topology

/-- A GH ball carrying a fixed spectral rank and both cutoff gaps. -/
structure SpectralModelNeighborhood (hm : GHPMetricInput.{0})
    (hs : InvariantFiberLawSelectionStatement hm) (X₀ : MeasuredCompact.{0})
    (η : ℝ) (n : ℕ) where
  radius : ℝ
  radius_pos : 0 < radius
  rank : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < radius →
    n = Module.finrank ℝ (spectralCutoff (selectedProbability hm hs Y : Measure Y) η)
  gaps : ∀ Y : MeasuredCompact.{0}, dist (toGHSpace Y) (toGHSpace X₀) < radius →
    (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs Y : Measure Y)) ∧
    ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs Y : Measure Y))

theorem exists_spectralModelNeighborhood
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    (hg : GHCommonEmbeddingInput.{0}) (X₀ : MeasuredCompact.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})
     (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X₀ : Measure X₀)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X₀ : Measure X₀)))
    (n : ℕ) (hd : n = Module.finrank ℝ
      (spectralCutoff (selectedProbability hm hs X₀ : Measure X₀) η)) :
    Nonempty (SpectralModelNeighborhood hm hs X₀ η n) := by
  obtain ⟨δ, hδ, hball⟩ := exists_spectral_rank_gap_ball
    hm hp hs hg X₀   hf   η hη hpos hneg
  exact ⟨⟨δ, hδ, fun Y hY ↦ hd.trans (hball Y hY).2.2.symm,
    fun Y hY ↦ ⟨(hball Y hY).1, (hball Y hY).2.1⟩⟩⟩

namespace SpectralModelNeighborhood
variable {hm : GHPMetricInput.{0}} {hs : InvariantFiberLawSelectionStatement hm}
  {X₀ : MeasuredCompact.{0}} {η : ℝ} {n : ℕ}

/-- The local coordinate class on an arbitrary carrier in the ball. -/
noncomputable def coordinateClass (B : SpectralModelNeighborhood hm hs X₀ η n)
    (hf : CompactEigenvalueFinitenessInput.{0}) (hη : 0 < η)
    (Y : MeasuredCompact.{0}) (hY : dist (toGHSpace Y) (toGHSpace X₀) < B.radius)
    (p : ENNReal) [Fact (1 ≤ p)]
    [StrictConvexSpace ℝ (Lp ℝ p (selectedProbability hm hs Y : Measure Y))] :
    NormedCoordinateClass Y (EuclideanSpace ℝ (Fin n)) :=
  selectedSpectralCoordinateClass hm hs hf Y η hη p n (B.rank Y hY)

/-- Local continuity at any limit carrier in the same ball, with representatives
chosen before all correspondences; ranks and gaps follow from ball membership. -/
theorem representatives_converge (B : SpectralModelNeighborhood hm hs X₀ η n)
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
    ∃ a : NormedCoordinatePair X (EuclideanSpace ℝ (Fin n)),
      ∃ as : ∀ k, NormedCoordinatePair (Xs k) (EuclideanSpace ℝ (Fin n)),
        Quotient.mk _ a = B.coordinateClass hf hη X hX p ∧
        (∀ k, Quotient.mk _ (as k) = B.coordinateClass hf hη (Xs k) (hXs k) p) ∧
        Tendsto (fun k ↦ unitNormError (as k).norm a.norm) atTop (𝓝 0) ∧
        ∀ R : ∀ k, PaperN.Shared.Correspondence (Xs k) X,
          Tendsto (fun k ↦ ⨆ z : (R k).rel,
            dist (C.seqMap k z.val.1) (C.limitMap z.val.2)) atTop (𝓝 0) →
          Tendsto (fun k ↦ coordinateError (R k) (as k).coordinates a.coordinates) atTop (𝓝 0) := by
  exact selected_spectral_class_representatives_converge hm hp hs C   hf   hH
    η hη (B.gaps X hX).1 (B.gaps X hX).2 n (B.rank X hX)
    (fun k ↦ B.rank (Xs k) (hXs k)) p hpfin hp2

end SpectralModelNeighborhood
end PaperN.PartII.AmbientKernel
