import PaperN.PartII.SpectralProjectionProperties
import PaperN.PartI.LiftInputs

namespace PaperN.PartII.AmbientKernel
open MeasureTheory Filter PaperN.PartI ComplexKernel GromovHausdorff
open scoped Topology

/-- The selected spectral rank and both cutoff gaps persist in a GH ball,
uniformly over all measured carriers representing points of that ball. -/
theorem exists_spectral_rank_gap_ball
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm)
    (hg : GHCommonEmbeddingInput.{0}) (X : MeasuredCompact.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})
     (η : ℝ) (hη : 0 < η)
    (hpos : (η : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    (hneg : ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
      (ComplexKernel.distanceOperator (selectedProbability hm hs X : Measure X)))
    : ∃ δ : ℝ, 0 < δ ∧ ∀ Y : MeasuredCompact.{0},
      dist (toGHSpace Y) (toGHSpace X) < δ →
      (η : ℂ) ∈ resolventSet ℂ
        (ComplexKernel.distanceOperator (selectedProbability hm hs Y : Measure Y)) ∧
      ((-η : ℝ) : ℂ) ∈ resolventSet ℂ
        (ComplexKernel.distanceOperator (selectedProbability hm hs Y : Measure Y)) ∧
      Module.finrank ℝ (spectralCutoff (selectedProbability hm hs Y : Measure Y) η) =
        Module.finrank ℝ (spectralCutoff (selectedProbability hm hs X : Measure X) η) := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (1 / ((k : ℝ) + 1)) (by positivity)
  choose Xs hdist hfail using hbad
  have ht : Tendsto (fun k ↦ toGHSpace (Xs k)) atTop (𝓝 (toGHSpace X)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ dist_nonneg) (fun k ↦ (hdist k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hH⟩ := hg Xs X ht
  have hevent := (spectralProjections_spec hm hp hs C   hf   hH η hη hpos hneg).2.1
  obtain ⟨k, hk⟩ := hevent.exists
  exact hfail k hk.1 hk.2.1 hk.2.2.1

end PaperN.PartII.AmbientKernel
