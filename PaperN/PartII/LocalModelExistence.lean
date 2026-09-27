import PaperN.PartII.SpectralLocalModel
import PaperN.PartII.LpStrictConvexity

namespace PaperN.PartII.AmbientKernel
open MeasureTheory PaperN.PartI

/-- Local models for every small whole compact carrier, with Lp strict convexity
proved internally and only the registered general inputs remaining. -/
theorem exists_localModel
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) : Nonempty (LocalModel X τ) := by
  apply exists_localModel_of_strictConvex hm hp hs hg hk   hf   _ X τ hτ
  intro q hq _ Y
  apply lp_strictConvexSpace (selectedProbability hm hs Y : Measure Y) (ENNReal.ofReal q)
    _ ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
  linarith

end PaperN.PartII.AmbientKernel
