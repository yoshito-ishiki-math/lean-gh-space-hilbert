import PaperN.PartIV.HilbertCubeApproximation
import PaperN.PartII.GHAbsoluteRetract
import Mathlib.Analysis.Normed.Lp.lpSpace

namespace PaperN.PartIV
open PaperN.PartI PaperN.PartII GromovHausdorff

/-- The real square-summable sequence space, with its norm topology. -/
abbrev RealHilbertSpace := lp (fun _ : ℕ ↦ ℝ) 2

/-- General cited input: Toruńczyk 1981, p.248 (i), with the 1985 Section C correction.
The metrizable AR category is explicitly restricted to Type-0 ambient spaces. -/
def TorunczykRecognitionInput : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [Nonempty X], IsAbsoluteRetract.{0,0} X →
      (Nonempty (X ≃ₜ RealHilbertSpace) ↔ HasHilbertCubeDiscreteApproximation X)

/-- Recognition applied to the actual GH approximation construction and a proved AR premise. -/
theorem ghSpace_homeomorphic_hilbert_of_absoluteRetract
    (hT : TorunczykRecognitionInput) (hg : GHCommonEmbeddingInput.{0})
    (hAR : IsAbsoluteRetract.{0,0} GHSpace) : Nonempty (GHSpace ≃ₜ RealHilbertSpace) :=
  (hT GHSpace hAR).mpr (ghSpace_hilbertCubeDiscreteApproximation hg)

/-- The main homeomorphism theorem, retaining every cited input as an explicit hypothesis. -/
theorem ghSpace_homeomorphic_hilbert
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) : Nonempty (GHSpace ≃ₜ RealHilbertSpace) :=
  ghSpace_homeomorphic_hilbert_of_absoluteRetract hT hg
    (AmbientKernel.ghSpace_absoluteRetract hm hp hs hg hk   hf   hH hO hD hA  hK)

end PaperN.PartIV
