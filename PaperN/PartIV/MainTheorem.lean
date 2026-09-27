import PaperN.PartIV.DiscreteApproximationMain
import PaperN.PartII.MainTheorem
import PaperN.PartI.GHPSeparability
import PaperN.PartI.GHPCommonEmbeddingProof
import PaperN.PartI.GHPSeparationProof
import PaperN.PartI.MainTheorem
import PaperN.PartI.GHCommonEmbeddingProof
import PaperN.PartI.ProbabilityApproximationProof
import PaperN.PartII.ContractibleExtensorProof
import PaperN.PartII.HannerCategoryProof
import PaperN.PartIV.HilbertRecognition
import PaperN.PartI.InvariantSelection
import PaperN.PartII.RealKernelSpectral
import PaperN.PartII.CompactEigenvalueProof

namespace PaperN.PartIV
open PaperN.PartI PaperN.PartII GromovHausdorff

/-- The main theorem with the Part I selection constructed from its explicit
literature inputs, rather than assumed as an intermediate conclusion. -/
theorem ghSpace_homeomorphic_hilbert_from_selection_inputs
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc)
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) : Nonempty (GHSpace ≃ₜ RealHilbertSpace) :=
  ghSpace_homeomorphic_hilbert hm hp (invariantFiberLawSelection_spec hm hp hc hg ha hv)
    hg hk   hf   hH hO hD hA  hK hT

/-- Main theorem with both Part I selection and real-kernel spectral properties proved. -/
theorem ghSpace_homeomorphic_hilbert_of_eigenvalue_finiteness
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hc : GHPCommonEmbeddingInput.{0}) (hg : GHCommonEmbeddingInput.{0})
    (ha : ProbabilityApproximationInput.{0}) (hv : InvariantValovInput hm hp hc)

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) : Nonempty (GHSpace ≃ₜ RealHilbertSpace) :=
  ghSpace_homeomorphic_hilbert_from_selection_inputs hm hp hc hg ha hv
    distanceKernelSpectralInput_proved   hf   hH hO hD hA  hK hT

/-- Main theorem with compact-eigenvalue finiteness also proved internally. -/
theorem ghSpace_homeomorphic_hilbert_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved ghpCommonEmbeddingInput_proved)



    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput)

    (hT : TorunczykRecognitionInput) : Nonempty (GHSpace ≃ₜ RealHilbertSpace) :=
  (hT GHSpace (ghSpace_absoluteRetract_main hv hH hO hD)).mpr
    hilbertCubeDiscreteApproximation_main

end PaperN.PartIV
