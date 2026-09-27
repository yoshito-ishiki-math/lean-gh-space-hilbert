import PaperN.PartII.AbsoluteExtensor
import PaperN.PartII.SeparableANRExtension
import PaperN.PartII.HannerDomination
import PaperN.Shared.Contraction

namespace PaperN.PartII
open TopologicalSpace PaperN.PartI GromovHausdorff

/-- General input: the ANR-to-ANE direction of Dugundji 1958, Theorem 12.1. -/
def ANRToANEInput : Prop :=
  ∀ (X : Type) [TopologicalSpace X], IsAbsoluteNeighborhoodRetract.{0,0} X →
    IsAbsoluteNeighborhoodExtensor.{0,0} X

/-- General input: Hanner 1952, Theorem 12.3, for metrizable ambient spaces. -/
def ContractibleANEToAEInput : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [Nonempty X] [ContractibleSpace X],
    IsAbsoluteNeighborhoodExtensor.{0,0} X → IsAbsoluteExtensor.{0,0} X

namespace AmbientKernel
/-- GH space has the absolute extension property under the registered general inputs. -/
theorem ghSpace_absoluteExtensor
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput) :
    IsAbsoluteExtensor.{0,0} GHSpace := by
  letI : ContractibleSpace GHSpace := PaperN.Shared.ghSpace_contractible
  exact hK GHSpace
    (ghSpace_absoluteNeighborhoodRetract hm hp hs hg hk   hf   hH hO hD hA).isAbsoluteNeighborhoodExtensor_of_separable

/-- Part III's AR conclusion for all metrizable Type-0 ambient spaces. -/
theorem ghSpace_absoluteRetract
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput) :
    IsAbsoluteRetract.{0,0} GHSpace :=
  (ghSpace_absoluteExtensor hm hp hs hg hk   hf   hH hO hD hA  hK).isAbsoluteRetract

end AmbientKernel
end PaperN.PartII
