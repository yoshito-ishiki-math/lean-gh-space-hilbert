import PaperN.PartIV.MainTheorem
open PaperN.PartI PaperN.PartII PaperN.PartIV GromovHausdorff TopologicalSpace
example : CompleteSpace GHSpace := inferInstance
example : SeparableSpace GHSpace := inferInstance
example : Nonempty GHSpace := inferInstance
example : HasHilbertCubeDiscreteApproximation GHSpace := hilbertCubeDiscreteApproximation_main
example (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
    ghpCommonEmbeddingInput_proved) (hH : EquivariantHyperspaceARInput)
    (hO : OrbitARInput) (hD : HannerDominationInput) :
    IsAbsoluteRetract.{0,0} GHSpace := ghSpace_absoluteRetract_main hv hH hO hD
#print TorunczykRecognitionInput
#print HasHilbertCubeDiscreteApproximation
#print IsDiscreteFamily
#print axioms hilbertCubeDiscreteApproximation_main
#print axioms ghSpace_homeomorphic_hilbert_main
