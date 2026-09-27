import PaperN.PartII.MainTheorem

open PaperN.PartI PaperN.PartII GromovHausdorff

-- Hanner's small-domination premise is constructed without assuming Hanner itself.
example
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved)
    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput) :
    HasSmallANRDomination GHSpace :=
  AmbientKernel.ghSpace_hasSmallANRDomination ghpMetricInput_proved ghpPolishInput_proved
    (invariantFiberLawSelection_main hv) ghCommonEmbeddingInput_proved
    distanceKernelSpectralInput_proved compactEigenvalueFinitenessInput_proved hH hO

#print PaperN.PartII.HasSmallANRDomination
#print PaperN.PartII.HannerDominationInput
#print axioms PaperN.PartII.AmbientKernel.ghSpace_hasSmallANRDomination
#print axioms PaperN.PartII.hannerANRCategoryInput_proved
#print axioms PaperN.PartII.ghSpace_absoluteRetract_main
