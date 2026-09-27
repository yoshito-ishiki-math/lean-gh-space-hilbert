import PaperN.PartI.MainTheorem
import PaperN.PartI.OpenProjection
import PaperN.PartI.Valov

open PaperN.PartI TopologicalSpace

-- The application hypotheses are proved, not hidden in the Valov literature input.
example : InvariantMeasuredPolishStatement ghpMetricInput_proved.{0} :=
  invariantMeasuredPolish_spec ghpMetricInput_proved ghpPolishInput_proved
    ghpCommonEmbeddingInput_proved

example : OpenInvariantProjectionStatement ghpMetricInput_proved.{0} :=
  openInvariantProjection_spec ghpMetricInput_proved ghCommonEmbeddingInput_proved
    probabilityApproximationInput_proved

#print axioms PaperN.PartI.invariantMeasuredPolish_spec
#print axioms PaperN.PartI.openInvariantProjection_spec
#print axioms PaperN.PartI.probability_innerRegular_polish
#print axioms PaperN.PartI.valovSelection_spec
#print axioms PaperN.PartI.fiberLawSelection_spec
#print axioms PaperN.PartI.invariantFiberLawSelection_main
