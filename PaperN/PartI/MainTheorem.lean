import PaperN.PartI.CurrentStatements
import PaperN.PartI.GHCommonEmbeddingProof
import PaperN.PartI.ProbabilityApproximationProof
import PaperN.PartI.GHPSeparability
import PaperN.PartI.GHPCommonEmbeddingProof

namespace PaperN.PartI

/-- Part I selection with the GHP metric, Polish properties, common embeddings,
and probability approximation proved internally. Only the Valov input remains. -/
theorem invariantFiberLawSelection_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved) :
    InvariantFiberLawSelectionStatement ghpMetricInput_proved :=
  invariantFiberLawSelection_spec ghpMetricInput_proved ghpPolishInput_proved
    ghpCommonEmbeddingInput_proved ghCommonEmbeddingInput_proved
    probabilityApproximationInput_proved hv

/-- The live M1--M3 conclusion in every fixed carrier universe,
with only the specialized Valov theorem as an external input. -/
theorem currentInvariantAssignment_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved) :
    CurrentInvariantAssignmentStatement.{u} :=
  currentInvariantAssignment_spec ghpMetricInput_proved ghpPolishInput_proved
    ghpCommonEmbeddingInput_proved ghCommonEmbeddingInput_proved
    probabilityApproximationInput_proved hv
end PaperN.PartI
