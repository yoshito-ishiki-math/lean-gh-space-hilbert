import PaperN.PartI.MainTheorem
import PaperN.PartII.LocalModelExistence
import PaperN.PartII.UniversalLocalConvergence
import PaperN.PartII.RealKernelSpectral
import PaperN.PartII.CompactEigenvalueProof
import PaperN.PartII.HannerCategoryProof
import PaperN.PartII.ContractibleExtensorProof
import PaperN.PartII.UniversalAbsoluteRetract

namespace PaperN.PartII
open PaperN.PartI GromovHausdorff
universe v

/-- Part II local models with only the remaining Valov citation input. -/
theorem localModel_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved)
    (X : MeasuredCompact.{0}) (τ : ℝ) (hτ : 0 < τ) : Nonempty (LocalModel X τ) :=
  AmbientKernel.exists_localModel ghpMetricInput_proved ghpPolishInput_proved
    (invariantFiberLawSelection_main hv) ghCommonEmbeddingInput_proved
    distanceKernelSpectralInput_proved compactEigenvalueFinitenessInput_proved X τ hτ

/-- Part II at an arbitrary concrete compact metric center, with the universal
coordinate-class and convergence APIs supplied by the returned local model. -/
theorem localModel_concrete_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved)
    (X : Type*) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ M : LocalModel (smallCarrier X) τ,
      toGHSpace X ∈ M.domain ∧ M.error (toGHSpace X) < τ := by
  obtain ⟨M⟩ := localModel_main hv (smallCarrier X) τ hτ
  refine ⟨M, ?_, ?_⟩
  · simpa only [smallCarrier, ghRepresentative_class] using M.center_mem
  · simpa only [smallCarrier, ghRepresentative_class] using M.center_error

/-- Part III absolute retract conclusion in every metrizable ambient universe,
with exactly its four literature inputs. -/
theorem ghSpace_absoluteRetract_main
    (hv : InvariantValovInput ghpMetricInput_proved ghpPolishInput_proved
      ghpCommonEmbeddingInput_proved)
    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) : IsAbsoluteRetract.{0,v} GHSpace :=
  (AmbientKernel.ghSpace_absoluteRetract ghpMetricInput_proved ghpPolishInput_proved
    (invariantFiberLawSelection_main hv) ghCommonEmbeddingInput_proved
    distanceKernelSpectralInput_proved compactEigenvalueFinitenessInput_proved
    hH hO hD hannerANRCategoryInput_proved contractibleANEToAEInput_proved).allUniverses
end PaperN.PartII
