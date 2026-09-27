import PaperN.PartII.ClosedEmbeddingFactor
import PaperN.PartII.GHAbsoluteRetract
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace PaperN.PartII
open Set Topology TopologicalSpace
universe v

/-- Separable metrizable AR targets have the AR property in every ambient universe. -/
theorem IsAbsoluteRetract.allUniverses
    {X : Type*} [TopologicalSpace X] [SeparableSpace X] [Nonempty X]
    (h : IsAbsoluteRetract.{_,0} X) : IsAbsoluteRetract.{_,v} X := by
  letI : MetrizableSpace X := h.1
  letI := TopologicalSpace.metrizableSpaceMetric X
  letI := TopologicalSpace.metrizableSpaceMetric (ℕ → ℝ)
  obtain ⟨i, hi⟩ := Metric.PiNatEmbed.exists_embedding_to_hilbert_cube (X := X)
  let j : X → ℕ → ℝ := fun x n ↦ (i x n).val
  have hj : IsEmbedding j :=
    (IsEmbedding.piMap (fun _ : ℕ ↦ IsEmbedding.subtypeVal)).comp hi
  refine ⟨h.1, ?_⟩
  intro Y _ _ e he
  letI := TopologicalSpace.metrizableSpaceMetric Y
  obtain ⟨f, hf⟩ := (⟨j, hj.continuous⟩ : C(X, ℕ → ℝ)).exists_extension' he
  apply h.retraction_of_factor e he.continuous f f.continuous
    (by rw [hf]; exact hj) (fun y ↦ Metric.infDist y (range e))
    (Metric.continuous_infDist_pt _)
  intro y
  exact (he.isClosed_range.mem_iff_infDist_zero (range_nonempty e)).symm

namespace AmbientKernel
open PaperN.PartI GromovHausdorff

/-- The Part III AR conclusion for every metrizable ambient universe. -/
theorem ghSpace_absoluteRetract_allUniverses
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput) :
    IsAbsoluteRetract.{0,v} GHSpace :=
  (ghSpace_absoluteRetract hm hp hs hg hk   hf   hH hO hD hA  hK).allUniverses

/-- The corresponding full ambient-category ANR conclusion. -/
theorem ghSpace_absoluteNeighborhoodRetract_allUniverses
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput) :
    IsAbsoluteNeighborhoodRetract.{0,v} GHSpace :=
  (ghSpace_absoluteRetract hm hp hs hg hk   hf   hH hO hD hA  hK).allUniverses.isAbsoluteNeighborhoodRetract

end AmbientKernel
end PaperN.PartII
