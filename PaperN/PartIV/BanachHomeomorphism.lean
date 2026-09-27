import PaperN.PartIV.HilbertRecognition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace PaperN.PartIV
open PaperN.PartI PaperN.PartII GromovHausdorff TopologicalSpace

/-- Kadets 1967, p.53: the real ℓ² specialization of Banach-space topological equivalence.
This is an explicit cited proposition, not a constructed proof or an implicit axiom. -/
def KadetsHomeomorphismInput : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E], (¬ FiniteDimensional ℝ E) → Nonempty (RealHilbertSpace ≃ₜ E)

/-- Composing the main homeomorphism with Kadets gives every real separable infinite-dimensional
Banach target. No linear or metric preservation is asserted. -/
theorem ghSpace_homeomorphic_banach_of_homeomorph
    (h : Nonempty (GHSpace ≃ₜ RealHilbertSpace)) (hK : KadetsHomeomorphismInput)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E] (hInfinite : ¬ FiniteDimensional ℝ E) : Nonempty (GHSpace ≃ₜ E) := by
  obtain ⟨e⟩ := h
  obtain ⟨f⟩ := hK E hInfinite
  exact ⟨e.trans f⟩

/-- The manuscript's Banach-space consequence with all registered input hypotheses exposed. -/
theorem ghSpace_homeomorphic_banach
    (hm : GHPMetricInput.{0}) (hp : GHPPolishInput hm)
    (hs : InvariantFiberLawSelectionStatement hm) (hg : GHCommonEmbeddingInput.{0})
    (hk : DistanceKernelSpectralInput.{0})

    (hf : CompactEigenvalueFinitenessInput.{0})

    (hH : EquivariantHyperspaceARInput) (hO : OrbitARInput)
    (hD : HannerDominationInput) (hA : HannerANRCategoryInput)
     (hK : ContractibleANEToAEInput)
    (hT : TorunczykRecognitionInput) (hB : KadetsHomeomorphismInput)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [SeparableSpace E] (hinf : ¬ FiniteDimensional ℝ E) : Nonempty (GHSpace ≃ₜ E) :=
  ghSpace_homeomorphic_banach_of_homeomorph
    (ghSpace_homeomorphic_hilbert hm hp hs hg hk   hf   hH hO hD hA  hK hT)
    hB E hinf

end PaperN.PartIV
